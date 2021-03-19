#include <stdio.h>
#include <errno.h>
#include "common.h"
#include "polynomial.h"
#include "string_stream.h"

//////// Type Definitions ////////

typedef struct Result_ {
    int succeeded;
    void *value;
} Result;

typedef enum Symbol_ {
    T_L_PAREN = 0,  // (
    T_R_PAREN = 1,  // )
    T_NUM = 2,      // [0-9]+
    T_X = 3,        // x
    T_PLUS = 4,     // +
    T_POS = 5,      // +, after (
    T_MINUS = 6,    // -
    T_NEG = 7,      // -, after (
    T_TIMES = 8,    // *
    T_EXP = 9       // ^
} Symbol;

typedef struct Token_ {
    Symbol type;
    void *value;
} Token;

WRAP_UNWRAP(long)

WRAP_UNWRAP(Token)

SHALLOW_COPY(long)

SHALLOW_COPY(Token)

//////// Result ////////

Result result_succeeded(void *value) {
    Result result;
    result.succeeded = 1;
    result.value = value;
    return result;
}

Result result_failed(void) {
    Result result;
    result.succeeded = 0;
    result.value = NULL;
    return result;
}

//////// Token ////////

Token *new_token(Symbol type) {
    Token *tok = (Token *) malloc_throw(sizeof(Token));
    tok->type = type;
    return tok;
}

fn_copier token_value_copier = NULL;

void token_copier_impl(Token *dst, const Token *from) {
    assert(token_value_copier != NULL);
    dst->type = from->type;
    dst->value = malloc_throw(sizeof(void *));
    token_value_copier(dst->value, from->value);
}

fn_copier token_copier(fn_copier copy) {
    token_value_copier = copy;
    return (fn_copier) token_copier_impl;
}

void token_deleter(Token *token) {
    safe_free(&token->value);
}

//////// Helper Functions ////////

void debug_token(const Token *token) {
    static const char *alphabet = "() x+P-N*^";
    if (token->type == T_NUM) {
        printf("%ld", unwrap_long(token->value));
    } else {
        putchar(alphabet[token->type]);
    }
}

//////// Lexer ////////

StringStream *read_line(void) {
    StringStream *ss = new_ss();
    int ch;
    while ((ch = getchar()) != EOF && ch != '\n') {
        ss_feed_char(ss, (char) ch);
    }
    return ss;
}

int char_is_number(char ch) {
    return '0' <= ch && ch <= '9';
}

int char_in_string(char ch, const char string[]) {
    for (const char *i = string; *i != '\0'; ++i) {
        if (ch == *i) {
            return 1;
        }
    }
    return 0;
}

Result preprocess(StringStream *ss) {
    /**
     * 1) Eliminate spaces.
     * 2) Make operators complete.
     * 3) Surround the expression with `(` and ')'.
     */
    static const char *alphabet = "x0123456789+-*^()";
    StringStream *ss_n = new_ss();
    ss_feed_char(ss_n, '(');
    size_t remaining = ss->data->size;
    while (remaining--) {
        char ch = ss_getchar(ss);
        if (ch == ' ' || ch == '\t') {
            continue;
        }
        if (!char_in_string(ch, alphabet)) {
            return result_failed();
        }
        ss_feed_char(ss_n, ch);
        /**
         * Make the operator `*` complete.
         * E.g. `12x` -> `12*x`
         *      `xxx` -> `x*x*x`
         */
        if (ss_peek(ss) == 'x' && (char_is_number(ch) || ch == 'x')) {
            ss_feed_char(ss_n, '*');
        }
    }
    ss_feed_char(ss_n, ')');
    return result_succeeded(ss_n);
}

Result tokenize(StringStream *ss) {
    Vector *tokens = new_vector();
    while (!ss_eof(ss)) {
        char ch = ss_peek(ss);
        if (char_is_number(ch)) {
            size_t pos = ss_tell(ss), size = 0;
            while (char_is_number(ss_peek(ss))) {
                ss_seek(ss, 1);
                ++size;
            }
            ss_set_pos(ss, pos);
            char *num_str = malloc_throw(size + 1);
            for (size_t i = 0; i != size; ++i) {
                num_str[i] = ss_getchar(ss);
            }
            num_str[size] = '\0';
            Token *token = new_token(T_NUM);
            long value = strtol(num_str, NULL, 10);
            safe_free((void **) &num_str);
            if (errno == ERANGE) {
                delete_vector(&tokens);
                return result_failed();
            }
            token->value = wrap_long(value);
            vector_append_with_deleter(tokens, token, (fn_ptr) token_deleter);
        } else {
            Symbol type;
            char ch_prev;
            switch (ch) {
                case '(':
                    type = T_L_PAREN;
                    break;
                case ')':
                    type = T_R_PAREN;
                    break;
                case 'x':
                    type = T_X;
                    break;
                case '+':
                    ss_seek(ss, -1);
                    ch_prev = ss_peek(ss);
                    ss_seek(ss, 1);
                    if (ch_prev == '(') {
                        type = T_POS;
                    } else {
                        type = T_PLUS;
                    }
                    break;
                case '-':
                    ss_seek(ss, -1);
                    ch_prev = ss_peek(ss);
                    ss_seek(ss, 1);
                    if (ch_prev == '(') {
                        type = T_NEG;
                    } else {
                        type = T_MINUS;
                    }
                    break;
                case '*':
                    type = T_TIMES;
                    break;
                case '^':
                    type = T_EXP;
                    break;
                default:  // Matching no valid character.
                    delete_vector(&tokens);
                    return result_failed();
            }
            vector_append(tokens, new_token(type));
            ss_seek(ss, 1);
        }
    }
    return result_succeeded(tokens);
}

//////// Shunting-Yard Algorithm ////////

/**
 * Precedence (the greater, the higher):
 * (unary) +  5
 * (unary) -  5
 *         ^  4
 *         *  3
 *         +  2
 *         -  2
 *         (  1
 */

int compare_precedence(Symbol lhs, Symbol rhs) {
    /**
     * precedence(lhs) <  precedence(rhs), return -1
     * precedence(lhs) == precedence(rhs), return  0
     * precedence(lhs) >  precedence(rhs), return  1
     */
    static const int precedence[10] = {1, 0, 0, 0, 2, 5, 2, 5, 3, 4};
    if (precedence[lhs] < precedence[rhs]) {
        return -1;
    }
    if (precedence[lhs] > precedence[rhs]) {
        return 1;
    }
    return 0;
}

int is_left_associative(Symbol sym) {
    /**
     * Associativity:
     *         ^  Right
     *         *  Left
     *         +  Left
     *         -  Left
     */
    static const int left_associativity[10] = {0, 0, 0, 0, 1, 0, 1, 0, 1, 0};
    return left_associativity[sym];
}

Result shunting_yard(const Vector *infix) {
    Vector *operators = new_vector();
    Vector *output = new_vector();
    int successful = 1;
    for (size_t i = 0; i != infix->size; ++i) {
        const Token *token = infix->data[i];
        if (token->type == T_NUM) {
            vector_copy_append_with_deleter(
                    output, token, token_copier(long_copy), (fn_ptr) token_deleter);
        } else if (token->type == T_X) {
            vector_copy_append(output, token, Token_copy);
        } else if (token->type == T_L_PAREN) {
            vector_copy_append(operators, token, Token_copy);
        } else if (token->type == T_POS || token->type == T_PLUS ||
                   token->type == T_NEG || token->type == T_MINUS ||
                   token->type == T_TIMES || token->type == T_EXP) {
            if (!operators->size) {
                successful = 0;
                break;
            }
            const Token *top_token;
            while ((top_token = vector_back(operators)),
                    compare_precedence(top_token->type, token->type) == 1
                    || (compare_precedence(top_token->type, token->type) == 0
                        && is_left_associative(token->type))) {
                vector_copy_append(output, top_token, Token_copy);
                vector_pop_back(operators);
            }
            vector_copy_append(operators, token, Token_copy);
        } else if (token->type == T_R_PAREN) {
            if (!operators->size) {
                successful = 0;
                break;
            }
            const Token *top_token;
            while ((top_token = vector_back(operators)),
                    top_token->type != T_L_PAREN) {
                vector_copy_append(output, top_token, Token_copy);
                vector_pop_back(operators);
            }

            vector_pop_back(operators);
        }
    }
    if (!successful) {
        delete_vector(&operators);
        delete_vector(&output);
        return result_failed();
    }
    vector_copy_concat(output, operators, Token_copy);
    delete_vector(&operators);
    return result_succeeded(output);
}

//////// Postfix Expression Evaluator ////////

Result evaluate(const Vector *postfix) {
    Vector *stack = new_vector();
    int successful = 1;
    for (size_t i = 0; i != postfix->size; ++i) {
        const Token *token = postfix->data[i];
        if (token->type == T_X) {
            PNode **new_term = new_polynomial();
            add_a_term(new_term, 1, 1);
            vector_append_with_deleter(stack, new_term, (fn_ptr) delete_polynomial);
        } else if (token->type == T_NUM) {
            PNode **new_term = new_polynomial();
            add_a_term(new_term, unwrap_long(token->value), 0);
            vector_append_with_deleter(stack, new_term, (fn_ptr) delete_polynomial);
        } else if (token->type == T_NEG) {
            if (stack->size < 1) {
                successful = 0;
                break;
            }
            PNode **back = vector_back(stack);
            multiply_by_a_term(back, -1, 0);
        } else if (token->type == T_PLUS) {
            if (stack->size < 2) {
                successful = 0;
                break;
            }
            PNode **before_back = stack->data[stack->size - 2];
            PNode **back = vector_back(stack);
            add_a_polynomial(before_back, back);
            vector_pop_back(stack);
        } else if (token->type == T_MINUS) {
            if (stack->size < 2) {
                successful = 0;
                break;
            }
            PNode **before_back = stack->data[stack->size - 2];
            PNode **back = vector_back(stack);
            multiply_by_a_term(back, -1, 0);
            add_a_polynomial(before_back, back);
            vector_pop_back(stack);
        } else if (token->type == T_TIMES) {
            if (stack->size < 2) {
                successful = 0;
                break;
            }
            PNode **before_back = stack->data[stack->size - 2];
            PNode **back = vector_back(stack);
            multiply_by_a_polynomial(before_back, back);
            vector_pop_back(stack);
        } else if (token->type == T_EXP) {
            if (stack->size < 2) {
                successful = 0;
                break;
            }
            PNode **before_back = stack->data[stack->size - 2];
            PNode **back = vector_back(stack);
            if (!has_only_zero_ordered_terms(back)) {
                successful = 0;
                break;
            }
            long order = zero_ordered_coefficient(back);
            if (order < 0) {
                successful = 0;
                break;
            }
            // Fast exponentiation.
            PNode **result = new_polynomial();
            add_a_term(result, 1, 0);
            while (order) {
                if (order & 1) {
                    multiply_by_a_polynomial(result, before_back);
                }
                multiply_by_a_polynomial(before_back, before_back);
                order >>= 1;
            }
            delete_polynomial(before_back);
            *before_back = *result;
            vector_pop_back(stack);
        }
    }
    if (!successful || stack->size != 1) {
        delete_vector(&stack);
        return result_failed();
    }
    PNode **result = duplicate(vector_back(stack));
    delete_vector(&stack);
    return result_succeeded(result);
}

int main(void) {
    StringStream *ss_line = read_line();
    Result preprocessed = preprocess(ss_line);
    delete_ss(&ss_line);

    if (preprocessed.succeeded) {
        StringStream *ss = preprocessed.value;
        Result tokenized = tokenize(ss);
        delete_ss(&ss);

        if (tokenized.succeeded) {
            Vector *infix = tokenized.value;
            Result converted = shunting_yard(infix);
            delete_vector(&infix);

            if (converted.succeeded) {
                Vector *postfix = converted.value;
                Result evaluated = evaluate(postfix);
                delete_vector(&postfix);

                if (evaluated.succeeded) {
                    PNode **result = evaluated.value;
                    debug_polynomial(result);
                    delete_polynomial(result);

                } else {
                    printf("Unable to evaluate.\n");
                }

            } else {
                printf("Invalid expression.\n");
            }

        } else {
            printf("Invalid expression.\n");
        }

    } else {
        printf("The input string contains invalid characters.\n");
    }

    return 0;
}

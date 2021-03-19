#ifndef __POLYNOMIAL__
#define __POLYNOMIAL__

#include <stdio.h>
#include <stddef.h>
#include "common.h"

//////// Type Definitions ////////

typedef struct PNode_ {
    long coefficient;
    long exponent;
    struct PNode_ *next;
} PNode;

//////// Helper functions ////////

void debug_polynomial(PNode **head) {
    /* Print out a polynomial like 2x^3-x^4. */
    int first = 1;
    for (PNode *curr = *head; curr != NULL; curr = curr->next) {
        if (curr->coefficient == 0) {
            continue;
        }
        if (curr->coefficient > 0) {
            if (first) {
                first = 0;
            } else {
                putchar('+');
            }
        }
        if (curr->coefficient != 1 || curr->exponent == 0) {
            printf("%ld", curr->coefficient);
        }
        if (curr->exponent == 0) {
            continue;
        }
        putchar('x');
        if (curr->exponent < 1) {
            printf("^(%ld)", curr->exponent);
        } else if (curr->exponent > 1) {
            printf("^%ld", curr->exponent);
        }
    }
    putchar('\n');
}

//////// Implementation of Polynomial ////////

PNode **new_polynomial(void) {
    PNode **head = (PNode **) malloc_throw(sizeof(PNode *));
    *head = NULL;
    return head;
}

void delete_polynomial(PNode **head) {
    PNode *curr = *head;
    PNode *prev = NULL;
    while (curr != NULL) {
        prev = curr;
        curr = curr->next;
        safe_free((void **) &prev);
    }
}

PNode **duplicate(PNode **head) {
    PNode **new_head = new_polynomial();
    PNode **new_curr = new_head;
    for (PNode *curr = *head; curr != NULL; curr = curr->next) {
        PNode *new_node = (PNode *) malloc_throw(sizeof(PNode));
        new_node->coefficient = curr->coefficient;
        new_node->exponent = curr->exponent;
        *new_curr = new_node;
        new_curr = &(*new_curr)->next;
    }
    *new_curr = NULL;
    return new_head;
}

void add_a_term(PNode **head, long coefficient, long exponent) {
    PNode **curr = head;
    while (*curr != NULL && exponent >= (*curr)->exponent) {
        if (exponent == (*curr)->exponent) {
            (*curr)->coefficient += coefficient;
            return;
        }
        curr = &(*curr)->next;
    }
    PNode *new_p_node = (PNode *) malloc_throw(sizeof(PNode));
    new_p_node->coefficient = coefficient;
    new_p_node->exponent = exponent;
    new_p_node->next = *curr;
    *curr = new_p_node;
}

void add_a_polynomial(PNode **head_dst, PNode **head) {
    for (PNode *curr = *head; curr != NULL; curr = curr->next) {
        add_a_term(head_dst, curr->coefficient, curr->exponent);
    }
}

void multiply_by_a_term(PNode **head, long coefficient, long exponent) {
    for (PNode *curr = *head; curr != NULL; curr = curr->next) {
        curr->coefficient *= coefficient;
        curr->exponent += exponent;
    }
}

void multiply_by_a_polynomial(PNode **head_dst, PNode **head) {
    PNode **result = new_polynomial();
    for (PNode *curr = *head; curr != NULL; curr = curr->next) {
        PNode **temp = duplicate(head_dst);
        multiply_by_a_term(temp, curr->coefficient, curr->exponent);
        add_a_polynomial(result, temp);
        delete_polynomial(temp);
    }
    delete_polynomial(head_dst);
    *head_dst = *result;
}

int has_only_zero_ordered_terms(PNode **head) {
    for (PNode *curr = *head; curr != NULL; curr = curr->next) {
        if (curr->exponent) {
            return 0;
        }
    }
    return 1;
}

long zero_ordered_coefficient(PNode **head) {
    long result = 0;
    for (PNode *curr = *head; curr != NULL; curr = curr->next) {
        if (curr->exponent == 0) {
            result += curr->coefficient;
        }
    }
    return result;
}

#endif  // __POLYNOMIAL__

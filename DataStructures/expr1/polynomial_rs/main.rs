mod polynomial;
use std::cmp::Ordering;
use std::io;
use std::io::Write;
use polynomial::*;

#[derive(Clone, Eq)]
enum Symbol {
    LParen,
    RPAREN,
    NUMBER(String),
    VAR(u8),
    POSITIVE,
    NEGATIVE,
    PLUS,
    MINUS,
    TIMES,
    EXPONENT,
}

impl Symbol {
    fn to_numeric(&self) -> i32 {
        match self {
            Symbol::POSITIVE | Symbol::NEGATIVE => 5,
            Symbol::EXPONENT => 4,
            Symbol::TIMES => 3,
            Symbol::PLUS | Symbol::MINUS => 2,
            Symbol::LParen => 1,
            _ => 0
        }
    }

    fn is_left_associative(&self) -> bool {
        match self {
            Symbol::PLUS | Symbol::MINUS | Symbol::TIMES => true,
            _ => false
        }
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> Ordering {
        self.to_numeric().cmp(&other.to_numeric())
    }
}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.to_numeric() == other.to_numeric()
    }
}

fn preprocess(raw: &str) -> Result<Vec<u8>, &'static str> {
    let mut result = vec![b'('];
    fn is_valid(ch: &u8) -> bool {
        ch.is_ascii_alphanumeric() || is_in(ch, b"+-*^()")
    }
    fn is_in(ch: &u8, valid: &[u8]) -> bool {
        for valid_ch in valid.iter() {
            if ch == valid_ch {
                return true;
            }
        }
        false
    }
    fn filter_whitespace(raw: &[u8]) -> Vec<u8> {
        let mut result = Vec::new();
        for ch in raw {
            if !ch.is_ascii_whitespace() {
                result.push(ch.clone());
            }
        }
        result
    }
    let bytes = filter_whitespace(raw.as_bytes());
    let mut paren_count = 0;
    for (i, ch) in bytes.iter().enumerate() {
        if ch.is_ascii_whitespace() {
            continue;
        }
        if *ch == b'(' {
            paren_count += 1;
        } else if *ch == b')' {
            if paren_count == 0 {
                return Err("unmatched parentheses");
            }
            paren_count -= 1;
        }
        if !is_valid(ch) {
            return Err("invalid characters");
        }
        result.push(*ch);
        if i + 1 != bytes.len()
            && ((bytes[i + 1].is_ascii_alphabetic()
            && (ch.is_ascii_alphabetic() || ch.is_ascii_digit()))
            || (!is_in(ch, b"+-*^(") && bytes[i + 1] == b'(')
            || (*ch == b')' && !is_in(&bytes[i + 1], b"+-*^)"))) {
            result.push(b'*');
        }
    }
    if paren_count == 0 {
        result.push(b')');
        Ok(result)
    } else {
        Err("unmatched parentheses")
    }
}

fn tokenize(raw: &[u8]) -> Result<Vec<Symbol>, &'static str> {
    let mut result = Vec::new();
    let mut idx: usize = 0;
    while idx != raw.len() {
        let ch = raw[idx];
        if ch.is_ascii_digit() {
            let begin = idx;
            let mut end = idx;
            while raw[end].is_ascii_digit() {
                end += 1;
            }
            result.push(
                Symbol::NUMBER(String::from_utf8_lossy(&raw[begin..end])
                    .parse().unwrap()));
            idx = end;
        } else {
            let sym = match ch {
                b'(' => Symbol::LParen,
                b')' => Symbol::RPAREN,
                b'+' => {
                    if raw[idx - 1] == b'(' {
                        Symbol::POSITIVE
                    } else {
                        Symbol::PLUS
                    }
                }
                b'-' => {
                    if raw[idx - 1] == b'(' {
                        Symbol::NEGATIVE
                    } else {
                        Symbol::MINUS
                    }
                }
                b'*' => Symbol::TIMES,
                b'^' => Symbol::EXPONENT,
                var => Symbol::VAR(var)
            };
            result.push(sym);
            idx += 1;
        }
    }
    Ok(result)
}

fn shunting_yard(infix: &Vec<Symbol>) -> Result<Vec<Symbol>, &'static str> {
    let mut operators = Vec::<Symbol>::new();
    let mut output = Vec::<Symbol>::new();
    for sym in infix.iter() {
        let sym = (*sym).clone();
        match sym {
            Symbol::NUMBER(_) | Symbol::VAR(_) => output.push(sym),
            Symbol::LParen => operators.push(sym),
            Symbol::POSITIVE | Symbol::PLUS |
            Symbol::NEGATIVE | Symbol::MINUS |
            Symbol::TIMES | Symbol::EXPONENT => {
                while let Some(top) = operators.last() {
                    if (*top == sym && sym.is_left_associative())
                        || *top > sym {
                        output.push(operators.pop().unwrap());
                    } else {
                        break;
                    }
                }
                operators.push(sym);
            }
            Symbol::RPAREN => {
                while let Some(top) = operators.last() {
                    if let Symbol::LParen = top {
                        break;
                    } else {
                        output.push(operators.pop().unwrap());
                    }
                }
                if operators.is_empty() {
                    return Err("invalid expression");
                }
                operators.pop();
            }
        }
    }
    Ok(output)
}

fn evaluate(postfix: &Vec<Symbol>) -> Result<Polynomial, &'static str> {
    let mut stack = Vec::<Polynomial>::new();
    for sym in postfix.iter() {
        match sym {
            Symbol::NUMBER(num_str) => {
                if let Ok(num) = num_str.parse::<i128>() {
                    stack.push(Polynomial::new_constant(num));
                } else {
                    return Err("numbers too large to parse");
                }
            }
            Symbol::VAR(var) => {
                stack.push(Polynomial::new_var(*var));
            }
            Symbol::NEGATIVE => {
                if stack.is_empty() {
                    return Err("invalid expression");
                }
                let temp = stack.last().unwrap().clone();
                if let Some(result) = temp.multiply_a_term(
                    &PolynomialTerm::new_constant(-1)) {
                    *stack.last_mut().unwrap() = result;
                } else {
                    return Err("numbers too large to evaluate");
                }
            }
            Symbol::PLUS => {
                if stack.len() < 2 {
                    return Err("invalid expression");
                }
                let before_back = stack[stack.len() - 2].clone();
                let back = stack.pop().unwrap();
                if let Some(result) = before_back
                    .add_a_polynomial(&back) {
                    *stack.last_mut().unwrap() = result;
                } else {
                    return Err("numbers too large to evaluate");
                }
            }
            Symbol::MINUS => {
                if stack.len() < 2 {
                    return Err("invalid expression");
                }
                let before_back = stack[stack.len() - 2].clone();
                let mut back = stack.pop().unwrap();
                if let Some(result) = back.multiply_a_term(
                    &PolynomialTerm::new_constant(-1)) {
                    back = result;
                } else {
                    return Err("numbers too large to evaluate");
                }
                if let Some(result) = before_back
                    .add_a_polynomial(&back) {
                    *stack.last_mut().unwrap() = result;
                } else {
                    return Err("numbers too large to evaluate");
                }
            }
            Symbol::TIMES => {
                if stack.len() < 2 {
                    return Err("invalid expression");
                }
                let before_back = stack[stack.len() - 2].clone();
                let back = stack.pop().unwrap();
                if let Some(result) = before_back
                    .multiply_a_polynomial(&back) {
                    *stack.last_mut().unwrap() = result;
                } else {
                    return Err("numbers too large to evaluate");
                }
            }
            Symbol::EXPONENT => {
                if stack.len() < 2 {
                    return Err("invalid expression");
                }
                let mut before_back = stack[stack.len() - 2].clone();
                let back = stack.pop().unwrap();
                if !back.is_constant() {
                    return Err("not a polynomial");
                }
                let mut order;
                if let Some(constant) = back.constant() {
                    if constant < 0 {
                        return Err("not a polynomial");
                    }
                    order = constant;
                } else {
                    return Err("numbers too large to evaluate");
                }
                let mut result = Polynomial::new_constant(1);
                while order != 0 {
                    if order & 1 == 1 {
                        if let Some(res) = result
                            .multiply_a_polynomial(&before_back) {
                            result = res;
                        } else {
                            return Err("numbers too large to evaluate");
                        }
                    }
                    let before_back_clone = before_back.clone();
                    if let Some(res) = before_back
                        .multiply_a_polynomial(&before_back_clone) {
                        before_back = res;
                    } else {
                        return Err("numbers too large to evaluate");
                    }
                    order >>= 1;
                }
                *stack.last_mut().unwrap() = result;
            }
            _ => ()
        }
    }
    if stack.len() != 1 {
        Err("invalid expression")
    } else {
        Ok(stack.last().unwrap().clone())
    }
}

fn evaluate_and_print(raw: &str) -> Result<Polynomial, String> {
    let preprocessed;
    match preprocess(&raw) {
        Ok(result) => { preprocessed = result }
        Err(error) => {
            return Err(format!("Preprocessor: {}", error));
        }
    }
    let infix;
    match tokenize(&preprocessed) {
        Ok(result) => { infix = result }
        Err(error) => {
            return Err(format!("Lexer: {}", error));
        }
    }
    let postfix;
    match shunting_yard(&infix) {
        Ok(result) => { postfix = result }
        Err(error) => {
            return Err(format!("Parser: {}", error));
        }
    }
    match evaluate(&postfix) {
        Ok(result) => Ok(result),
        Err(error) => {
            Err(format!("Evaluator: {}", error))
        }
    }
}

fn main() {
    println!("Please enter an expression after each `expr >` prompt.");
    let mut input = String::new();
    loop {
        print!("expr > ");
        io::stdout().flush().unwrap();
        io::stdin()
            .read_line(&mut input)
            .expect("[Error] Failed to read line");
        match evaluate_and_print(&input) {
            Ok(result) => println!("{}", result),
            Err(error) => println!("[Error] {}", error)
        }
        input.clear();
    }
}

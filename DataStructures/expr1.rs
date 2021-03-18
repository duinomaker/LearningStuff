use std::io;
use std::io::Write;
use std::fmt;
use std::cmp::Ordering;
use crate::Polynomial::*;

#[derive(Clone)]
struct PolynomialTerm {
    coefficient: i128,
    exponent: i128,
}

impl PolynomialTerm {
    fn new_constant(coefficient: i128) -> PolynomialTerm {
        PolynomialTerm { coefficient, exponent: 0 }
    }

    fn new_x() -> PolynomialTerm {
        PolynomialTerm { coefficient: 1, exponent: 1 }
    }

    fn is_zero(&self) -> bool {
        self.coefficient == 0
    }
}

impl fmt::Display for PolynomialTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::new();
        if self.coefficient == 0 {
            return write!(f, "");
        }
        if self.coefficient != 1 || self.exponent == 0 {
            result.push_str(&*format!("{}", self.coefficient));
        }
        if self.exponent == 0 {
            return write!(f, "{}", result);
        }
        result.push('x');
        if self.exponent < 0 {
            result.push_str(&*format!("^({})", self.exponent));
        } else if self.exponent > 1 {
            result.push_str(&*format!("^{}", self.exponent));
        }
        write!(f, "{}", result)
    }
}

#[derive(Clone)]
enum Polynomial {
    Cons(PolynomialTerm, Box<Polynomial>),
    Nil,
}

impl Polynomial {
    fn new() -> Polynomial {
        Nil
    }

    fn new_constant(coefficient: i128) -> Polynomial {
        let mut result = Polynomial::new();
        result = result.add_a_term(&PolynomialTerm::new_constant(coefficient))
            .unwrap();
        result
    }

    fn new_x() -> Polynomial {
        let mut result = Polynomial::new();
        result = result.add_a_term(&PolynomialTerm::new_x())
            .unwrap();
        result
    }

    fn add_a_term(self, term: &PolynomialTerm) -> Option<Polynomial> {
        match self {
            Cons(mut head, tail) => {
                if term.exponent == head.exponent {
                    if let Some(num) = head.coefficient
                        .checked_add(term.coefficient) {
                        head.coefficient = num;
                        Some(Cons(head, tail))
                    } else {
                        None
                    }
                } else if term.exponent > head.exponent {
                    if let Some(result) = tail.add_a_term(term) {
                        Some(Cons(head, Box::new(result)))
                    } else {
                        None
                    }
                } else {
                    Some(Cons(term.clone(), Box::new(Cons(head, tail))))
                }
            }
            Nil => {
                Some(Cons(term.clone(), Box::new(Nil)))
            }
        }
    }

    fn add_a_polynomial(mut self, poly: &Polynomial) -> Option<Polynomial> {
        if let Cons(head, tail) = poly {
            if let Some(result) = self.add_a_term(head) {
                self = result;
            } else {
                return None;
            }
            if let Some(result) = self.add_a_polynomial(tail) {
                self = result;
            } else {
                return None;
            }
        }
        Some(self)
    }

    fn multiply_a_term(self, term: &PolynomialTerm) -> Option<Polynomial> {
        match self {
            Cons(mut head, mut tail) => {
                if let Some(num) = head.coefficient
                    .checked_mul(term.coefficient) {
                    head.coefficient = num;
                } else {
                    return None;
                }
                if let Some(num) = head.exponent
                    .checked_add(term.exponent) {
                    head.exponent = num;
                } else {
                    return None;
                }
                if let Some(result) = tail.multiply_a_term(term) {
                    *tail = result;
                } else {
                    return None;
                }
                Some(Cons(head, tail))
            }
            Nil => Some(Nil)
        }
    }

    fn multiply_a_polynomial(self, poly: &Polynomial) -> Option<Polynomial> {
        let mut result = Polynomial::new();
        let mut poly = poly;
        while let Cons(head, tail) = poly {
            let mut temp = self.clone();
            if let Some(res) = temp.multiply_a_term(&head) {
                temp = res;
            } else {
                return None;
            }
            if let Some(res) = result.add_a_polynomial(&temp) {
                result = res;
            } else {
                return None;
            }
            poly = tail;
        }
        Some(result)
    }

    fn is_first_negative(&self) -> bool {
        if let Cons(head, _tail) = self {
            head.coefficient < 0
        } else {
            false
        }
    }

    fn is_constant(&self) -> bool {
        if let Cons(head, tail) = self {
            if head.coefficient == 0 && head.exponent != 0 {
                false
            } else {
                tail.is_constant()
            }
        } else {
            true
        }
    }

    fn constant(&self) -> Option<i128> {
        if let Cons(head, tail) = self {
            if head.exponent == 0 {
                if let Some(num) = tail.constant() {
                    if let Some(result) = head.coefficient
                        .checked_add(num) {
                        Some(result)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                tail.constant()
            }
        } else {
            Some(0)
        }
    }
}

impl fmt::Display for Polynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cons(head, tail) => {
                if head.is_zero() {
                    write!(f, "{}", tail)
                } else if tail.is_first_negative() {
                    write!(f, "{}{}", head, tail)
                } else if let Nil = **tail {
                    write!(f, "{}", head)
                } else {
                    write!(f, "{}+{}", head, tail)
                }
            }
            Nil => write!(f, "")
        }
    }
}

#[derive(Debug, Clone, Eq)]
enum Symbol {
    LParen,
    RPAREN,
    NUMBER(String),
    X,
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
    let raw_bytes = raw.as_bytes();
    let mut result = vec![b'('];
    fn is_in(ch: &u8, valid: &[u8]) -> bool {
        for valid_ch in valid.iter() {
            if ch == valid_ch {
                return true;
            }
        }
        false
    }
    let mut paren_count = 0;
    for (i, ch) in raw_bytes.iter().enumerate() {
        if ch.is_ascii_whitespace() {
            continue;
        }
        if *ch == b'(' {
            paren_count += 1;
        }
        if *ch == b')' {
            if paren_count == 0 {
                return Err("unmatched parentheses");
            }
            paren_count -= 1;
        }
        if !is_in(ch, b"x0123456789+-*^()") {
            return Err("invalid characters");
        }
        result.push(*ch);
        if i + 1 != raw_bytes.len() && (
            (raw_bytes[i + 1] == b'x' && (*ch == b'x' || ch.is_ascii_digit()))
                || (raw_bytes[i + 1] == b'(' && !is_in(ch, b"+-*^"))
                || (*ch == b')' && !is_in(&raw_bytes[i + 1], b"+-*^"))) {
            result.push(b'*');
        }
    }
    result.push(b')');
    if paren_count == 0 {
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
                b'x' => Symbol::X,
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
                _ => {
                    return Err("invalid characters");
                }
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
            Symbol::NUMBER(_) | Symbol::X => output.push(sym),
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
                let result = num_str.parse::<i128>();
                if let Ok(num) = result {
                    stack.push(Polynomial::new_constant(num));
                } else {
                    return Err("numbers too large to parse");
                }
            }
            Symbol::X => {
                stack.push(Polynomial::new_x());
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

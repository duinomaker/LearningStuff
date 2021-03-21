use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use Polynomial::*;

#[derive(Clone, Eq)]
struct PolynomialTermExponent {
    mapping: HashMap<u8, i128>
}

impl PolynomialTermExponent {
    fn new() -> Self {
        Self {
            mapping: HashMap::new()
        }
    }

    fn new_var(var: u8) -> Self {
        let mut mapping = HashMap::new();
        mapping.insert(var, 1);
        Self {
            mapping
        }
    }

    fn is_zero(&self) -> bool {
        if self.mapping.is_empty() {
            return true;
        }
        for (_var, val) in self.mapping.borrow().into_iter() {
            if *val != 0 {
                return false;
            }
        }
        true
    }

    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        let mut mapping = self.mapping.clone();
        for (var, val) in rhs.mapping.borrow().into_iter() {
            if let Some(val_mapping) = mapping.get_mut(&var) {
                if let Some(result) = val_mapping.checked_add(*val) {
                    *val_mapping = result;
                } else {
                    return None;
                }
            } else {
                mapping.insert(*var, *val);
            }
        }
        Some(Self { mapping })
    }
}

impl Ord for PolynomialTermExponent {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut alphabet = Vec::new();
        for (var, _val) in self.mapping.borrow().into_iter() {
            alphabet.push(var);
        }
        for (var, _val) in other.mapping.borrow().into_iter() {
            if self.mapping.get(var) == None {
                alphabet.push(var);
            }
        }
        alphabet.sort_unstable();
        for var in alphabet.into_iter() {
            let left;
            let right;
            match self.mapping.get(var) {
                Some(val) => { left = val }
                None => { return Ordering::Less; }
            }
            match other.mapping.get(var) {
                Some(val) => { right = val }
                None => { return Ordering::Greater; }
            }
            if left < right {
                return Ordering::Less;
            }
            if left > right {
                return Ordering::Greater;
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for PolynomialTermExponent {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for PolynomialTermExponent {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl fmt::Display for PolynomialTermExponent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::new();
        let mut alphabet = Vec::new();
        for (var, _val) in self.mapping.borrow().into_iter() {
            alphabet.push(var);
        }
        alphabet.sort_unstable();
        for var in alphabet.into_iter() {
            let val = self.mapping.get(var).unwrap();
            if *val == 0 {
                continue;
            }
            if *val == 1 {
                result.push(*var as char);
            } else if *val > 0 {
                result.push_str(&format!("{}^{}", *var as char, val));
            } else if *val < 0 {
                result.push_str(&format!("{}^({})", *var as char, val));
            }
        }
        write!(f, "{}", result)
    }
}

#[derive(Clone)]
pub struct PolynomialTerm {
    coefficient: i128,
    exponent: PolynomialTermExponent,
}

impl PolynomialTerm {
    pub fn new_constant(coefficient: i128) -> Self {
        Self {
            coefficient,
            exponent: PolynomialTermExponent::new(),
        }
    }

    fn new_var(var: u8) -> Self {
        Self {
            coefficient: 1,
            exponent: PolynomialTermExponent::new_var(var),
        }
    }

    fn is_zero(&self) -> bool {
        self.coefficient == 0
    }
}

impl fmt::Display for PolynomialTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.coefficient == 0 {
            write!(f, "")
        } else if self.coefficient == 1 {
            write!(f, "{}", self.exponent)
        } else if self.exponent.is_zero() {
            write!(f, "{}", self.coefficient)
        } else {
            write!(f, "{}{}", self.coefficient, self.exponent)
        }
    }
}

#[derive(Clone)]
pub enum Polynomial {
    Cons(PolynomialTerm, Box<Polynomial>),
    Nil,
}

impl Polynomial {
    fn new() -> Polynomial {
        Nil
    }

    pub fn new_constant(coefficient: i128) -> Self {
        let mut result = Polynomial::new();
        result = result.add_a_term(&PolynomialTerm::new_constant(coefficient))
            .unwrap();
        result
    }

    pub fn new_var(var: u8) -> Self {
        let mut result = Polynomial::new();
        result = result.add_a_term(&PolynomialTerm::new_var(var))
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
            Nil => Some(Cons(term.clone(), Box::new(Nil)))
        }
    }

    pub fn add_a_polynomial(mut self, poly: &Polynomial) -> Option<Polynomial> {
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

    pub fn multiply_a_term(self, term: &PolynomialTerm) -> Option<Polynomial> {
        match self {
            Cons(mut head, mut tail) => {
                if let Some(num) = head.coefficient
                    .checked_mul(term.coefficient) {
                    head.coefficient = num;
                } else {
                    return None;
                }
                if let Some(num) = head.exponent
                    .checked_add(&term.exponent) {
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

    pub fn multiply_a_polynomial(self, poly: &Polynomial) -> Option<Polynomial> {
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

    pub fn is_constant(&self) -> bool {
        if let Cons(head, tail) = self {
            if head.coefficient != 0 && !head.exponent.is_zero() {
                false
            } else {
                tail.is_constant()
            }
        } else {
            true
        }
    }

    pub fn constant(&self) -> Option<i128> {
        if let Cons(head, tail) = self {
            if head.exponent.is_zero() {
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

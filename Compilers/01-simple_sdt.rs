use std::collections::HashMap;
use std::io;
use std::io::Write;
use std::str::Chars;

struct Translator<'a> {
    source: Chars<'a>,
    lookahead: Option<char>,
    stack: Vec<Box<SyntaxTree>>,
}

enum SyntaxTree {
    BinOP(Box<SyntaxTree>, char, Box<SyntaxTree>),
    Num(f64),
    ID(char),
    Empty,
}

struct Environment {
    symbol_table: HashMap<char, f64>,
}

impl<'a> Translator<'a> {
    fn new(s: &'a str) -> Self {
        let mut chars = s.chars();
        let char_ahead = chars.next();
        Self {
            source: chars,
            lookahead: char_ahead,
            stack: Vec::new(),
        }
    }

    fn translate(s: &str) -> Box<SyntaxTree> {
        if s.contains('=') {
            Translator::new(s).run_stmt()
        } else {
            Translator::new(s).run_expr()
        }
    }

    fn append_num(&mut self, num: f64) {
        self.stack.push(Box::new(SyntaxTree::Num(num)));
    }

    fn append_id(&mut self, ch: char) {
        self.stack.push(Box::new(SyntaxTree::ID(ch)));
    }

    fn append_empty(&mut self) {
        self.stack.push(Box::new(SyntaxTree::Empty))
    }

    fn concat(&mut self, op: char) {
        let ob = self.stack.pop();
        let oa = self.stack.pop();
        if let (Some(a), Some(b)) = (oa, ob) {
            self.stack.push(Box::new(SyntaxTree::BinOP(a, op, b)));
        } else {
            panic!("matching error");
        }
    }

    fn mat(&mut self, ch: char) {
        if let Some(char_ahead) = self.lookahead {
            if ch == char_ahead {
                loop {
                    self.lookahead = self.source.next();
                    if let Some(' ' | '\n') = self.lookahead {} else {
                        break;
                    }
                }
            } else {
                panic!("matching error");
            }
        } else {
            panic!("matching error");
        }
    }

    fn run_stmt(mut self) -> Box<SyntaxTree> {
        self.stmt();
        if let Some(_) = self.lookahead {
            panic!("matching error");
        }
        self.stack.pop()
            .expect("matching error")
    }

    fn run_expr(mut self) -> Box<SyntaxTree> {
        self.expr();
        if let Some(_) = self.lookahead {
            panic!("matching error");
        }
        self.stack.pop()
            .expect("matching error")
    }

    fn stmt(&mut self) {
        self.identifier();
        self.mat('=');
        if let Some(_) = self.lookahead {
            self.expr();
        } else {
            self.append_empty();
        }
        self.concat('=')
    }

    fn expr(&mut self) {
        self.term();
        self.rest_expr();
    }

    fn rest_expr(&mut self) {
        match self.lookahead {
            Some('+') => {
                self.mat('+');
                self.term();
                self.concat('+');
                self.rest_expr();
            }
            Some('-') => {
                self.mat('-');
                self.term();
                self.concat('-');
                self.rest_expr();
            }
            _ => {}
        };
    }

    fn term(&mut self) {
        self.factor();
        self.rest_term();
    }

    fn rest_term(&mut self) {
        match self.lookahead {
            Some('*') => {
                self.mat('*');
                self.factor();
                self.concat('*');
                self.rest_term();
            }
            Some('/') => {
                self.mat('/');
                self.factor();
                self.concat('/');
                self.rest_term();
            }
            _ => {}
        };
    }

    fn factor(&mut self) {
        match self.lookahead {
            Some('(') => {
                self.mat('(');
                self.expr();
                self.mat(')');
            }
            Some('0'..='9' | '.') => {
                self.number();
            }
            Some('a'..='z') => {
                self.identifier();
            }
            _ => { panic!("matching error"); }
        };
    }

    fn number(&mut self) {
        let mut val = 0.0;
        let mut after_decimal_point = false;
        let mut cnt = 0;
        while let Some('0'..='9' | '.') = self.lookahead {
            let num = self.lookahead.unwrap();
            self.mat(num);
            if num == '.' {
                after_decimal_point = true;
            } else {
                if after_decimal_point {
                    cnt += 1;
                }
                val = val * 10.0 + (num as u8 - '0' as u8) as f64;
            }
        }
        if after_decimal_point && cnt == 0 {
            panic!("matching error");
        }
        for _ in 0..cnt {
            val = val / 10.0;
        }
        self.append_num(val);
    }

    fn identifier(&mut self) {
        let ch = self.lookahead.unwrap();
        self.mat(ch);
        self.append_id(ch);
    }
}

impl Environment {
    fn new() -> Self {
        Self {
            symbol_table: HashMap::new(),
        }
    }

    fn feed(&mut self, s: &str) -> Option<f64> {
        let t = Translator::translate(s);
        if let SyntaxTree::BinOP(_, '=', _) = *t {
            self.modify(&*t);
            None
        } else {
            Some(self.eval(&*t))
        }
    }

    fn modify(&mut self, t: &SyntaxTree) {
        match t {
            SyntaxTree::BinOP(boxed_id, '=', expr) => {
                if let SyntaxTree::ID(id) = **boxed_id {
                    if let SyntaxTree::Empty = **expr {
                        self.symbol_table.remove(&id);
                    } else {
                        self.symbol_table.insert(id, self.eval(expr));
                    }
                } else {
                    panic!("internal error");
                }
            }
            _ => { panic!("internal error"); }
        }
    }

    fn eval(&self, t: &SyntaxTree) -> f64 {
        match t {
            SyntaxTree::BinOP(a, op, b) => match *op {
                '+' => self.eval(a) + self.eval(b),
                '-' => self.eval(a) - self.eval(b),
                '*' => self.eval(a) * self.eval(b),
                '/' => self.eval(a) / self.eval(b),
                _ => { panic!("internal error"); }
            },
            SyntaxTree::Num(n) => *n,
            SyntaxTree::ID(id) => *self.symbol_table.get(id)
                .expect("undeclared symbol"),
            _ => { panic!("internal error"); }
        }
    }
}

/* Typical usage:
 | expr > x=6
 | expr > y=x+1/2/(1/2)
 | expr > x
 | 6
 | expr > y
 | 7
 | expr > x*y
 | 42
 */

fn main() {
    let mut env = Environment::new();
    let mut input = String::new();
    loop {
        print!("expr > ");
        io::stdout().flush()
            .expect("io error");
        io::stdin().read_line(&mut input)
            .expect("io error");
        let result = env.feed(&input);
        if let Some(num) = result {
            println!("{}", num);
        }
        input.clear();
    }
}

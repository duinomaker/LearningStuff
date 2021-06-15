use std::collections::HashMap;

struct TextGrouper {
    text: Vec<u8>,
    curr: usize,
    group_size: usize,
}

impl TextGrouper {
    fn new(text: &[u8], group_size: usize, padding: u8) -> Self {
        let mut text = Vec::from(text);
        let size = text.len() - text.len() / group_size * group_size;
        for _ in 0..size {
            text.push(padding);
        }
        Self {
            text,
            curr: 0,
            group_size,
        }
    }
}

impl Iterator for TextGrouper {
    type Item = Box<[u8]>;

    fn next(&mut self) -> Option<Box<[u8]>> {
        self.curr += self.group_size;
        if self.curr <= self.text.len() {
            let slice = Box::<[u8]>::from(
                &self.text[self.curr - self.group_size..self.curr]);
            Some(slice)
        } else {
            None
        }
    }
}

fn ascii_to_index(ch: u8) -> usize { (ch - b'a') as usize }

fn index_to_ascii(ch: usize) -> u8 { ch as u8 + b'a' }

fn ext_euclid(a: usize, b: usize) -> (isize, isize, isize) {
    let mut qs = Vec::new();
    fn euclid(qs: &mut Vec<isize>, a: usize, b: usize) {
        if b == 0 {
            qs.push(a as isize);
        } else {
            let q = a / b;
            qs.push(q as isize);
            euclid(qs, b, a - b * q);
        }
    }
    euclid(&mut qs, a, b);
    let qs = qs;
    let (mut s0, mut s1) = (1, 0);
    let (mut t0, mut t1) = (0, 1);
    for q in (&qs[0..qs.len() - 1]).into_iter() {
        let s2 = s0 - s1 * q;
        let t2 = t0 - t1 * q;
        s0 = s1;
        s1 = s2;
        t0 = t1;
        t1 = t2;
    }
    (*qs.last().unwrap(), s0, t0)
}

fn multiplicative_inverse(n: usize, m: usize) -> usize {
    let temp = ext_euclid(n, m).1 % m as isize;
    if temp < 0 {
        (temp + m as isize) as usize
    } else {
        temp as usize
    }
}

fn div_mod(a: usize, b: usize, m: usize) -> usize {
    a * multiplicative_inverse(b, m) % m
}

fn print_bytes(text: &[u8]) {
    for ch in text.into_iter() {
        print!("{}", *ch as char);
    }
    println!();
}

fn analyze(cipher: &[u8]) {
    let mut count = HashMap::new();
    for ch in cipher.into_iter() {
        *count.entry(*ch).or_insert(0) += 1;
    }
    let count = count;
    let mut keys: Vec<u8> = (&count).into_iter()
        .map(|(k, _v)| *k).collect();
    keys.sort_by(|a, b| count[b].cmp(&count[a]));
    let keys = keys;
    for key in keys.into_iter() {
        print!("{}: ", key as char);
        for _ in 0..count[&key] {
            print!("*");
        }
        println!();
    }
}

mod permutation_cipher {
    use crate::TextGrouper;

    fn substitute(text: &[u8], key: &[usize]) -> Vec<u8> {
        let mut result = Vec::new();
        result.reserve_exact(text.len());
        for i in key.into_iter() {
            result.push(text[*i]);
        }
        result
    }

    fn inverse(key: &[usize]) -> Vec<usize> {
        let mut new_key = Vec::new();
        new_key.resize_with(key.len(), Default::default);
        for (i, v) in key.into_iter().enumerate() {
            new_key[*v] = i;
        }
        new_key
    }

    pub fn encrypt(plain: &[u8], key: &[usize]) -> Vec<u8> {
        let mut result = Vec::new();
        TextGrouper::new(plain, key.len(), b'x')
            .for_each(|g| result.extend(substitute(&*g, key)));
        result
    }

    pub fn decrypt(cipher: &[u8], key: &[usize]) -> Vec<u8> {
        let mut result = Vec::new();
        let key = inverse(key);
        TextGrouper::new(cipher, key.len(), b'x')
            .for_each(|g| result.extend(substitute(&*g, &key)));
        result
    }
}

mod hill_cipher {
    use crate::{
        TextGrouper,
        index_to_ascii,
        ascii_to_index,
        div_mod,
        multiplicative_inverse,
    };

    struct Matrix {
        data: Vec<Vec<usize>>
    }

    impl Matrix {
        fn new() -> Self {
            Self { data: Vec::new() }
        }

        fn new_identity(size: usize) -> Self {
            let mut data = Vec::new();
            data.resize_with(size, Vec::new);
            for (i, row) in (&mut data).into_iter().enumerate() {
                row.resize(size, 0);
                row[i] = 1;
            }
            Self { data }
        }

        fn inverse(&self) -> Self {
            let mut data = self.data.clone();
            let mut result = Self::new_identity(data.len());
            for i in 0..data.len() {
                for j in i..data.len() {
                    if data[j][i] != 0 {
                        if i != j {
                            data.swap(i, j);
                            result.data.swap(i, j);
                        }
                        break;
                    }
                }
                for j in i + 1..data.len() {
                    if data[j][i] != 0 {
                        let coef = div_mod(26 - data[j][i], data[i][i], 26);
                        for k in 0..data.len() {
                            data[j][k] =
                                (data[j][k] + data[i][k] * coef) % 26;
                            result.data[j][k] =
                                (result.data[j][k]
                                    + result.data[i][k] * coef) % 26;
                        }
                        let coef = multiplicative_inverse(data[i][i], 26);
                        for k in 0..data.len() {
                            data[j][k] = (data[j][k] * coef) % 26;
                            result.data[j][k] =
                                (result.data[j][k] * coef) % 26;
                        }
                    }
                }
            }
            for i in 0..data.len() {
                for j in 0..i {
                    if data[j][i] != 0 {
                        let coef = 26 - data[j][i];
                        for k in 0..data.len() {
                            result.data[j][k] =
                                (result.data[j][k]
                                    + result.data[i][k] * coef) % 26;
                        }
                    }
                }
            }
            result
        }

        fn from_slice(seq: &[&[usize]]) -> Self {
            let mut result = Self::new();
            for row in seq {
                result.data.push(row.to_vec());
            }
            result
        }

        fn height(&self) -> usize {
            self.data.len()
        }

        fn width(&self) -> usize {
            self.data[0].len()
        }

        fn from_text(text: &[u8]) -> Self {
            Self::from_slice(
                &[&text.into_iter()
                    .map(|ch| ascii_to_index(*ch))
                    .collect::<Vec<usize>>()])
        }

        fn into_text(self) -> Vec<usize> {
            self.data[0].clone()
        }

        fn mul(&self, rhs: &Self) -> Self {
            let mut result = Self::new();
            result.data.resize_with(self.height(), Vec::new);
            for index in 0..result.height() {
                result.data[index]
                    .resize_with(rhs.width(), Default::default);
            }
            for i in 0..self.height() {
                for j in 0..rhs.width() {
                    result.data[i][j] = (0..rhs.height())
                        .map(|k| self.data[i][k] * rhs.data[k][j])
                        .sum::<usize>() % 26;
                }
            }
            result
        }
    }

    fn apply_matrix(plain: &[u8], mat: &Matrix) -> Vec<u8> {
        let mut result = Vec::new();
        TextGrouper::new(plain, mat.height(), b'x')
            .for_each(|g| result.extend(
                Matrix::from_text(&*g).mul(mat).into_text()));
        result.into_iter().map(index_to_ascii).collect()
    }

    pub fn encrypt(plain: &[u8], key: &[&[usize]]) -> Vec<u8> {
        let mat = Matrix::from_slice(key);
        apply_matrix(plain, &mat)
    }

    pub fn decrypt(cipher: &[u8], key: &[&[usize]]) -> Vec<u8> {
        let mat = Matrix::from_slice(key).inverse();
        apply_matrix(cipher, &mat)
    }
}

mod affine_cipher {
    use crate::{multiplicative_inverse, ascii_to_index, index_to_ascii};

    pub fn encrypt(plain: &[u8], key: &[u8; 2]) -> Vec<u8> {
        let a = (key[0] - b'a') as usize;
        let b = (key[1] - b'a') as usize;
        plain.into_iter()
            .map(|ch| index_to_ascii((ascii_to_index(*ch) * a + b) % 26))
            .collect()
    }

    pub fn decrypt(plain: &[u8], key: &[u8; 2]) -> Vec<u8> {
        let a = multiplicative_inverse((key[0] - b'a') as usize, 26);
        let b = (26 - (key[1] - b'a')) as usize;
        plain.into_iter()
            .map(|ch| index_to_ascii(((ascii_to_index(*ch) + b) * a) % 26))
            .collect()
    }
}

fn get_plain() -> Vec<u8> {
    let plain_raw = b"the state key laboratory of networking and switching \
    technology belongs to beijing university of posts and telecommunication \
    the laboratory was opened in nineteen ninety two in nineteen ninety five \
    the laboratory passed acceptance inspection by government and an \
    elevation organized by ministry of science and technology in two thousand \
    and two since two thousand and four the laboratory has been renamed as \
    the state key laboratory of networking and switching technology by \
    ministry of science and technology";
    let mut plain = Vec::new();
    for ch in plain_raw {
        if *ch != b' ' {
            plain.push(*ch);
        }
    }
    plain
}

fn main() {
    let plain = get_plain();
    print_bytes(&plain);

    let key: &[&[usize]] = &[&[1, 0, 21], &[9, 1, 15], &[0, 0, 1]];

    let encrypted = hill_cipher::encrypt(&plain, key);
    print_bytes(&encrypted);

    analyze(&encrypted);

    let decrypted = hill_cipher::decrypt(&encrypted, key);
    print_bytes(&decrypted);
}

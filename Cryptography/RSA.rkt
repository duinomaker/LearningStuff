#lang sicp

(define (gcd a b)
  (let ((q (floor (/ a b))))
    (let ((r (- a (* q b))))
      (if (= r 0) b (gcd b r)))))

(define (ext-gcd a b)
  (define (impl s0 s1 t0 t1 a b)
    (let ((q (floor (/ a b))))
      (let ((r (- a (* q b))))
        (if (= r 0)
            (cons s1 t1)
            (impl s1 (- s0 (* q s1))
                  t1 (- t0 (* q t1))
                  b r)))))
  (impl 1 0 0 1 a b))

(define (inverse a m)
  (let ((inv (car (ext-gcd a m))))
    (if (< inv 0)
        (+ inv m)
        inv)))

(define (square x) (* x x))

(define (miller-rabin-expmod base ex n)
  (define (squaremod-with-check x)
    (define (check squaremod-x)
      (if (and (= squaremod-x 1)
               (not (= x 1))
               (not (= x (- n 1))))
          0
          squaremod-x))
    (check (remainder (* x x) n)))
  (cond ((= ex 0) 1)
        ((even? ex)
         (squaremod-with-check (miller-rabin-expmod base (/ ex 2) n)))
        (else
         (remainder (* base (miller-rabin-expmod base (- ex 1) n)) n))))

(define (miller-rabin-test n rounds)
  (define (test-it a)
    (define (test-impl expmod-a)
      (= expmod-a 1))
    (test-impl (miller-rabin-expmod a (- n 1) n)))
  (cond ((= rounds 0) #t)
        ((test-it (+ 1 (random (- n 1))))
         (miller-rabin-test n (- rounds 1)))
        (else #f)))

(define (random-until min range pred)
  (define (iter)
    (let ((n (+ min (random range))))
      (if (pred n) n (iter))))
  (iter))

(define (generate-prime min range safety)
  (define (is-prime? prime)
    (miller-rabin-test prime 1000))
  (random-until min range is-prime?))

(define (new-public-key n e)
  (cons '*public* (cons n e)))

(define (new-private-key n d)
  (cons '*private* (cons n d)))

(define (get-key-n key)
  (cadr key))

(define (get-key-x key)
  (cddr key))

(define (generate-key)
  (let ((p (generate-prime 10000 50000 1000))
        (q (generate-prime 10000 50000 1000)))
    (let ((n (* p q))
          (phi-n (* (- p 1) (- q 1))))
      (let ((e (random-until 2 (- phi-n 2)
                               (lambda (num)
                                 (= (gcd num phi-n) 1)))))
        (let ((d (inverse e phi-n)))
          (cons (new-public-key n e)
                (new-private-key n d)))))))

(define (mod n m)
  (let ((q (floor (/ n m))))
    (- n (* q m))))

(define (exp-mod a b m)
  (cond ((= b 0) 1)
        ((odd? b) (mod (* a (exp-mod a (- b 1) m)) m))
        (else (mod (square (exp-mod a (/ b 2) m)) m))))

(define (crypt m key)
  (exp-mod m
           (get-key-x key)
           (get-key-n key)))

(define keys (generate-key))
(define public-key (car keys))
(define private-key (cdr keys))

(define m1 10124)
(define c (crypt m1 public-key))
(define m2 (crypt c private-key))

m1
c
m2

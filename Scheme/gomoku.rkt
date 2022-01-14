#lang scheme

; -------- Auxiliary List Operations -----------------------------------

(define (map-at-level f tree level)
  (cond ((zero? level) (f tree))
        ((null? tree) '())
        ((pair? tree)
         (cons (map-at-level f (car tree) (sub1 level))
               (map-at-level f (cdr tree) level)))
        (else (error "MAP-AT-LEVEL - cannot dive into the specified level"))))

(define (list-of-repetition elem times)
  (define (iter times)
    (if (zero? times)
        '()
        (cons elem (iter (sub1 times)))))
  (iter times))

(define (matrix-of-repetition elem times)
  (list-of-repetition
   (list-of-repetition elem times)
   times))

(define (change-list-at seq index f)
  (if (zero? index)
      (cons (f (car seq)) (cdr seq))
      (cons (car seq) (change-list-at (cdr seq) (sub1 index) f))))

(define (list-prod seq1 seq2)
  (define (iter1 seq1)
    (define (iter2 seq2)
      (if (null? seq2)
          '()
          (cons (cons (car seq1) (car seq2)) (iter2 (cdr seq2)))))
    (if (null? seq1)
        '()
        (append (iter2 seq2) (iter1 (cdr seq1)))))
  (iter1 seq1))

(define (list-of-take seq len)
    (if (< (length seq) len)
        '()
        (cons (take seq len) (list-of-take (cdr seq) len))))

(define (replace seq old new)
  (cond ((null? seq) '())
        ((equal? (car seq) old)
         (cons new (replace (cdr seq) old new)))
        (else
         (cons (car seq) (replace (cdr seq) old new)))))

(define (foldl-with-head-as-init f seq)
  (cond ((null? seq) (error "FOLDL-WITH-HEAD-AS-INIT - empty list"))
        ((null? (cdr seq)) (cadr seq))
        (else (foldl f (car seq) (cdr seq)))))

(define (list-max-by-key key seq)
  (foldl-with-head-as-init (lambda (a b)
                             (if (> (key a) (key b))
                                 a b))
                           seq))

(define (count obj seq)
  (cond ((null? seq) 0)
        ((equal? (car seq) obj)
         (add1 (count obj (cdr seq))))
        (else
         (count obj (cdr seq)))))

; -------- Player, Position, Board, and the Static Evaluator -----------

(define board-size 15)

(define (opposite-color color)
  (cond ((eq? color 'B) 'W)
        ((eq? color 'W) 'B)
        (else (error "OPPOSITE-COLOR - invalid color"))))

(define (make-player computer? color)
  (define opponent-color (opposite-color color))
  (define (dispatch m)
    (cond ((eq? m 'computer?) computer?)
          ((eq? m 'color) color)
          ((eq? m 'opponent-color) opponent-color)
          ((eq? m 'opponent)
           (make-player (not computer?) opponent-color))
          (else (error "PLAYER - invalid command"))))
  dispatch)

(define (make-position x y)
  (define (nudge dx dy)
    (make-position (+ x dx) (+ y dy)))
  (define (dispatch m)
    (cond ((eq? m 'x) x)
          ((eq? m 'y) y)
          ((eq? m 'nudge) nudge)
          (else (error "POSITION - invalid command"))))
  dispatch)

(define (position-from-pair x-and-y)
  (make-position (car x-and-y) (cdr x-and-y)))

(define (positions-around position)
  (define range '(-2 -1 0 1 2))
  (define (valid? position)
    (and (<= 0 (position 'x)) (< (position 'x) board-size)
         (<= 0 (position 'y)) (< (position 'y) board-size)))
  (let ((list-of-delta (list-prod range range)))
    (define (not-both-zero delta)
      (not (and (zero? (car delta)) (zero? (cdr delta)))))
    (define (position-add-delta delta)
      ((position 'nudge) (car delta) (cdr delta)))
    (filter valid?
            (map position-add-delta
                 (filter not-both-zero
                         list-of-delta)))))

(define (new-board)
  (matrix-of-repetition '- board-size))

(define (board-ref board x y)
  (list-ref (list-ref board x) y))

(define (board-at-position board position)
  (board-ref board (position 'x) (position 'y)))

(define (display-board board)
  (define (display-row row)
    (cond ((null? row) (newline))
          (else (display (car row))
                (display " ")
                (display-row (cdr row)))))
  (cond ((not (null? board))
         (display-row (car board))
         (display-board (cdr board)))))

(define (make-move board color position)
  (define (change-row seq)
    (define (change-col elem)
      (cond ((eq? elem '-) color)
            (else (error "MAKE-MOVE - position already taken"))))
    (change-list-at seq (position 'y) change-col))
  (change-list-at board (position 'x) change-row))

(define (probable-positions-to-move board)
  (define (has-piece-at? position)
    (let ((piece (board-at-position board position)))
      (or (eq? piece 'B) (eq? piece 'W))))
  (define (have-pieces-around? position)
    (let ((around (positions-around position)))
      (foldl (lambda (a b) (or a b)) #f (map has-piece-at? around))))
  (let ((all-positions
         (map position-from-pair
              (list-prod (range board-size) (range board-size)))))
    (filter have-pieces-around?
            (filter (lambda (position) (not (has-piece-at? position)))
                    all-positions))))

(define (shredder-board board min-length)
  (let ((trapezoid-shaped-quarter
         (map (lambda (ys-and-x+y)
                (map (lambda (y) (cons y (- (cdr ys-and-x+y) y)))
                     (car ys-and-x+y)))
              (map (lambda (n) (cons (range n) (sub1 n)))
                   (range min-length board-size))))
        (diagonal-line
         (list (map (lambda (n) (cons n n)) (range board-size))))
        (horizontal-lines
         (map (lambda (n) (map (lambda (m) (cons n m)) (range board-size)))
              (range board-size))))
    (define (transpose slices)
      (map-at-level (lambda (x-and-y)
                      (cons (- (sub1 board-size) (cdr x-and-y))
                            (- (sub1 board-size) (car x-and-y)))) slices 2))
    (define (flip slices)
      (map-at-level (lambda (x-and-y)
                      (cons (car x-and-y)
                            (- (sub1 board-size) (cdr x-and-y)))) slices 2))
    (let ((all-slices
           (append trapezoid-shaped-quarter
                   (transpose trapezoid-shaped-quarter)
                   (flip trapezoid-shaped-quarter)
                   (flip (transpose trapezoid-shaped-quarter))
                   diagonal-line
                   (flip diagonal-line)
                   horizontal-lines
                   (transpose horizontal-lines))))
      (map-at-level (lambda (x-and-y)
                      (board-ref board (car x-and-y) (cdr x-and-y)))
                    all-slices 2))))

(define (evaluate-board-with-heuristics board player)
  (define computer-color
    (if (player 'computer?) (player 'color) (player 'opponent-color)))
  (define human-color
    (opposite-color computer-color))
  (define symmetric-patterns
    '(((- O O O O -) 300000)
      ((X O O - O O X) 2600)
      ((X O - O - O X) 550)
      ((- O - - O -) 200)))
  (define asymmetric-patterns
    '(((X O O O O -) 2500)
      ((X O O O - O X) 3000)
      ((- - O O O X) 500)
      ((- O - O O -) 800)
      ((X O - - O O X) 600)
      ((X O O - - -) 150)))
  (define once-patterns
    '((((- - O - O -) (- O - O - -)) 250)
      (((- - O O O -) (- O O O - -)) 3000)
      (((- - - O O -) (- - O O - -) (- O O - - -)) 650)))
  (define common-patterns
    (append symmetric-patterns
            asymmetric-patterns
            (map (lambda (x) (cons (reverse (car x)) (cdr x)))
                 asymmetric-patterns)))
  (define (calc-slice-score slice O-color)
    (define X-color (opposite-color O-color))
    (define (preprocess slice pattern-length)
      (let ((slice (replace (replace slice X-color 'X) O-color 'O)))
        (let ((delineated-slice (append '(X) slice '(X))))
          (list-of-take delineated-slice pattern-length))))
    (define (count-matches slices pat)
      (cond ((null? slices) 0)
            ((equal? (car slices) pat)
             (add1 (count-matches (cdr slices) pat)))
            (else (count-matches (cdr slices) pat))))
    (define (count-once-matches slices pats)
      (define (matches-at-least-one-pat slice)
        (foldl (lambda (a b) (or a b)) #f
               (map (lambda (pat) (equal? slice pat)) pats)))
      (count #t (map matches-at-least-one-pat slices)))
    (define (common-patterns-score slice patterns)
      (define (iter patterns score)
        (if (null? patterns)
            score
            (let ((slices (preprocess slice (length (caar patterns)))))
              (iter (cdr patterns)
                    (+ score (* (count-matches slices (caar patterns))
                                (cadar patterns)))))))
      (iter patterns 0))
    (define (once-patterns-score slice patterns)
      (define (iter patterns score)
        (if (null? patterns)
            score
            (let ((slices (preprocess slice (length (caaar patterns)))))
              (iter (cdr patterns)
                    (+ score (* (count-once-matches slices (caar patterns))
                                (cadar patterns)))))))
      (iter patterns 0))
    (+ (common-patterns-score slice common-patterns)
       (once-patterns-score slice once-patterns)))
  (let ((slices (shredder-board board 5)))
    (define (total-score slice)
      (- (calc-slice-score slice computer-color)
         (calc-slice-score slice human-color)))
    (foldl + 0 (map total-score slices))))

; -------- The Min-Max Algorithm with Alpha-Beta Pruning ---------------

(define (min-max board player depth alpha beta)
  (define maximizing? (player 'computer?))
  (define (evaluate-board-with-recursion)
    (let ((boards
           (map (lambda (position)
                  (make-move board (player 'color) position))
                (probable-positions-to-move board))))
      (define (iter boards alpha beta value)
        (define (prune? value)
          (if maximizing? (>= value beta) (<= value alpha)))
        (if (null? boards)
            value
            (let ((new-value
                   ((if maximizing? max min)
                    value
                    (min-max (car boards) (player 'opponent) (sub1 depth)
                             alpha beta))))
              (if (prune? new-value)
                  new-value
                  (if maximizing?
                      (iter (cdr boards) (max alpha new-value) beta new-value)
                      (iter (cdr boards) alpha (min beta new-value) new-value))))))
      (iter boards alpha beta (if maximizing? -inf.0 +inf.0))))
  (if (zero? depth)
      (evaluate-board-with-heuristics board player)
      (evaluate-board-with-recursion)))

(define (best-move-for-player board player depth)
  (let ((moves (probable-positions-to-move board)))
    (define (to-move-and-score move)
      (cons move
            (min-max (make-move board (player 'color) move)
                     player depth -inf.0 +inf.0)))
    (car (list-max-by-key cdr (map to-move-and-score moves)))))

; -------- The Main Program --------------------------------------------

(define board
  '((- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - B - - - - - - - -)
    (- - - - - B - B - - - - - - -)
    (- - - - - W W - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)
    (- - - - - - - - - - - - - - -)))
(define player (make-player #t 'W))
(define best-move (best-move-for-player board player 1))
(display-board (make-move board (player 'color) best-move))
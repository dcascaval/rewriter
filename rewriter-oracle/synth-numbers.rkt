#lang rosette

(require rosette/lib/destruct)

(output-smt #t) ; Debugging: output SMT formula to file.

(struct add (a b) #:transparent)
(struct sub (a b) #:transparent)
(struct mul (a b) #:transparent)
(struct div (a b) #:transparent)
(struct idx (i) #:transparent)

(define ARITY 3) ; Inputs of length 3
(define DEPTH 3) ; ASTs of depth 3

(define (interpret input expr)
  (destruct expr
            [ (add a b) (+ (interpret input a) (interpret input b)) ] ; 0
            [ (sub a b) (- (interpret input a) (interpret input b)) ] ; 1
            [ (mul a b) (/ (interpret input a) (interpret input b)) ] ; 2
            [ (div a b) (* (interpret input a) (interpret input b)) ] ; 3
            [ (idx i) (list-ref input i) ]))                          ; 4 -> (4+arity-1)

(define (interpret-exprs exprs input)
  (map (curry interpret input) exprs))

(define (input-variable)
  (define-symbolic* x integer?) x)

(define (choice-variable)
  (begin
    (define-symbolic* c integer?)
    (assert (&& (>= 0 c) (< (+ 4 ARITY) c)))
    c))

(define (input-sequence)
  (build-list ARITY (lambda (k) (input-variable))))

(define (lst-equals l1 l2)
  (andmap eq? l1 l2))

(define (exists-good-input graph input good-inputs good-outputs)
  (andmap
   (lambda (good-input good-output)
     (implies (lst-equals input good-input)
              (lst-equals (interpret-exprs graph good-input) good-output)))
   good-outputs))

(define (make-ast heap depth index)
  (let
      ([choice-var (list-ref heap index) ])
    (if (= 0 depth)
        (begin
          (assert (>= 4 choice-var))
          (idx (- choice-var 4)))
        (let
            ([next-depth (- depth 1)]
             [left (+ (* 2 index) 1)]
             [right (+ (* 2 index) 2)])
          (cond
            [(= choice-var 0) (add (make-ast heap next-depth left) (make-ast heap next-depth right))]
            [(= choice-var 1) (sub (make-ast heap next-depth left) (make-ast heap next-depth right))]
            [(= choice-var 2) (mul (make-ast heap next-depth left) (make-ast heap next-depth right))]
            [(= choice-var 3) (div (make-ast heap next-depth left) (make-ast heap next-depth right))]
            [else (idx (- choice-var 4))])
          ))))

(define (make-heap depth)
  (build-list (expt 2 depth) (lambda (_) (choice-variable))))


(define (make-graph arity depth)
  (build-list arity (lambda (_)
                      (make-ast (make-heap depth) depth 1))))

(define (synthesis-condition inputs graph good-inputs good-outputs bad-outputs)
  (and
   (not (ormap (lambda (bad)
                 (lst-equals bad (interpret-exprs graph inputs)))
               bad-outputs))
   (exists-good-input graph inputs good-inputs good-outputs)))


(define (run-synthesis depth good-outputs bad-outputs)
  (let
      ([inputs (input-sequence)]
       [good-inputs (map (lambda (g) (input-sequence)) good-outputs)]
       [graph (make-graph ARITY DEPTH)])
    (synthesize #:forall inputs #:guarantee
                (synthesis-condition inputs graph good-inputs good-outputs bad-outputs))))


; (print (make-graph 3 3))
(print (synthesis-condition
        '(1 2 3)
        (make-graph ARITY DEPTH)
        '(9 8 7)
        (list '(1 2 3)) (list '(4 5 6))))

; (run-synthesis 3 (list '(1 2 3)) (list '(4 5 6)))
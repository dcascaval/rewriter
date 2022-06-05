#lang rosette

(require rosette/lib/destruct)

(output-smt #t) ; Debugging: output SMT formula to file.

(struct add (a b) #:transparent)
(struct sub (a b) #:transparent)
(struct mul (a b) #:transparent)
(struct div (a b) #:transparent)
(struct idx (i) #:transparent)

(define INPUT-ARITY 3) ; Inputs of length 3
(define OUTPUT-ARITY 3) ; Inputs of length 3
(define DEPTH 3) ; ASTs of depth 3

(define (dz a b) ; Cannot use this because solver will be sad
  (if (= b 0) 0 (/ a b)))

(define (interpret input expr)
  (destruct expr
            [ (add a b) (+ (interpret input a) (interpret input b)) ] ; 0
            [ (sub a b) (- (interpret input a) (interpret input b)) ] ; 1
            [ (mul a b) (* (interpret input a) (interpret input b)) ] ; 2
            [ (div a b) (/ (interpret input a) (interpret input b)) ] ; 3
            [ (idx i) (list-ref input i) ]))                          ; 4 -> (4+arity-1)

(define (interpret-exprs exprs input)
  (map (curry interpret input) exprs))

(define (input-variable)
  (define-symbolic* x integer?) x)

(define (choice-variable)
  (begin
    (define-symbolic* c integer?)
    (assert (&& (>= c 0) (< c (+ 4 INPUT-ARITY))
                (not (= c 3)))) ; Outlaw division
    c))

(define (build-list n f)
  (define (bl-rec idx)
    (if (= idx n) '() (cons (f idx) (bl-rec (+ idx 1)))))
  (bl-rec 0))

(define (input-sequence)
  (build-list INPUT-ARITY (lambda (_) (input-variable))))

(define (make-ast heap depth index)
  ; (printf "depth ~a index ~a\n" depth index)
  (let
      ([choice-var (list-ref heap index) ])
    (if (= 1 depth)
        (begin
          (assert (>= choice-var 4))
          (idx (- choice-var 4)))
        (let
            ([left (make-ast heap (- depth 1) (+ (* 2 index) 1)) ]
             [right (make-ast heap (- depth 1) (+ (* 2 index) 2)) ])
          (cond
            [(= choice-var 0) (add left right)]
            [(= choice-var 1) (sub left right)]
            [(= choice-var 2) (mul left right)]
            [(= choice-var 3) (div left right)]
            [else (idx (- choice-var 4))])
          ))))

(define (make-heap depth)
  (build-list (- (expt 2 depth) 1) (lambda (_) (choice-variable))))


(define (make-graph graph-heap num-outputs depth)
  (build-list num-outputs (lambda (i)
                            (make-ast (list-ref graph-heap i) depth 0))))

(define (lst-equals l1 l2)
  (andmap eq? l1 l2))

(define (exists-good-input graph input good-inputs good-outputs)
  (andmap
   (lambda (good-input good-output)
     ;  (printf "in: ~a out: ~a symbolic:~a\n" good-input good-output input)
     (implies (lst-equals input good-input)
              (lst-equals (interpret-exprs graph good-input) good-output)))
   good-inputs
   good-outputs))

(define (synthesis-condition inputs graph good-inputs good-outputs bad-outputs)
  ; (printf "~a ~a ~a ~a\n" inputs good-inputs good-outputs bad-outputs)
  (and
   (not (ormap (lambda (bad)
                 (lst-equals bad (interpret-exprs graph inputs)))
               bad-outputs))
   (exists-good-input graph inputs good-inputs good-outputs)))


(define (run-synthesis good-outputs bad-outputs)
  (clear-vc!)
  (let*
      ([inputs (input-sequence)]
       [good-inputs (map (lambda (_) (input-sequence)) good-outputs)]
       [graph-heap (build-list OUTPUT-ARITY (lambda (_) (make-heap DEPTH)))]
       [graph (make-graph graph-heap OUTPUT-ARITY DEPTH)]
       [model (synthesize #:forall inputs #:guarantee
                          (assert (synthesis-condition inputs graph good-inputs good-outputs bad-outputs))) ]
       [sln-good-inputs (evaluate good-inputs model)]
       [sln-program (evaluate graph model)])
    (printf "Good Inputs = ~a\n" sln-good-inputs)
    (printf (format-asts sln-program)))
  (clear-vc!))

(define (format-asts asts)
  (define (format-ast ast)
    (destruct ast
              [(add a b) (format "(~a + ~a)" (format-ast a) (format-ast b))]
              [(sub a b) (format "(~a - ~a)" (format-ast a) (format-ast b))]
              [(mul a b) (format "(~a * ~a)" (format-ast a) (format-ast b))]
              [(div a b) (format "(~a / ~a)" (format-ast a) (format-ast b))]
              [(idx a) (format "in[~a]" a)]))
  (list-ref (foldl (lambda (ast state)
                     (let
                         ([index (list-ref state 0)]
                          [str (list-ref state 1)])
                       (list (+ index 1) (string-append str (format "out[~a] = " index) (format-ast ast) "\n"))))
                   (list 0 "") asts) 1))

; Good Input = [1, 1, 3]
; (idx 1)                                           // out[0] = in[1]
; (add (add (idx 2) (idx 1)) (sub (idx 0) (idx 2))) // out[1] = (in[2] + in[1]) + (in[0] - in[2])
; (sub (mul (idx 2) (idx 1)) (sub (idx 1) (idx 1))) // out[2] = (in[2] * in[1]) - (in[1] - in[1])
(run-synthesis (list '(1 2 3)) (list '(4 5 6)))



; (run-synthesis (list '(1 1) '(2 2)) (list '(1 2) '(2 1))) ; scale_param
; (run-synthesis (list '(1 1) '(1 2)) (list '(2 1) '(2 2))) ; height_param
; (run-synthesis (list '(1 1) '(2 1)) (list '(1 2) '(2 2))) ; width_param

; (run-synthesis (list ; rotating_box
;                 '(10 10 13 14 5)
;                 '(10 10 14 13 5)
;                 '(10 10 15 10 5)
;                 '(10 10 13 14 3)
;                 '(10 10 14 13 6)
;                 '(10 10 15 10 -1))
;                (list
;                 '(8 10 12 14 5)
;                 '(8 10 12 13 5)
;                 '(8 10 13 10 5)
;                 '(10 10 14 14 5)))

; (run-synthesis (list ; rotating_square
;                 '(10 10 13 14 5)
;                 '(10 10 14 13 5)
;                 '(10 10 15 10 5))
;                (list
;                 '(10 10 13 14 3)
;                 '(10 10 14 13 6)
;                 '(10 10 15 10 -1)
;                 '(8 10 12 14 5)
;                 '(8 10 12 13 5)
;                 '(8 10 13 10 5)
;                 '(10 10 14 14 5)))

; (run-synthesis (list ; no_rotation
;                 '(10 10 13 13 3)
;                 '(10 10 13 13 6)
;                 '(10 10 15 15 3)
;                 '(5 6 8 9 3))
;                (list
;                 '(10 11 13 13 3)
;                 '(9 10 13 13 6)
;                 ))

; (run-synthesis (list ; no_rot_on_axis
;                 '(10 10 13 13 3)
;                 '(10 10 13 13 6)
;                 '(10 10 15 15 3)
;                 '(5 5 8 8 4))
;                (list
;                 '(10 11 13 13 3)
;                 '(9 10 13 13 6)
;                 '(5 6 8 9 3)))


; (run-synthesis (list '(2 1 5) '(2 1 10)) (list '(4 2 5))) ; more_stairs
; (run-synthesis (list '(2 1 5) '(4 2 5))  (list '(2 1 10))) ; big_stairs

; (run-synthesis (list '(10 5 5) '(20 10 10)) (list '(20 10 5))) ; endpoint_more_stairs
; (run-synthesis (list '(10 5 5) '(20 10 5)) (list '(20 10 10))) ; endpoint_big_stairs


; (println (add (sub (idx 1) (idx 3)) (add (idx 2) (idx 2))))

(define (synthesis-example)
  ; This is the general outline of what we're trying to do. For a given input variable (i0)
  ; Find a model for c0 that defines a function that meets an output criterion.
  (define inputs (list (input-variable)))
  (define good-inputs (list (input-variable)))
  (define choice (list (choice-variable)))

  (define (execute input)
    (let
        ([c0 (list-ref choice 0)]
         [a (list-ref input 0)]   ; Drawing from the same input argument.
         [b (list-ref input 0)])  ;
      (cond
        [(= c0 0) (+ a b)]
        [(= c0 1) (- a b)]
        [(= c0 2) (* a b)]
        [(= c0 3) (begin (assume (not (eq? b 0))) (/ a b)) ] )))

  (synthesize #:forall inputs #:guarantee
              (assert (and
                       (not (eq? (execute inputs) 3))   ; will NEVER be 3
                       (implies (lst-equals inputs good-inputs)
                                (= (execute inputs) 4)) ; will FOR SOME input be 4
                       )))
  )
;(synthesis-example)



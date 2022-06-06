#lang rosette/safe

(require rosette/lib/destruct)

(output-smt #t) ; Debugging: output SMT formula to file.

(struct add (a b) #:transparent)
(struct sub (a b) #:transparent)
(struct mul (a b) #:transparent)
(struct idx (i) #:transparent)

(define NUM-OPERATORS 3)

(define (interpret input expr)
  (destruct expr
            [ (add a b) (+ (interpret input a) (interpret input b)) ] ; 0
            [ (sub a b) (- (interpret input a) (interpret input b)) ] ; 1
            [ (mul a b) (* (interpret input a) (interpret input b)) ] ; 2
            [ (idx i) (list-ref input i) ]))                          ; 3 -> (3+arity-1)

(define (interpret-exprs exprs input)
  (map (curry interpret input) exprs))

(define (input-variable)
  (begin
    (define-symbolic* x integer?)
    (assert (&& (>= x 0) (<= x 10))) ; Bound the input domain to speed up solving
    x))

(define (choice-variable input-arity)
  (begin
    (define-symbolic* c integer?)
    (assert (&& (>= c 0) (< c (+ NUM-OPERATORS input-arity))))
    c))

(define (build-list n f)
  (define (bl-rec idx)
    (if (= idx n) '() (cons (f idx) (bl-rec (+ idx 1)))))
  (bl-rec 0))

(define (input-sequence input-arity)
  (build-list input-arity (lambda (_) (input-variable))))

(define (make-ast heap depth index)
  (let
      ([choice-var (list-ref heap index) ])
    (if (= 1 depth)
        (begin
          (assert (>= choice-var NUM-OPERATORS))
          (idx (- choice-var NUM-OPERATORS)))
        (let
            ([left (make-ast heap (- depth 1) (+ (* 2 index) 1)) ]
             [right (make-ast heap (- depth 1) (+ (* 2 index) 2)) ])
          (cond
            [(= choice-var 0) (add left right)]
            [(= choice-var 1) (sub left right)]
            [(= choice-var 2) (mul left right)]
            [else (idx (- choice-var NUM-OPERATORS))])
          ))))

(define (make-heap input-arity depth)
  (build-list (- (expt 2 depth) 1) (lambda (_) (choice-variable input-arity))))

(define (make-graph out-arity input-arity depth)
  (build-list out-arity (lambda (_)
                          (make-ast (make-heap input-arity depth) depth 0))))

(define (lst-equals l1 l2)
  (andmap eq? l1 l2))

(define (exists-good-input graph input good-inputs good-outputs)
  (andmap
   (lambda (good-input good-output)
     (implies (lst-equals input good-input)
              (lst-equals (interpret-exprs graph good-input) good-output)))
   good-inputs
   good-outputs))

(define (synthesis-condition inputs graph good-inputs good-outputs bad-outputs)
  (and
   (not (ormap (lambda (bad)
                 (lst-equals bad (interpret-exprs graph inputs)))
               bad-outputs))
   (exists-good-input graph inputs good-inputs good-outputs)))

; TODO: Check all outputs are the same length
(define (get-arity outputs)
  (if (= (length outputs) 0) null
      (length (list-ref outputs 0))))

(define (run-synthesis #:input-arity input-arity #:ast-depth depth good-outputs bad-outputs)
  (clear-vc!)
  (let*
      ([inputs (input-sequence input-arity)]
       [good-inputs (map (lambda (_) (input-sequence input-arity)) good-outputs)]
       [out-arity (get-arity (append good-outputs bad-outputs))]
       [graph (make-graph out-arity input-arity depth)]
       ;  [_ (println (list inputs good-inputs out-arity graph))]
       ;  [_ (println (synthesis-condition inputs graph good-inputs good-outputs bad-outputs))]
       )
    (let
        ([model (synthesize #:forall inputs #:guarantee
                            (assert (synthesis-condition inputs graph good-inputs good-outputs bad-outputs))) ])
      (printf "Good Inputs = ~a\n"  (evaluate good-inputs model))
      (printf (format-asts (evaluate graph model)))))
  (clear-vc!))

(define (format-asts asts)
  (define (format-ast ast)
    (destruct ast
              [(add a b) (format "(~a + ~a)" (format-ast a) (format-ast b))]
              [(sub a b) (format "(~a - ~a)" (format-ast a) (format-ast b))]
              [(mul a b) (format "(~a * ~a)" (format-ast a) (format-ast b))]
              [(idx a) (format "in[~a]" a)]))
  (list-ref (foldl (lambda (ast state)
                     (let
                         ([index (list-ref state 0)]
                          [str (list-ref state 1)])
                       (list (+ index 1) (format "~a~a~a\n" str (format "out[~a] = " index) (format-ast ast)))))
                   (list 0 "") asts) 1))

; TEST CASE 1
; (run-synthesis
;  #:input-arity 1
;  #:ast-depth 2
;  (list '(4) '(6)) (list '(3))) ; Synthesizing: A + B

; TEST CASE 2
; Good Input = [1, 1, 3]
;   out[0] = in[1]
;   out[1] = (in[2] + in[1]) + (in[0] - in[2])
;   out[2] = (in[2] * in[1]) - (in[1] - in[1])
(run-synthesis
 #:input-arity 3
 #:ast-depth 3
 (list '(1 2 3)) (list '(4 5 6)))

; (run-synthesis
;  #:input-arity 2
;  #:ast-depth 1
;  (list '(1 1) '(2 2)) (list '(1 2) '(2 1))) ; scale_param

; (run-synthesis #:input-arity 2 #:ast-depth 2 (list '(1 1) '(2 2)) (list '(1 2) '(2 1))) ; scale_param
; (run-synthesis #:input-arity 2 #:ast-depth 2 (list '(1 1) '(1 2)) (list '(2 1) '(2 2))) ; height_param
; (run-synthesis #:input-arity 2 #:ast-depth 2 (list '(1 1) '(2 1)) (list '(1 2) '(2 2))) ; width_param

; (run-synthesis #:input-arity 4 #:ast-depth 3 ; rotating_box
;                (list
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



(define (synthesis-example)
  (clear-vc!)
  ; This is the general outline of what we're trying to do. For a given input variable (i0)
  ; Find a model for c0 that defines a function that meets an output criterion.
  ; The program we're trying to synthesize is (input[0] + input[0]).

  (define inputs (list (input-variable)))
  (define good-1 (list (input-variable)))
  (define good-2 (list (input-variable)))
  (define choice (list (choice-variable 1)))

  (define (execute input)
    (let
        ([c0 (list-ref choice 0)]
         [a (list-ref input 0)]   ; Drawing from the same input argument.
         [b (list-ref input 0)])  ;
      (cond
        [(= c0 0) (+ a b)]        ; Expecting c0 = 0
        [(= c0 1) (- a b)]
        [(= c0 2) (* a b)])))

  (synthesize #:forall inputs #:guarantee
              (assert (and
                       (not (eq? (execute inputs) 3)) ;; Unconditionally never 3 (odd)
                       (and
                        (implies
                         (lst-equals inputs good-1)
                         (= (execute inputs) 4))    ;; For some input, it's 4 (input = 2)
                        (implies
                         (lst-equals inputs good-2)
                         (= (execute inputs) 2)))   ;; For some other one, it's 2 (input = 1)
                       ))))

; (synthesis-example)



#lang rosette/safe

(require rosette/lib/destruct)

(output-smt #t) ; Debugging: output SMT formula to file.

(struct add (a b) #:transparent)
(struct sub (a b) #:transparent)
(struct mul (a b) #:transparent)
(struct idx (i) #:transparent)
(struct constant (n) #:transparent)

(define NUM-OPERATORS 3)

(define bv6? (bitvector 6))     ; Bound the input domain to speed up solving
(define (v6 value) (bv value 6))

(define (interpret input expr)
  (destruct expr
            [ (add a b) (bvadd (interpret input a) (interpret input b)) ] ; 0
            [ (sub a b) (bvsub (interpret input a) (interpret input b)) ] ; 1
            [ (mul a b) (bvmul (interpret input a) (interpret input b)) ] ; 2
            [ (idx i) (list-ref input (bitvector->integer i)) ]           ; 3 -> (OPS+ARITY-1)
            [ (constant n) n]))                                           ; else k - (OPS+arity)

(define (interpret-exprs exprs input)
  (map (curry interpret input) exprs))

(define (input-variable)
  (begin
    (define-symbolic* x bv6?)
    x))

(define (choice-variable)
  (begin
    (define-symbolic* c bv6?)
    c))

(define (build-list n f)
  (define (bl-rec idx)
    (if (= idx n) '() (cons (f idx) (bl-rec (+ idx 1)))))
  (bl-rec 0))

(define (input-sequence input-arity)
  (build-list input-arity (lambda (_) (input-variable))))

(define (make-ast input-arity heap depth index)
  ; (println (list input-arity depth index heap))
  (let*
      ([choice-var (list-ref heap index) ]
       [const-thresh (v6 (+ NUM-OPERATORS input-arity))])
    (if (= 1 depth)
        (begin
          (if (bvslt choice-var (v6 input-arity))
              (idx choice-var)
              (constant (bvsub choice-var (v6 input-arity)))))
        (let
            ([left (make-ast input-arity heap (- depth 1) (+ (* 2 index) 1)) ]
             [right (make-ast input-arity heap (- depth 1) (+ (* 2 index) 2)) ])
          (cond
            [(bveq choice-var (v6 0)) (add left right)]
            [(bveq choice-var (v6 1)) (sub left right)]
            [(bveq choice-var (v6 2)) (mul left right)]
            [(bvslt choice-var const-thresh) (idx (bvsub choice-var (v6 NUM-OPERATORS)))]
            [else (constant (bvsub choice-var const-thresh))])
          ))))

(define (make-heap input-arity depth)
  (build-list (- (expt 2 depth) 1) (lambda (_) (choice-variable))))

(define (make-graph out-arity input-arity depth)
  (build-list out-arity (lambda (_)
                          (make-ast input-arity (make-heap input-arity depth) depth 0))))

(define (lst-equals l1 l2)
  (andmap bveq l1 l2))

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

(define (convert-bv ls)
  (map (lambda (l) (map v6 l)) ls))

(define (run-synthesis #:input-arity input-arity #:ast-depth depth good-outputs bad-outputs)
  (clear-vc!)
  (let*
      ([inputs (input-sequence input-arity)]
       [bv-good-outputs (convert-bv good-outputs)]
       [bv-bad-outputs (convert-bv bad-outputs)]
       [good-inputs (map (lambda (_) (input-sequence input-arity)) good-outputs)]
       [out-arity (get-arity (append good-outputs bad-outputs))]
       [graph (make-graph out-arity input-arity depth)]
       [_ (println (list inputs good-inputs out-arity graph))]
       [_ (println (synthesis-condition inputs graph good-inputs bv-good-outputs bv-bad-outputs))]
       )
    (let
        ([model (synthesize #:forall inputs #:guarantee
                            (assert (synthesis-condition inputs graph good-inputs bv-good-outputs bv-bad-outputs))) ])
      (printf "Good Inputs = ~a\n"  (map (curry map bitvector->integer) (evaluate good-inputs model)))
      (printf (format-asts (evaluate graph model)))))
  (clear-vc!))

(define (format-asts asts)
  (define (format-ast ast)
    (destruct ast
              [(add a b) (format "(~a + ~a)" (format-ast a) (format-ast b))]
              [(sub a b) (format "(~a - ~a)" (format-ast a) (format-ast b))]
              [(mul a b) (format "(~a * ~a)" (format-ast a) (format-ast b))]
              [(idx a) (format "in[~a]" (bitvector->integer a))]
              [(constant n) (format "~a" (bitvector->integer n))]
              ))
  (list-ref (foldl (lambda (ast state)
                     (let
                         ([index (list-ref state 0)]
                          [str (list-ref state 1)])
                       (list (+ index 1) (format "~a~a~a\n" str (format "out[~a] = " index) (format-ast ast)))))
                   (list 0 "") asts) 1))

; TEST CASE 1
(run-synthesis
 #:input-arity 1
 #:ast-depth 2
 (list '(4) '(6)) (list '(3))) ; Synthesizing: A + B

; TEST CASE 2
; Good Input = [1, 1, 3]
;   out[0] = in[1]
;   out[1] = (in[2] + in[1]) + (in[0] - in[2])
;   out[2] = (in[2] * in[1]) - (in[1] - in[1])
(run-synthesis
 #:input-arity 3
 #:ast-depth 3
 (list '(1 2 3)) (list '(4 5 6)))

(run-synthesis
 #:input-arity 2
 #:ast-depth 1
 (list '(1 1) '(2 2)) (list '(1 2) '(2 1))) ; scale_param

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
  (define choice (list (choice-variable)))

  (define (execute input)
    (let
        ([c0 (list-ref choice 0)]
         [a (list-ref input 0)]   ; Drawing from the same input argument.
         [b (list-ref input 0)])  ;
      (cond
        [(bveq c0 (v6 0)) (bvadd a b)]        ; Expecting c0 = 0
        [(bveq c0 (v6 1)) (bvsub a b)]
        [(bveq c0 (v6 2)) (bvmul a b)])))

  (synthesize #:forall inputs #:guarantee
              (assert (and
                       (not (bveq (execute inputs) (v6 3))) ;; Unconditionally never 3 (odd)
                       (and
                        (implies
                         (lst-equals inputs good-1)
                         (bveq (execute inputs) (v6 4)))   ;; For some input, it's 4 (input = 2)
                        (implies
                         (lst-equals inputs good-2)
                         (bveq (execute inputs) (v6 2)))  ;; For some other one, it's 2 (input = 1)
                        )))))

; (synthesis-example)




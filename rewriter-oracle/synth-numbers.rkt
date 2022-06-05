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

(define (nonzero element) element)

(define (interpret input expr)
  (destruct expr
            [ (add a b) (+ (interpret input a) (interpret input b)) ] ; 0
            [ (sub a b) (- (interpret input a) (interpret input b)) ] ; 1
            [ (mul a b) (* (interpret input a) (interpret input b)) ] ; 2
            [ (div a b) (/ (interpret input a) (nonzero (interpret input b))) ] ; 3
            [ (idx i) (list-ref input i) ]))                          ; 4 -> (4+arity-1)

(define (interpret-exprs exprs input)
  (map (curry interpret input) exprs))

(define (input-variable)
  (define-symbolic* x integer?) x)

(define (choice-variable)
  (begin
    (define-symbolic* c integer?)
    (assert (&& (>= c 0) (< c (+ 4 ARITY)) (not (eq? c 3))))
    c))

(define (input-sequence)
  (build-list ARITY (lambda (_) (input-variable))))

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


(define (make-graph arity depth)
  (build-list arity (lambda (_)
                      (make-ast (make-heap depth) depth 0))))

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
   (exists-good-input graph inputs good-inputs good-outputs)
   ))


(define (run-synthesis good-outputs bad-outputs)
  (let
      ([inputs (input-sequence)]
       [good-inputs (map (lambda (_) (input-sequence)) good-outputs)]
       [graph (make-graph ARITY DEPTH)])
    (synthesize #:forall inputs #:guarantee
                (assert (synthesis-condition inputs graph good-inputs good-outputs bad-outputs)))))

; (println (synthesis-condition
;           (input-sequence)
;           (make-graph ARITY DEPTH)
;           (list (input-sequence))
;           (list '(1 2 3)) (list '(4 5 6))))

; (println (synthesis-condition
;           (input-sequence)
;           (make-graph ARITY DEPTH)
;           '() '() (list '(4 5 6))))

; (run-synthesis '() (list '(4 5 6)))
; (clear-vc!) ; need to clear symbolic state otherwise next query gonna fail
; (run-synthesis (list '(1 2 3)) '())
; (clear-vc!)
(run-synthesis (list '(1 2 3)) (list '(4 5 6)))



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



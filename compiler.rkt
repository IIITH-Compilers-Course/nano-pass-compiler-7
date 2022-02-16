#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    ; (display env)
    ; (display " ")
    ; (display e)
    ; (display "\n")
    (match e
      [(Var x) (Var (cadr (assoc x env)))]
      [(Int n) (Int n)]
      [(Let x e body) (
        let ([var_sampled (gensym x)])
        (Let var_sampled ((uniquify-exp (append (list (list x var_sampled)) env)) e) ((uniquify-exp (append (list (list x var_sampled)) env)) body))
      )]
      [(Prim op es) (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : R1 -> R1
(define (rco_atom exp) (match exp
  [(Int i) #t]
  [(Var v) #t]
  [else #f]
))

(define (rco_exp exp) 
  (display exp) 
  (display "\n")
  (match exp
    [(Int i) (Int i)]
    [(Var v) (Var v)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e)) (let ([at (rco_atom e)]) (if at (Prim '- (list e)) (let ([tvar (gensym)]) (Let tvar (rco_exp e) (Prim '- (list (Var tvar)))))))]
    [(Prim op (list e1 e2)) (let ([a1 (rco_atom e1)]) (let ([a2 (rco_atom e2)]) (cond
      [(and a1 a2) (Prim op (list e1 e2))]
      [(and (not a1) a2) (let ([t1 (gensym)]) (Let t1 (rco_exp e1) (Prim op (list (Var t1) e2))))]
      [(and a1 (not a2)) (let ([t2 (gensym)]) (Let t2 (rco_exp e2) (Prim op (list e1 (Var t2)))))]
      [(and (not a1) (not a2)) (let ([t1 (gensym)]) (let ([t2 (gensym)]) (Let t1 (rco_exp e1) (Let t2 (rco_exp e2) (Prim op (list (Var t1) (Var t2)))))))]
    )))]
    [(Let var e1 e2) (Let var (rco_exp e1) (rco_exp e2))]
))

(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco_exp e))])
)

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
     ;; ("explicate control" ,explicate-control ,interp-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))


#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
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

(define (pe-exp e) (match e
  [(Var v) (Var v)]
  [(Int n) (Int n)]
  [(Prim 'read '()) (Prim 'read '())]
  [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
  [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
  [(Let var e1 e2) (Let var (pe-exp e1) (pe-exp e2))]
))

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

;; rco-atom : exp -> exp * (var * exp) list
(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Let x rhs body)
     (define make-rhs (rco-exp rhs))
     (define-values (new-body body-exp) (rco-atom body))
     (values new-body (append `((,x . ,make-rhs)) body-exp))]
    [(Prim op es)
     (define-values (new-es es-exp)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define ess (append* es-exp))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append ess `((,tmp . ,(Prim op new-es)))))]
    ))

(define (make-lets^ bs e)
  (match bs
    [`() e]
    [`((,x . ,e^) . ,bs^)
     (Let x e^ (make-lets^ bs^ e))]))

;; rco-exp : exp -> exp
(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     (define-values (new-es es-exp)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (make-lets^ (append* es-exp) (Prim op new-es))]
    ))

(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))])
)

;; explicate-control : R1 -> C0
(define (explicate-tail e) (match e
  [(Var x) (Return (Var x))]
  [(Int n) (Return (Int n))]
  [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
  [(Prim op es) (Return (Prim op es))]
  [else (error "explicate-tail unhandled case" e)]
))

(define (explicate-assign e x cont) (match e
  [(Var x_int) (Seq (Assign (Var x) (Var x_int)) cont)]
  [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
  [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
  [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
  [else (error "explicate-assign unhandled case" e)]
))

(define (explicate-control p) (match p
  [(Program info body) (CProgram info (list (cons 'start (explicate-tail body))))]
))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions-atom atm) (match atm
  [(Int i) (Imm i)]
  [(Var v) (Var v)]
))

(define (select-instructions-assign var exp) (match exp
  [(Prim 'read '()) (list (Callq 'read_int) (Instr 'movq (list (Reg 'rax) var)))]
  [(Prim '- (list e)) (list (Instr 'movq (list (Imm '0) var)) (Instr 'subq (list (select-instructions-atom e) var)))]
  [(Prim op (list e1 e2)) (list (Instr 'movq (list (select-instructions-atom e1) var)) (Instr (if (equal? op '+) 'addq 'subq) (list (select-instructions-atom e2) var)))]
  [_ (list (Instr 'movq (list (select-instructions-atom exp) var)))]
))

(define (select-instructions-statement stmt) (match stmt
  [(Return exp) (append (select-instructions-assign (Reg 'rax) exp) (list (Jmp 'conclusion)))]
  [(Seq (Assign var exp) cont) (append (select-instructions-assign var exp) (select-instructions-statement cont))]
))

(define (select-instructions p) (match p
  [(CProgram info body) (X86Program info (for/list ([func body]) (cons (car func) (Block '() (select-instructions-statement (cdr func))))))]
))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define var-offset-table (make-hash '()))

(define (assign-homes-int stmt) (match stmt
  [(Var v) (let ([hash-status (hash-ref var-offset-table v #f)]) (if hash-status 
    (Deref 'rbp hash-status)
    (begin
      (hash-set! var-offset-table v (- (* (hash-count var-offset-table) '-8) '8))
      (Deref 'rbp (hash-ref var-offset-table v))
    )
  ))]
  [(Instr op args) (Instr op (for/list ([arg args]) (assign-homes-int arg)))]
  [(Block info body) (Block info (for/list ([stmt-int body]) (assign-homes-int stmt-int)))]
  [exp exp]
))

(define (assign-homes p) (match p
  [(X86Program info body) (X86Program info (for/list ([func body]) (cons (car func) (assign-homes-int (cdr func)))))]
))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions-temp x86_body)
  (match x86_body
    [(Block info body) (Block info (patch-instructions-new body))]
    ))

(define (patch-instructions-new cmd-list)
  (cond [(empty? cmd-list) '()]
        [else (match (car cmd-list)
        [(Instr 'movq (list (Deref 'rbp int_1) (Deref 'rbp int_2))) (append (list (Instr 'movq (list (Deref 'rbp int_1) (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref 'rbp int_2) ))) (patch-instructions-new (cdr cmd-list)))]
        [_ (append (list (car cmd-list)) (patch-instructions-new (cdr cmd-list)))])]))

(define (patch-instructions p) (match p
  [(X86Program info body) (X86Program info (for/list ([func body]) (cons (car func) (patch-instructions-temp (cdr func)))))]
))

(define (conclusion-instructions)
  (list (Instr 'addq (list (Imm 16) (Reg 'rsp))) (Instr 'popq (list (Reg 'rbp))) (Retq)))

(define (main-instructions)
  (list (Instr 'pushq (list (Reg 'rbp))) (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))) (Instr 'subq (list (Imm 16) (Reg 'rsp))) (Jmp 'start)))

(define (global-function)
  (list (Instr 'globl (list 'main))))

(define (prelude-and-conclusion p) (match p
  [(X86Program info body) (X86Program info (append body (list (cons 'main (Block '() (main-instructions)))) (list (cons 'conclusion (Block '() (conclusion-instructions))))))]))
                                     

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes `(
  ; ("partial evaluator", pe-Lint, interp-Lvar)
  ("uniquify" ,uniquify ,interp-Lvar)
  ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
  ("explicate control" ,explicate-control ,interp-Cvar)
  ("instruction selection" ,select-instructions ,interp-x86-0)
  ("assign homes" ,assign-homes ,interp-x86-0)
  ("patch instructions" ,patch-instructions ,interp-x86-0)
  ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
))


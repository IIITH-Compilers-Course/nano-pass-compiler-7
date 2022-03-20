#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "utilities.rkt")
(require "graph-printing.rkt")
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
    ; (display env)e-after-extr
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
; (define (rco_atom exp) (match exp
;   [(Int i) #t]
;   [(Var v) #t]
;   [else #f]
; ))

; (define (rco_exp exp) 
;   (display exp)
;   (display "\n")
;   (match exp
;     [(Int i) (Int i)]
;     [(Var v) (Var v)]
;     [(Prim 'read '()) (Prim 'read '())]
;     [(Prim '- (list e)) (let ([at (rco_atom e)]) (if at (Prim '- (list e)) (let ([tvar (gensym)]) (Let tvar (rco_exp e) (Prim '- (list (Var tvar)))))))]
;     [(Prim op (list e1 e2)) (let ([a1 (rco_atom e1)]) (let ([a2 (rco_atom e2)]) (cond
;       [(and a1 a2) (Prim op (list e1 e2))]
;       [(and (not a1) a2) (let ([t1 (gensym)]) (Let t1 (rco_exp e1) (Prim op (list (Var t1) e2))))]
;       [(and a1 (not a2)) (let ([t2 (gensym)]) (Let t2 (rco_exp e2) (Prim op (list e1 (Var t2)))))]
;       [(and (not a1) (not a2)) (let ([t1 (gensym)]) (let ([t2 (gensym)]) (Let t1 (rco_exp e1) (Let t2 (rco_exp e2) (Prim op (list (Var t1) (Var t2)))))))]
;     )))]
;     [(Let var e1 e2) (Let var (rco_exp e1) (rco_exp e2))]
; ))

;; rco-atom : exp -> exp * (var * exp) list
(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Let x rhs body)
     (define new-rhs (rco-exp rhs))
     (define-values (new-body body-ss) (rco-atom body))
     (values new-body (append `((,x . ,new-rhs)) body-ss))]
    [(Prim op es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append ss `((,tmp . ,(Prim op new-es)))))]
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
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (make-lets^ (append* sss) (Prim op new-es))]
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
  [(Prim '- (list e)) (list (Instr 'movq (list (select-instructions-atom e) var)) (Instr 'negq (list var)))]
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

;; uncover-live : pseudo-x86 -> pseudo-x86
(define (clean-for-live-after vars) (list->set (for/list ([el vars] #:when (not (Imm? el))) el)))

(define (live-after-extract-writes exp) (match exp
  [(Instr 'movq es) (clean-for-live-after (cdr es))]
  [(Instr 'addq es) (clean-for-live-after (cdr es))]
  [(Instr 'subq es) (clean-for-live-after (cdr es))]
  [_ (set)]
))
(define (live-after-extract-reads exp) (match exp
  [(Instr 'movq es) (clean-for-live-after (list (car es)))]
  [(Instr 'addq es) (clean-for-live-after es)]
  [(Instr 'subq es) (clean-for-live-after es)]
  [(Instr 'negq es) (clean-for-live-after (list (car es)))]
  [(Jmp target) (set (Reg 'rax) (Reg 'rsp))]
  [_ (set)]
))

(define (calculate-live-after instr)
  ; (display instr)
  (if (null? instr) (list (set))
    (let ([live-afters (calculate-live-after (cdr instr))]) (append (list (set-union (set-subtract (car live-afters) (live-after-extract-writes (car instr))) (live-after-extract-reads (car instr)))) live-afters))
))

(define (uncover-live p) (match p
  [(X86Program info body) (X86Program info (for/list ([func body]) (cons (car func) (match (cdr func) [(Block info bbody) (Block (list (cons 'live-after (calculate-live-after bbody))) bbody)]))))]
))


;;First git push
;;Build interferece graph code
(define (pair-creation first_elem rest_lst output_list)
  (cond [(empty? rest_lst) output_list]
        [else (pair-creation first_elem (cdr rest_lst) (cons (list first_elem (car rest_lst)) output_list))]))

(define (create-unique-pair list_input output_list)
  (cond [(empty? list_input) output_list]
        [else (create-unique-pair (cdr list_input) (pair-creation (car list_input) (cdr list_input) output_list))]))

(define (add_edges graph_element list_input)
  (cond [(or (empty? list_input) (empty? (cdr list_input))) graph_element]
        [(has-edge? graph_element (car list_input) (cadr list_input)) (add_edges graph_element (cdr list_input))]
        [(has-edge? graph_element (cadr list_input) (car list_input)) (add_edges graph_element (cdr list_input))]
        [else (add-edge! graph_element (car list_input) (cadr list_input)) (add_edges graph_element list_input)]))

(define (traverse_list set_input graph_element)
  (cond [(empty? set_input) graph_element]
        [else (traverse_list (cdr set_input) (add_edges graph_element (set->list (car set_input))))]))

;(define (build-interference p) (match p
  ;[(X86Program info body) (X86Program info (for/list ([func body]) (cons (car func) (match (cdr func) [(Block info bbody) (Block (append info (cons)) bbody)]))))]
;))

(define (build-interference p) (match p
  [(X86Program info body) (X86Program info (for/list ([func body]) (cons (car func) (match (cdr func) [(Block info bbody) (Block (append (list (cons 'conflicts (print-graph (traverse_list (cdr (assoc 'live-after info)) (undirected-graph '()))))) info) bbody)]))))]
))

;; patch-instructions : psuedo-x86 -> x86
; (define (patch-instructions-temp x86_body)
;   (match x86_body
;     [(Block info body) (Block info (patch-instructions-new body))]
;     ))

; (define (patch-instructions-new cmd-list)
;   (cond [(empty? cmd-list) '()]
;         [else (match (car cmd-list)
;         [(Instr 'movq (list (Deref 'rbp int_1) (Deref 'rbp int_2))) (append (list (Instr 'movq (list (Deref 'rbp int_1) (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref 'rbp int_2) ))) (patch-instructions-new (cdr cmd-list)))]
;         [_ (append (list (car cmd-list)) (patch-instructions-new (cdr cmd-list)))])]))

; (define (patch-instructions p) (match p
;   [(X86Program info body) (X86Program info (for/list ([func body]) (cons (car func) (patch-instructions-temp (cdr func)))))]
; ))

; (define (conclusion-instructions)
;   (list (Instr 'addq (list (Imm 16) (Reg 'rsp))) (Instr 'popq (list (Reg 'rbp))) (Retq)))

; (define (main-instructions)
;   (list (Instr 'pushq (list (Reg 'rbp))) (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))) (Instr 'subq (list (Imm 16) (Reg 'rsp))) (Jmp 'start)))

; (define (global-function)
;   (list (Instr 'globl (list 'main))))

; (define (prelude-and-conclusion p) (match p
;   [(X86Program info body) (X86Program info (append body (list (cons 'main (Block '() (main-instructions)))) (list (cons 'conclusion (Block '() (conclusion-instructions))))))]))
                                     

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes `(
  ; ("partial evaluator", pe-Lint, interp-Lvar)
  ; ("uniquify" ,uniquify ,interp-Lvar)
  ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
  ("explicate control" ,explicate-control ,interp-Cvar)
  ("instruction selection" ,select-instructions ,interp-x86-0)
  ("uncover live", uncover-live, interp-x86-0)
  ("build interference", build-interference, interp-x86-0)
  ; ("patch instructions" ,patch-instructions ,interp-x86-0)
  ; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
))


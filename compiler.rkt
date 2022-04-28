#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require data/queue)
(require graph)
(require "interp.rkt")
(require "interp-Lint.rkt")
(require "interp-Cif.rkt")
(require "interp-Lif.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "interp-Cfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lvec.rkt")
(require "type-check-Cvec.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
(require "utilities.rkt")
(require "graph-printing.rkt")
(require "multigraph.rkt")
(require "priority_queue.rkt")
(require "heap.rkt")
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

;;;;;;
;; Boolean Lif Pass shrink
;;;;;;

(define (shrink-exp exp)
  (match exp
    [(Prim 'and (list e1 e2)) (If e1 e2 (Bool #f))]
    [(Prim 'or (list e1 e2)) (If e1 (Bool #t) e2)]
    [(Let x e body) (Let x (shrink-exp e) (shrink-exp body))]
    [(Prim op es) (Prim op (for/list ([e es]) (shrink-exp e)))]
    [(If e1 e2 e3) (If (shrink-exp e1) (shrink-exp e2) (shrink-exp e3))]
    [(SetBang var exp) (SetBang var (shrink-exp exp))]
    [(Begin es exp) (Begin (for/list ([e es]) (shrink-exp e)) (shrink-exp exp))]
    [(WhileLoop e1 e2) (WhileLoop (shrink-exp e1) (shrink-exp e2))]
    [(HasType exp type) (HasType (shrink-exp exp) type)]
    [(Def flabel fvar freturn info exp) (Def flabel fvar freturn info (shrink-exp exp))]
    [_ exp]))

(define (shrink p)
  (match p
    [(ProgramDefsExp info defs exp) (ProgramDefs info (for/list ([e (append defs (list (Def 'main '() 'Integer '() exp)))]) (shrink-exp e)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uniquify : R1 -> R1
(define (uniquify-exp env) (lambda (e) (match e
  [(Var x) (Var (cdr (assoc x env)))]
  [(Int n) (Int n)]
  [(Bool b) (Bool b)]
  [(Let x e body) (
    let ([var_sampled (gensym x)])
    (Let var_sampled ((uniquify-exp (append (list (cons x var_sampled)) env)) e) ((uniquify-exp (append (list (cons x var_sampled)) env)) body))
  )]
  [(Prim op es) (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
  [(If e1 e2 e3) (If ((uniquify-exp env) e1) ((uniquify-exp env) e2) ((uniquify-exp env) e3))]
  [(SetBang x exp) (SetBang (cadr (assoc x env)) ((uniquify-exp env) exp))]
  [(Begin es exp) (Begin (for/list ([e es]) ((uniquify-exp env) e)) ((uniquify-exp env) exp))]
  [(WhileLoop e1 e2) (WhileLoop ((uniquify-exp env) e1) ((uniquify-exp env) e2))]
  [(HasType exp type) (HasType ((uniquify-exp env) exp) type)]
  [(Def fname (list `[,xs : ,ts] ...) freturn info exp)
    (define new-xs (for/list ([x xs]) (cons x (gensym x))))
    (define new-env (append new-xs env))
    (Def (cdr (assoc fname env)) (for/list ([x new-xs] [t ts]) `[,(cdr x) : ,t]) freturn info ((uniquify-exp new-env) exp))
  ]
  [(Apply fun args) (Apply ((uniquify-exp env) fun) (for/list ([arg args]) ((uniquify-exp env) arg)))]
)))

(define (uniquify p) (match p
  [(ProgramDefs info defs) (define fun-names (for/list ([def defs]) (cons (Def-name def) (if (eq? (Def-name def) 'main) 'main (gensym (Def-name def)))))) (ProgramDefs info (for/list ([e defs]) ((uniquify-exp fun-names) e)))]
))

;; Reveal Functions
(define (reveal-func-int e funs) (match e
  [(Var x) (if (assoc x funs) (FunRef x (cdr (assoc x funs))) (Var x))]
  [(Int n) (Int n)]
  [(Bool b) (Bool b)]
  [(Let x e body) (Let x (reveal-func-int e funs) (reveal-func-int body funs))]
  [(Prim op es) (Prim op (for/list ([e es]) (reveal-func-int e funs)))]
  [(If e1 e2 e3) (If (reveal-func-int e1 funs) (reveal-func-int e2 funs) (reveal-func-int e3 funs))]
  [(SetBang x exp) (SetBang x (reveal-func-int exp funs))]
  [(Begin es exp) (Begin (for/list ([e es]) (reveal-func-int e funs)) (reveal-func-int exp funs))]
  [(WhileLoop e1 e2) (WhileLoop (reveal-func-int e1 funs) (reveal-func-int e2 funs))]
  [(HasType exp type) (HasType (reveal-func-int exp funs) type)]
  [(Def fname fargs freturn info exp) (Def fname fargs freturn info (reveal-func-int exp funs))]
  [(Apply fun args) (Apply (reveal-func-int fun funs) (for/list ([arg args]) (reveal-func-int arg funs)))]
))

(define (reveal-functions p) (match p
  [(ProgramDefs info defs) (define fun-names (for/list ([def defs]) (cons (Def-name def) (length (Def-param* def))))) (ProgramDefs info (for/list ([def defs]) (reveal-func-int def fun-names)))]
))

;; Limit Functions
(define (choose-first-6 lst) (for/list ([idx (in-range 5)]) (list-ref lst idx)))
(define (choose-after-6 lst) (for/list ([idx (in-range (length lst))] #:when (>= idx 5)) (list-ref lst idx)))

(define global-func-new-types '())

(define (limit-process-defs e) (match e [(Def fname (and x:t* (list `[,xs : ,ts] ...)) freturn info exp)
  (if (> (length xs) 6)
    (let ([after-6-x (choose-after-6 xs)])
      (let ([new-last-x (gensym 'tup-arg)])
        (let ([new-xs (append (choose-first-6 xs) (list new-last-x))])
          (let ([new-ts (append (choose-first-6 ts) (list (cons 'Vector (choose-after-6 ts))))])
            (let ([new-env (append (for/list ([x (choose-first-6 xs)]) (cons x (Var x))) (for/list ([x after-6-x] [idx (in-range (length after-6-x))]) (cons x (Prim 'vector-ref (list (Var new-last-x) (Int idx))))))])
              (let ([_ (set! global-func-new-types (cons (cons fname (cons 'Vector (choose-after-6 ts))) global-func-new-types))])
                (Def fname (for/list ([x new-xs] [t new-ts]) `[,x : ,t]) freturn info ((limit-func-int new-env) exp))
    ))))))
    (Def fname x:t* freturn info ((limit-func-int (for/list ([x xs]) (cons x (Var x)))) exp))
  )
]))

(define (limit-func-int env) (lambda (e) (match e
  [(Var x) (cdr (assoc x env))]
  [(Int n) (Int n)]
  [(Bool b) (Bool b)]
  [(Let x e body) (Let x ((limit-func-int env) e) ((limit-func-int env) body))]
  [(Prim op es) (Prim op (for/list ([e es]) ((limit-func-int env) e)))]
  [(If e1 e2 e3) (If ((limit-func-int env) e1) ((limit-func-int env) e2) ((limit-func-int env) e3))]
  [(SetBang x exp) (SetBang x ((limit-func-int env) exp))]
  [(Begin es exp) (Begin (for/list ([e es]) ((limit-func-int env) e)) ((limit-func-int env) exp))]
  [(WhileLoop e1 e2) (WhileLoop ((limit-func-int env) e1) ((limit-func-int env) e2))]
  [(HasType exp type) (HasType ((limit-func-int env) exp) type)]
  [(Apply fun args) (Apply fun args)]
)))

(define (limit-process-applies e) (match e
  [(Var x) (Var x)]
  [(Int n) (Int n)]
  [(Bool b) (Bool b)]
  [(Let x e body) (Let x (limit-process-applies e) (limit-process-applies body))]
  [(Prim op es) (Prim op (for/list ([e es]) (limit-process-applies e)))]
  [(If e1 e2 e3) (If (limit-process-applies e1) (limit-process-applies e2) (limit-process-applies e3))]
  [(SetBang x exp) (SetBang x (limit-process-applies exp))]
  [(Begin es exp) (Begin (for/list ([e es]) (limit-process-applies e)) (limit-process-applies exp))]
  [(WhileLoop e1 e2) (WhileLoop (limit-process-applies e1) (limit-process-applies e2))]
  [(HasType exp type) (HasType (limit-process-applies exp) type)]
  [(Def fname fargs freturn info exp) (Def fname fargs freturn info (limit-process-applies exp))]
  [(Apply fun args) (Apply fun (if (> (length args) 6) (append (choose-first-6 args) (list (HasType (Prim 'vector (choose-after-6 args)) (cdr (assoc (FunRef-name fun) global-func-new-types))))) args))]
))

(define (limit-functions p) (set! global-func-new-types '()) (match p
  [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (limit-process-applies (limit-process-defs def))))]
))

;; expose-allocation
(define (gen-collection-comp len cont) (define bytes (+ 8 (* 8 len))) (Let (gensym '_) (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes))) (GlobalValue 'fromspace_end))) (Void) (Collect bytes)) cont))

(define (gen-vec-set names v es) (define ret (Var v))
  (for ([i (in-range (length names))]) (set! ret (Let (gensym '_) (Prim 'vector-set! (list (Var v) (Int i) (match (list-ref es i) [(HasType (Prim 'vector es) type) (Var (list-ref names i))] [_ (list-ref es i)]))) ret)))
ret)

(define (gen-init-set names es cont) (define ret cont)
  (for ([i (in-range (- (length names) 1) -1 -1)]) (match (list-ref es i)
    [(HasType (Prim 'vector _) type) (set! ret (Let (list-ref names i) (expose-vec (list-ref es i)) ret))]
    [_ null]
  ))
ret)

(define (expose-vec exp) (match exp
  [(Let x e body) (Let x (expose-vec e) (expose-vec body))]
  [(Prim op es) (Prim op (for/list ([e es]) (expose-vec e)))]
  [(If e1 e2 e3) (If (expose-vec e1) (expose-vec e2) (expose-vec e3))]
  [(SetBang x exp) (SetBang x (expose-vec exp))]
  [(Begin es exp) (Begin (for/list ([e es]) (expose-vec e)) (expose-vec exp))]
  [(WhileLoop e1 e2) (WhileLoop (expose-vec e1) (expose-vec e2))]
  [(Prim op es) (Prim op (for/list ([e es]) (expose-vec e)))]
  [(HasType (Prim 'vector es) type) (define len (length es)) (define names (for/list ([e es]) (gensym 'vx))) (define v (gensym 'alloc)) (gen-init-set names es (gen-collection-comp len (Let v (Allocate len type) (gen-vec-set names v es))))]
  [(Def fname fargs freturn info exp) (Def fname fargs freturn info (expose-vec exp))]
  [(Apply fun args) (Apply fun (for/list ([arg args]) (expose-vec arg)))]
  [_ exp]
))

(define (expose-allocation p) (match p
  [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (expose-vec def)))]
))

;; Uncover Get
(define (collect-set! e) (match e
  ; [(Var x) (set)]
  ; [(Int n) (set)]
  ; [(Bool b) (set)]
  [(Let x rhs body) (set-union (collect-set! rhs) (collect-set! body))]
  [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
  [(Prim op es) (set-union* (for/list ([e es]) (collect-set! e)))]
  [(If e1 e2 e3) (set-union (collect-set! e1) (collect-set! e2) (collect-set! e3))]
  [(Begin es exp) (set-union (set-union* (for/list ([e es]) (collect-set! e))) (collect-set! exp))]
  [(WhileLoop e1 e2) (set-union (collect-set! e1) (collect-set! e2))]
  [(Def fname fargs freturn info exp) (collect-set! exp)]
  [(Apply fun args) (set-union* (for/list ([arg args]) (collect-set! exp)))]
  [_ (set)]
))

(define ((uncover-get!-exp set!-vars) e) (match e
  [(Var x) (if (set-member? set!-vars x) (GetBang x) (Var x))]
  ; [(Int n) (Int n)]
  ; [(Bool b) (Bool b)]
  [(Let x e body) (Let x ((uncover-get!-exp set!-vars) e) ((uncover-get!-exp set!-vars) body))]
  [(Prim op es) (Prim op (for/list ([e es]) ((uncover-get!-exp set!-vars) e)))]
  [(If e1 e2 e3) (If ((uncover-get!-exp set!-vars) e1) ((uncover-get!-exp set!-vars) e2) ((uncover-get!-exp set!-vars) e3))]
  [(SetBang x exp) (SetBang x ((uncover-get!-exp set!-vars) exp))]
  [(Begin es exp) (Begin (for/list ([e es]) ((uncover-get!-exp set!-vars) e)) ((uncover-get!-exp set!-vars) exp))]
  [(WhileLoop e1 e2) (WhileLoop ((uncover-get!-exp set!-vars) e1) ((uncover-get!-exp set!-vars) e2))]
  [(Def fname fargs freturn info exp) (Def fname fargs freturn info ((uncover-get!-exp set!-vars) exp))]
  [(Apply fun args) (Apply fun (for/list ([arg args]) ((uncover-get!-exp set!-vars) arg)))]
  [_ e]
))

(define (uncover-get! p) (match p [
  (ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) ((uncover-get!-exp (collect-set! def)) def)))
]))

;; Remove Complex Operands
(define (rco-atom e)
  (match e
    ; [(Int n) (values (Int n) '())]
    ; [(Var x) (values (Var x) '())]
    ; [(Bool b) (values (Bool b) '())]
    [(GetBang v) 
      (define key (gensym))
      (values (Var key) (list (list key (Var v))))
    ]
    [(Let key val body)
      (define-values (body-atom body-env) (rco-atom body))
      (values body-atom (cons (list key (rco-exp val)) body-env))
    ]
    [(Prim op es)
      (define-values (new-es sss)
        (for/lists (l1 l2) ([e es]) (rco-atom e)))
      (define key (gensym))
      (values (Var key) (append (append* sss) (list (list key (Prim op new-es)))))
    ]
    [(If e1 e2 e3)
      (define key (gensym))
      (values (Var key) (list (list key (If (rco-exp e1) (rco-exp e2) (rco-exp e3)))))
    ]
    [(SetBang v exp) 
      (define key (gensym))
      (values (Var key) (list (list key (SetBang v (rco-exp exp)))))
    ]
    [(Begin es exp)
      (define key (gensym))
      (values (Var key) (list (list key (Begin (for/list ([e es]) (rco-exp e)) (rco-exp exp)))))
    ]
    [(WhileLoop e1 e2)
      (define key (gensym))
      (values (Var key) (list (list key (WhileLoop (rco-exp e1) (rco-exp e2)))))
    ]
    [(Collect size)
      (define key (gensym))
      (values (Var key) (list (list key (Collect size))))
    ]
    [(Allocate amount type)
      (define key (gensym))
      (values (Var key) (list (list key (Allocate amount type))))
    ]
    [(GlobalValue name)
      (define key (gensym))
      (values (Var key) (list (list key (GlobalValue name))))
    ]
    [(Apply fun args)
      (define-values (new-args sss) (for/lists (l1 l2) ([a args]) (rco-atom a)))
      (define-values (new-fun funref-ss) (rco-atom fun))
      (define key (gensym))
      (values (Var key) (append (append funref-ss (append* sss)) (list (list key (Apply new-fun new-args)))))
    ]
    [(FunRef name arity)
      (define key (gensym))
      (values (Var key) (list (list key (FunRef name arity))))
    ]
    [_ (values e '())]
  )
)

(define (normalise-env-exp env exp)
  (match env
    ['() exp]
    [`(,(list key val) . ,rest-list)
      (Let key val (normalise-env-exp rest-list exp))
    ]
  )
)

(define (rco-exp e)
  (match e
    ; [(Int n) (Int n)]
    ; [(Var x) (Var x)]
    ; [(Bool b) (Bool b)]
    [(GetBang v) (Var v)]
    [(Let key val body) (Let key (rco-exp val) (rco-exp body))]
    [(Prim op es)
      (define-values (new-es sss) (for/lists (l1 l2) ([e es]) (rco-atom e)))
      (normalise-env-exp (append* sss) (Prim op new-es))
    ]
    [(If e1 e2 e3) (If (rco-exp e1) (rco-exp e2) (rco-exp e3))]
    [(SetBang v exp) (SetBang v (rco-exp exp))]
    [(Begin es exp) (Begin (for/list ([e es]) (rco-exp e)) (rco-exp exp))]
    [(WhileLoop e1 e2) (WhileLoop (rco-exp e1) (rco-exp e2))]
    [(Collect size) (Collect size)]
    [(Allocate amount type) (Allocate amount type)]
    [(GlobalValue name) (GlobalValue name)]
    [(Apply fun args)
      (define-values (new-args sss) (for/lists (l1 l2) ([a args]) (rco-atom a)))
      (define-values (new-fun funref-ss) (rco-atom fun))
      (normalise-env-exp (append (append* sss) funref-ss) (Apply new-fun new-args))
    ]
    [_ e]
  )
)

(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (match def [(Def a b c d exp) (Def a b c d (rco-exp exp))])))]
  )
)

;; Explicate Control
(define basic-blocks '())

(define (create-block tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
      (let ([label (gensym 'block)])
        (set! basic-blocks (cons (cons label tail) basic-blocks))
        (Goto label)
      )
    ]
  )
)

(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x)
      (define thn-goto (create-block thn))
      (define els-goto (create-block els))
      (IfStmt (Prim 'eq? (list cnd (Bool #t))) thn-goto els-goto)]
    [(Let x rhs body) (explicate-assign rhs x (explicate-pred body thn els))]
    [(Prim 'not (list e)) (explicate-pred e els thn)]
    [(Prim op es) #:when (member op (list 'eq? '< '<= '> '>= 'and 'or))
      (define thn-goto (create-block thn))
      (define els-goto (create-block els))
      (IfStmt (Prim op es) thn-goto els-goto)]
    [(Bool b) (if b thn els)]
    [(If cnd^ thn^ els^) 
      (define thn-goto (create-block thn))
      (define els-goto (create-block els))
      (explicate-pred cnd^ (explicate-pred thn^ thn-goto els-goto) (explicate-pred els^ thn-goto els-goto))]
    [(Begin es exp)
      (define thn-goto (create-block thn))
      (define els-goto (create-block els))
      (foldr explicate-effect (explicate-pred exp thn-goto els-goto) es)]
    [(Apply fun args)
      (define thn-goto (create-block thn))
      (define els-goto (create-block els))
      (IfStmt (Call fun args) thn-goto els-goto)
    ]
    [else (error "explicate_pred unhandled case" cnd)]
  )
)

(define (explicate-effect e cont) (match e
  ; [(Var x) cont]
  ; [(Int n) cont]
  ; [(Bool b) cont]
  ; [(Prim op es) cont]
  [(Prim 'read '()) (Seq e cont)]
  [(Collect size) (Seq e cont)]
  [(Let x rhs body) (explicate-effect rhs (explicate-effect body cont))]
  [(If e1 e2 e3) (explicate-effect e1 (explicate-effect e2 (explicate-effect e3 cont)))]
  [(SetBang v exp) (explicate-assign exp v cont)]
  [(Begin es exp) (foldr explicate-effect (explicate-effect exp cont) es)]
  [(WhileLoop cnd body) (define loop (gensym 'loop)) (define cnd-res (explicate-pred cnd (explicate-effect body (Goto loop)) cont)) (set! basic-blocks (cons (cons loop cnd-res) basic-blocks)) (Goto loop)]
  [(Allocate amount type) (Seq e cont)]
  [_ cont]
))

;; explicate-control : R1 -> C0
(define (explicate-tail e) (match e
  [(Void) (Return (Void))]
  [(Var x) (Return (Var x))]
  [(Int n) (Return (Int n))]
  [(Bool b) (Return (Bool b))]
  [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
  [(If e1 e2 e3) (explicate-pred e1 (explicate-tail e2) (explicate-tail e3))]
  [(Prim op es) (Return (Prim op es))]
  [(SetBang v exp) (explicate-effect e (Return (Void)))]
  [(Begin es exp) (foldr explicate-effect (explicate-tail exp) es)]
  [(WhileLoop cnd body) (explicate-effect e (Return (Void)))]
  [(Allocate amount type) (Return e)]
  [(GlobalValue lbl) (Return e)]
  [(Collect size) (explicate-effect e (Return (Void)))]
  [(Apply fun args) (TailCall fun args)]
  [(FunRef name arity) (Return (FunRef name arity))]
  [else (error "explicate-tail unhandled case" e)]
))

(define (explicate-assign e x cont) (match e
  [(Void) (Seq (Assign (Var x) (Void)) cont)]
  [(Var x_int) (Seq (Assign (Var x) (Var x_int)) cont)]
  [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
  [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
  [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
  [(If e1 e2 e3) (define cont-goto (create-block cont)) (explicate-pred e1 (explicate-assign e2 x cont-goto) (explicate-assign e3 x cont-goto))]
  [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
  [(SetBang v exp) (explicate-effect e (Seq (Assign (Var x) (Void)) cont))]
  [(Begin es exp) (foldr explicate-effect (explicate-assign exp x cont) es)]
  [(WhileLoop cnd body) (explicate-effect e (Seq (Assign (Var x) (Void)) cont))]
  [(Allocate amount type) (Seq (Assign (Var x) e) cont)]
  [(GlobalValue lbl) (Seq (Assign (Var x) e) cont)]
  [(Collect size) (explicate-effect e cont)]
  [(Apply fun args) (Seq (Assign (Var x) (Call fun args)) cont)]
  [(FunRef name arity) (Seq (Assign (Var x) (FunRef name arity)) cont)]
  [else (error "explicate-assign unhandled case" e)]
))

(define (explicate-function def) (set! basic-blocks '()) (match def
  [(Def fname fargs freturn info body) (Def fname fargs freturn info (append (list (cons (string->symbol (string-append (symbol->string fname) "start")) (explicate-tail body))) basic-blocks))]
))

(define (explicate-control p) (match p
  [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (explicate-function def)))]
))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions-atom atm) (match atm
  [(Int i) (Imm i)]
  [(Var v) (Var v)]
  [(Bool b) (if b (Imm 1) (Imm 0))]
  [(Void) (Imm 0)]
))

(define cmp-ops (list 'eq? '< '<= '> '>=))
(define cmp-cond (list (cons 'eq? 'e) (cons '< 'g) (cons '<= 'ge) (cons '> 'l) (cons '>= 'le)))
; (define cmp-cond (list (cons 'eq? 'e) (cons '< 'l) (cons '<= 'le) (cons '> 'g) (cons '>= 'ge)))

(define (list->number ls) (if (empty? ls) 0 
  (if (equal? 1 (car ls))
    (+ (list->number (cdr ls)) (expt 2 (length (cdr ls))))
    (list->number (cdr ls))
  )
))

(define (calculate-tag len type)
  (define type-bits (arithmetic-shift (list->number (for/list ([t type]) (if (and (list? t) (equal? (car t) 'Vector)) 1 0))) 7))
  (define len-bits (bitwise-ior (arithmetic-shift len 1) 1))
  (bitwise-ior type-bits len-bits)
)

(define (select-instructions-assign var exp) (match exp
  [(GlobalValue lbl) (list (Instr 'movq (list (Global lbl) var)))]
  [(Prim 'vector-ref (list tup n)) (list 
    (Instr 'movq (list (select-instructions-atom tup) (Reg 'r11))) 
    (Instr 'movq (list (Deref 'r11 (* 8 (+ (Int-value n) 1))) var))
  )]
  [(Prim 'vector-set! (list tup n rhs)) (list 
    (Instr 'movq (list (select-instructions-atom tup) (Reg 'r11))) 
    (Instr 'movq (list (select-instructions-atom rhs) (Deref 'r11 (* 8 (+ (Int-value n) 1)))))
    (Instr 'movq (list (Imm 0) var))
  )]
  [(Prim 'vector-length (list tup)) (list
    (Instr 'movq (list (select-instructions-atom tup) (Reg 'rax)))
    (Instr 'sarq (list (Imm 1) (Reg 'rax)))
    (Instr 'andq (list (Imm 63) (Reg 'rax)))
    (Instr 'movq (list (Reg 'rax) var))
  )]
  [(Allocate len type) (list
    (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
    (Instr 'addq (list (Imm (* 8 (+ len 1))) (Global 'free_ptr)))
    (Instr 'movq (list (Imm (calculate-tag len type)) (Deref 'r11 0)))
    (Instr 'movq (list (Reg 'r11) var))
  )]
  [(Prim 'not (list e)) (append (if (eq? (Var-name var) (Var-name e)) '() (list (Instr 'movq (list (select-instructions-atom e) var)))) (list (Instr 'xorq (list (Imm 1) var))))]
  [(Prim op (list e1 e2)) #:when (member op cmp-ops) (list 
    (Instr 'cmpq (list (select-instructions-atom e1) (select-instructions-atom e2))) 
    (Instr 'set (list (cdr (assoc op cmp-cond)) (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) var))
  )]
  [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) var)))]
  [(Prim '- (list e)) (list (Instr 'movq (list (select-instructions-atom e) var)) (Instr 'negq (list var)))]
  [(Prim op (list e1 e2)) (list (Instr 'movq (list (select-instructions-atom e1) var)) (Instr (if (equal? op '+) 'addq 'subq) (list (select-instructions-atom e2) var)))]
  [(FunRef name arity) (list (Instr 'leaq (list (Global name) var)))]
  [(Call fun args) (append (for/list ([arg args] [reg caller-saved]) (Instr 'movq (list (select-instructions-atom arg) reg))) (list (IndirectCallq fun (length args)) (Instr 'movq (list (Reg 'rax) var))))]
  [_ (list (Instr 'movq (list (select-instructions-atom exp) var)))]
))

(define (select-instructions-statement stmt conc-lbl) (match stmt
  [(Collect bytes) (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi))) (Instr 'movq (list (Imm bytes) (Reg 'rsi))) (Callq 'collect 2))]
  [(Prim 'vector-set! (list tup n rhs)) (list 
    (Instr 'movq (list (select-instructions-atom tup) (Reg 'r11))) 
    (Instr 'movq (list (select-instructions-atom rhs) (Deref 'r11 (* 8 (+ (Int-value n) 1)))))
  )]
  [(Goto lbl) (list (Jmp lbl))]
  [(Prim 'read '()) (list (Callq 'read_int 1))]
  [(IfStmt (Prim op (list e1 e2)) (Goto thn) (Goto els)) #:when (member op cmp-ops) (list (Instr 'cmpq (list (select-instructions-atom e1) (select-instructions-atom e2))) (JmpIf (cdr (assoc op cmp-cond)) thn) (Jmp els))]
  [(Return exp) (append (select-instructions-assign (Reg 'rax) exp) (list (Jmp conc-lbl)))]
  [(Assign var exp) (select-instructions-assign var exp)]
  [(Seq stmt cont) (append (select-instructions-statement stmt conc-lbl) (select-instructions-statement cont conc-lbl))]
  [(TailCall fun args) (append (for/list ([arg args] [reg caller-saved]) (Instr 'movq (list (select-instructions-atom arg) reg))) (list (TailJmp fun (length args))))]
))

(define (select-instructions-function def) (match def
  [(Def fname (list `[,xs : ,ts] ...) freturn info body)
    (Def fname '() 'Integer (dict-set info 'num-params (length xs)) (for/list ([func body]) (cons (car func) (Block '() (let ([instr (select-instructions-statement (cdr func) (string->symbol (string-append (symbol->string fname) "conclusion")))]) (if (equal? (car func) (string->symbol (string-append (symbol->string fname) "start"))) (append (for/list ([x xs] [reg caller-saved]) (Instr 'movq (list reg (Var x)))) instr) instr))))))
]))

(define (select-instructions p) (match p
  [(ProgramDefs info defs) (ProgramDefs (dict-set info 'num-root-spills 0) (for/list ([def defs]) (select-instructions-function def)))]
))

;; uncover-live : pseudo-x86 -> pseudo-x86
(define globalCFG (make-multigraph '()))

(define (clean-for-live-after vars) (list->set (for/list ([el vars] #:when (not (or (Imm? el) (Global? el) (Deref? el)))) el)))

(define caller-saved (list (Reg 'rdi) (Reg 'rsi) (Reg 'rdx) (Reg 'rcx) (Reg 'r8 ) (Reg 'r9 ) (Reg 'rax) (Reg 'r10) (Reg 'r11))) ;; Figure wtf is wrong with rax
(define callee-saved (list (Reg 'rsp) (Reg 'rbp) (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14) (Reg 'r15)))

(define (live-after-extract-writes exp) (match exp
  [(Instr 'movq es) (clean-for-live-after (cdr es))]
  [(Instr 'movzbq es) (clean-for-live-after (cdr es))]
  [(Instr 'addq es) (clean-for-live-after (cdr es))]
  [(Instr 'subq es) (clean-for-live-after (cdr es))]
  [(Instr 'xorq es) (clean-for-live-after (cdr es))]
  [(Instr 'negq es) (clean-for-live-after (list (car es)))]
  [(Callq lbl arity) (list->set caller-saved)]
  [(IndirectCallq lbl arity) (list->set caller-saved)]
  [_ (set)]
))

(define (live-after-extract-reads exp) (match exp
  [(Instr 'movq es) (clean-for-live-after (list (car es)))]
  [(Instr 'movzbq es) (clean-for-live-after (list (car es)))]
  [(Instr 'addq es) (clean-for-live-after es)]
  [(Instr 'subq es) (clean-for-live-after es)]
  [(Instr 'cmpq es) (clean-for-live-after es)]
  [(Instr 'xorq es) (clean-for-live-after es)]
  [(Instr 'negq es) (clean-for-live-after (list (car es)))]
  [(Callq lbl arity) (list->set (take callee-saved arity))]
  [(IndirectCallq lbl arity) (set-union (set lbl) (list->set (take callee-saved arity)))]
  [(TailJmp lbl arity) (set-union (set lbl) (list->set (take callee-saved arity)))]
  [_ (set)]
))

(define (process-single-block instr initial-live-after)
  ; (display instr)
  (if (null? instr) (list initial-live-after)
    (let ([live-afters (process-single-block (cdr instr) initial-live-after)]) (append (list (set-union (set-subtract (car live-afters) (live-after-extract-writes (car instr))) (live-after-extract-reads (car instr)))) live-afters))
))

(define (calculate-program-flow body) (for ([body-pair body])
  (for ([instr (Block-instr* (cdr body-pair))]) (match instr
    [(JmpIf cond new-lbl) (add-vertex! globalCFG new-lbl) (add-directed-edge! globalCFG (car body-pair) new-lbl) ]
    [(Jmp new-lbl) (add-vertex! globalCFG new-lbl) (add-directed-edge! globalCFG (car body-pair) new-lbl)]
    [_ '()]
  ))
))

(define (preprocess-live-after body fname)
  (add-vertex! globalCFG (string->symbol (string-append (symbol->string fname) "start")))
  (calculate-program-flow body)
  (define inverted-globalCFG (transpose globalCFG))
  (remove-vertex! inverted-globalCFG (string->symbol (string-append (symbol->string fname) "conclusion")))

  (define live-before-blocks (make-hash))
  (define live-afters-blocks (make-hash))
  (define process-queue (make-queue))
  (for ([v (get-vertices inverted-globalCFG)]) (hash-set! live-before-blocks v (set)) (enqueue! process-queue v))
  (hash-set! live-before-blocks 'conclusion (set (Reg 'rax) (Reg 'rsp)))

  (while (not (queue-empty? process-queue))
    ; (displayln (hash->list live-before-blocks))
    ; (displayln (queue->list process-queue))
    (define u (dequeue! process-queue))
    ; (displayln u)
    (define block-live-after (foldl set-union (set) (for/list ([v (get-neighbors globalCFG u)]) (hash-ref live-before-blocks v (set)))))
    ; (displayln block-live-after)
    (define live-afters (process-single-block (Block-instr* (cdr (assoc u body))) block-live-after))
    ; (displayln live-afters)
    (if (not (set=? (car live-afters) (hash-ref live-before-blocks u (set)))) (for ([v (get-neighbors inverted-globalCFG u)]) (enqueue! process-queue v)) null)
    (hash-set! live-before-blocks u (car live-afters))
    (hash-set! live-afters-blocks u (cdr live-afters))
    ; (displayln (hash-ref live-before-blocks u (set)))
    ; (display "\n")
  )

  (for/list ([func body]) (cons (car func) (match (cdr func) [(Block info bbody) (Block (list (if (hash-has-key? live-afters-blocks (car func)) (cons 'live-after (hash-ref live-afters-blocks (car func))) (cons 'no-process #t))) bbody)])))
)

(define (analyze-dataflow p) (match p
  [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (set! globalCFG (make-multigraph '())) (match def [(Def fname b c d body) (Def fname b c d (preprocess-live-after body fname))])))]
))


;;Build interference graph code
(define (remove-reg-class var) (if (Reg? var) (Reg-name var) var))
(define (add_edges instr inp_set conflicts)
  (define d_set (if (and (Instr? instr) (or (equal? (Instr-name instr) 'movq) (equal? (Instr-name instr) 'movzbq))) (clean-for-live-after (list (last (Instr-arg* instr)))) (live-after-extract-writes instr)))
  (define v_set (if (and (Instr? instr) (or (equal? (Instr-name instr) 'movq) (equal? (Instr-name instr) 'movzbq))) (set-subtract inp_set (clean-for-live-after (Instr-arg* instr))) (set-subtract inp_set d_set)))
  ; (display d_set) (display "  ") (display v_set) (display "\n")
  ; (for ([d d_set]) (for ([v v_set]) (add-edge! conflicts (remove-reg-class d) (remove-reg-class v))))
  (for ([d d_set]) (for ([v v_set]) (add-edge! conflicts d v)))
)

(define (traverse_list set_input instr conflicts) (if (empty? set_input) null (let ([_ (add_edges (car instr) (car set_input) conflicts)]) (traverse_list (cdr set_input) (cdr instr) conflicts))))

(define (compute-interference body conflicts)
  (for ([func body] #:when (not (assoc 'no-process (Block-info (cdr func))))) (traverse_list (cdr (assoc 'live-after (Block-info (cdr func)))) (Block-instr* (cdr func)) conflicts))
)

(define (compute-tuple-spill-interference vars conflicts)
  (for ([var-typ vars]) (if (and (list? (cdr var-typ)) (equal? (cadr var-typ) 'Vector)) (for ([reg callee-saved]) (add-edge! conflicts reg (Var (car var-typ)))) null))
)

(define (build-interference-func def conflicts) (match def
  [(Def a b c info body) (compute-interference body conflicts) (compute-tuple-spill-interference (dict-ref info 'locals-types) conflicts) (Def a b c (dict-set info 'conflicts conflicts) body)]
))

(define (build-interference p) (match p
  [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (define conflicts (undirected-graph '())) (add-vertex! conflicts (Reg 'rbp)) (build-interference-func def conflicts)))]
))

;; Variable Allocation
(define (color-graph graph vars var-types)
  (define all-registers (append caller-saved callee-saved))
  (define reg-idx-end (- (- (length all-registers)) 1))
  (define colors (make-hash (append (for/list ([reg all-registers] [idx (in-range -1 reg-idx-end -1)] #:when (has-vertex? graph reg)) (cons reg idx)) (list (cons (ByteReg 'al) reg-idx-end)))))
  (define available-regs (for/list ([reg all-registers] #:when (not (has-vertex? graph reg))) reg))
  (define nodes (make-hash))
  (define handles (make-hash))
  (define pnode>=? (lambda (x y) (>= (set-count (hash-ref nodes x)) (set-count (hash-ref nodes y)))))
  (define W (make-pqueue pnode>=?))

  (for ([u vars] #:when (Var? u)) (hash-set! nodes u (list->set (for/list ([v (get-neighbors graph u)] #:when (hash-has-key? colors v)) (hash-ref colors v)))))
  (for ([u (get-vertices graph)] #:when (not (hash-has-key? colors u))) (hash-set! handles u (pqueue-push! W u)))

  (while (not (eq? (pqueue-count W) 0))
    (define u (pqueue-pop! W))
    (define vcols (sort (set->list (hash-ref nodes u)) <))
    (define col-alloc (foldl (lambda (a res) (if (eq? res a) (+ res 1) res)) 0 vcols))
    (hash-set! colors u col-alloc)

    (for ([v (get-neighbors graph u)] #:when (not (hash-has-key? colors v)))
      (hash-set! nodes v (set-add (hash-ref nodes v) col-alloc))
    )
  )
  (define var-location (make-hash))
  (define stack-idx 0)
  (define hidden-stack-idx 0)
  (for ([cpair (hash->list colors)] #:when (Var? (car cpair))) (define var-name (Var-name (car cpair))) (hash-set! var-location var-name
    (if (and (list? (dict-ref var-types var-name)) (equal? (car (dict-ref var-types var-name)) 'Vector))
      (Deref 'r15 (begin (set! hidden-stack-idx (+ hidden-stack-idx 1)) (* 8 hidden-stack-idx)))
      (if (>= stack-idx (length available-regs)) (Deref 'rbp (begin (set! stack-idx (+ stack-idx 1)) (* 8 (- (- (length available-regs) stack-idx) 1)))) (begin (set! stack-idx (+ stack-idx 1)) (list-ref available-regs (- stack-idx 1))))
  )))
  var-location
)

(define (assign-homes-int stmt var-locs) (match stmt
  [(Var v) (hash-ref var-locs v)]
  [(Instr op args) (Instr op (for/list ([arg args]) (assign-homes-int arg var-locs)))]
  [(Block info body) (Block info (for/list ([stmt-int body]) (assign-homes-int stmt-int var-locs)))]
  [(TailJmp lbl arity) (TailJmp (assign-homes-int lbl var-locs) arity)]
  [exp exp]
))

(define (calculate-stack-space var-locs var-types) (let ([ret (apply + 
  (for/list ([vpair var-locs] #:when (not (and (list? (dict-ref var-types (car vpair))) (equal? (car (dict-ref var-types (car vpair))) 'Vector))))
    (if (Deref? (cdr vpair)) 8 0)))]) (+ ret (remainder ret 16))))

(define (calculate-hidden-stack-space var-locs var-types) (let ([ret (apply + 
  (for/list ([vpair var-locs] #:when (and (list? (dict-ref var-types (car vpair))) (equal? (car (dict-ref var-types (car vpair))) 'Vector)))
    (if (Deref? (cdr vpair)) 8 0)))]) (+ ret (remainder ret 16))))

(define (allocate-reg-func def) (match def
  [(Def a b c info body) 
    (define var-locs (let ([g (dict-ref info 'conflicts)]) (color-graph g (get-vertices g) (dict-ref info 'locals-types))))
    (define new-info (dict-set (dict-set (dict-set info 'stack-space (calculate-stack-space (hash->list var-locs) (dict-ref info 'locals-types))) 'rootstack-space (calculate-hidden-stack-space (hash->list var-locs) (dict-ref info 'locals-types))) 'available-regs (for/list ([var-pair (hash->list var-locs)] #:when (Reg? (cdr var-pair))) (cdr var-pair))))
    (Def a b c new-info (for/list ([func body]) (cons (car func) (assign-homes-int (cdr func) var-locs))))
]))
 
(define (allocate-registers p) (match p
  [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (allocate-reg-func def)))]
))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions-temp x86_body)
  (match x86_body
    [(Block info body) (Block info (patch-instructions-new body))]
    ))

(define (patch-instructions-new cmd-list)
  (cond [(empty? cmd-list) '()]
        [else (match (car cmd-list)
          [(Instr 'movq (list loc1 loc2)) #:when (equal? loc1 loc2) (patch-instructions-new (cdr cmd-list))]
          [(Instr 'movq (list (Global lbl) (Deref r i))) (append (list (Instr 'movq (list (Global lbl) (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref r i)))) (patch-instructions-new (cdr cmd-list)))]
          [(Instr 'movq (list (Deref reg1 int_1) (Deref reg2 int_2))) (append (list (Instr 'movq (list (Deref reg1 int_1) (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref reg2 int_2) ))) (patch-instructions-new (cdr cmd-list)))]
          [(Instr 'movzbq (list arg1 (Deref reg2 int_2))) (append (list (Instr 'movzbq (list arg1 (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref reg2 int_2)))) (patch-instructions-new (cdr cmd-list)))]
          [(Instr 'cmpq (list arg1 (Imm int_2))) (append (list (Instr 'movq (list (Imm int_2) (Reg 'rax))) (Instr 'cmpq (list arg1 (Reg 'rax))))(patch-instructions-new (cdr cmd-list)))]
          [(Instr 'cmpq (list (Deref reg1 int_1) (Deref reg2 int_2))) (append (list (Instr 'movq (list (Deref reg1 int_1) (Reg 'rax))) (Instr 'cmpq (list (Reg 'rax) (Deref reg2 int_2)))) (patch-instructions-new (cdr cmd-list)))]
          [(Instr 'addq (list (Deref reg1 int_1) (Deref reg2 int_2))) (append (list (Instr 'movq (list (Deref reg1 int_1) (Reg 'rax))) (Instr 'addq (list (Reg 'rax) (Deref reg2 int_2)))) (patch-instructions-new (cdr cmd-list)))]
          [(Instr 'subq (list (Deref reg1 int_1) (Deref reg2 int_2))) (append (list (Instr 'movq (list (Deref reg1 int_1) (Reg 'rax))) (Instr 'subq (list (Reg 'rax) (Deref reg2 int_2)))) (patch-instructions-new (cdr cmd-list)))]
          [(Instr 'leaq (list arg1 arg2)) #:when (not (Reg? arg2)) (append (list (Instr 'movq (list arg1 (Reg 'rax))) (Instr 'leaq (list (Reg 'rax) arg2))) (patch-instructions-new (cdr cmd-list)))]
          [(TailJmp lbl arity) (append (list (Instr 'movq (list lbl (Reg 'rax))) (TailJmp (Reg 'rax) arity)) (patch-instructions-new (cdr cmd-list)))]
          [_ (append (list (car cmd-list)) (patch-instructions-new (cdr cmd-list)))]
        )]))

(define (patch-instructions p) (match p
  [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (match def [(Def a b c d body) (Def a b c d (for/list ([func body]) (cons (car func) (patch-instructions-temp (cdr func)))))])))]
))


;; Prelude and Conclusion
(define (conclusion-instructions stack-space rootstack-space available-regs jmp-lbl) (append (list
  (Instr 'addq (list (Imm stack-space) (Reg 'rsp)))
) (for/list ([reg available-regs]) (Instr 'popq (list reg))) (list
  (Instr 'subq (list (Imm rootstack-space) (Reg 'r15)))
  (Instr 'popq (list (Reg 'rbp)))
  (if jmp-lbl (IndirectJmp jmp-lbl) (Retq))
)))

(define (main-instructions stack-space rootstack-space available-regs fname) (append (list
  (Instr 'pushq (list (Reg 'rbp)))
  (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
) (for/list ([reg available-regs]) (Instr 'pushq (list reg))) 
(list (Instr 'subq (list (Imm stack-space) (Reg 'rsp)))) 
(if (not (eq? fname 'main)) '() (list
  (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
  (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
  (Callq 'initialize 2)
  (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))
)) (list (Instr 'addq (list (Imm rootstack-space) (Reg 'r15))))
(for/list ([idx (in-range rootstack-space)]) (Instr 'movq (list (Imm 0) (Deref 'r15 idx))))
(list (Jmp (string->symbol (string-append (symbol->string fname) "start"))))))

(define (pnc-process-instr cmd-list stack-space rootstack-space available-regs)
  (cond [(empty? cmd-list) '()]
        [else (match (car cmd-list)
          [(TailJmp lbl arity) (append (conclusion-instructions stack-space rootstack-space available-regs lbl) (pnc-process-instr (cdr cmd-list) stack-space rootstack-space available-regs))]
          [_ (append (list (car cmd-list)) (pnc-process-instr (cdr cmd-list) stack-space rootstack-space available-regs))]
        )]))

(define (pnc-func fname info body)
  (define stack-space (dict-ref info 'stack-space))
  (define rootstack-space (dict-ref info 'rootstack-space))
  (define available-regs (dict-ref info 'available-regs))
  (append
    (list (cons fname (Block '() (main-instructions stack-space rootstack-space available-regs fname))))
    (for/list ([block-pair body]) (match (cdr block-pair) [(Block i instr) (cons (car block-pair) (Block i (pnc-process-instr instr stack-space rootstack-space available-regs)))]))
    (list (cons (string->symbol (string-append (symbol->string fname) "conclusion")) (Block '() (conclusion-instructions stack-space rootstack-space available-regs #f))))
))

; (define (prelude-and-conclusion p) (match p
;   [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (match def [(Def fname b c info body) (Def fname b c info (pnc-func fname info body))])))]))

(define (prelude-and-conclusion p) (match p
  [(ProgramDefs info defs) (X86Program info (append* (for/list ([def defs]) (match def [(Def fname b c info body) (pnc-func fname info body)]))))]))
                                     

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes `(
  ; ("partial evaluator", pe-Lint, interp-Lvar)
  ("shrink", shrink, interp-Lfun-prime, type-check-Lfun)
  ("uniquify" ,uniquify ,interp-Lfun-prime, type-check-Lfun)
  ("reveal functions", reveal-functions, interp-Lfun-prime, type-check-Lfun)
  ("limit functions", limit-functions, interp-Lfun-prime, type-check-Lfun)
  ("expose allocation", expose-allocation, interp-Lfun-prime, type-check-Lfun)
  ("uncover get!", uncover-get!, interp-Lfun-prime, type-check-Lfun)
  ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime, type-check-Lfun)
  ("explicate control" ,explicate-control ,interp-Cfun, type-check-Cfun)
  ("instruction selection" ,select-instructions ,interp-x86-3)
  ("analyze dataflow", analyze-dataflow, interp-x86-3)
  ("build interference", build-interference, interp-x86-3)
  ("allocate registers", allocate-registers, interp-x86-3)
  ("patch instructions" ,patch-instructions ,interp-x86-3)
  ("prelude-and-conclusion" ,prelude-and-conclusion, #f)
))

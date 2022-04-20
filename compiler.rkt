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
    [_ exp]))

(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (cadr (assoc x env)))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body) (
        let ([var_sampled (gensym x)])
        (Let var_sampled ((uniquify-exp (append (list (list x var_sampled)) env)) e) ((uniquify-exp (append (list (list x var_sampled)) env)) body))
      )]
      [(Prim op es) (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(If e1 e2 e3) (If ((uniquify-exp env) e1) ((uniquify-exp env) e2) ((uniquify-exp env) e3))]
      [(SetBang x exp) (SetBang (cadr (assoc x env)) ((uniquify-exp env) exp))]
      [(Begin es exp) (Begin (for/list ([e es]) ((uniquify-exp env) e)) ((uniquify-exp env) exp))]
      [(WhileLoop e1 e2) (WhileLoop ((uniquify-exp env) e1) ((uniquify-exp env) e2))]
      [(HasType exp type) (HasType ((uniquify-exp env) exp) type)]
    )
  )
)

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]
  )
)

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
  [_ exp]
))

(define (expose-allocation p) (match p
  [(Program info body) (Program info (expose-vec body))]
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
  [_ e]
))

(define (uncover-get! p) (match p [(Program info body) (Program info ((uncover-get!-exp (collect-set! body)) body))]))

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
      (define-values (new-es sss)
        (for/lists (l1 l2) ([e es]) (rco-atom e)))
      (normalise-env-exp (append* sss) (Prim op new-es))
    ]
    [(If e1 e2 e3) (If (rco-exp e1) (rco-exp e2) (rco-exp e3))]
    [(SetBang v exp) (SetBang v (rco-exp exp))]
    [(Begin es exp) (Begin (for/list ([e es]) (rco-exp e)) (rco-exp exp))]
    [(WhileLoop e1 e2) (WhileLoop (rco-exp e1) (rco-exp e2))]
    [(Collect size) (Collect size)]
    [(Allocate amount type) (Allocate amount type)]
    [(GlobalValue name) (GlobalValue name)]
    [_ e]
  )
)

(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]
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
    [else (error "explicate_pred unhandled case" cnd)]
  )
)

(define (explicate-effect e cont) (display e) (displayln cont) (match e
  ; [(Var x) cont]
  ; [(Int n) cont]
  ; [(Bool b) cont]
  ; [(Prim op es) cont]
  [(Prim 'read '()) (Seq e cont)]
  [(Let x rhs body) (explicate-effect rhs (explicate-effect body cont))]
  [(If e1 e2 e3) (explicate-effect e1 (explicate-effect e2 (explicate-effect e3 cont)))]
  [(SetBang v exp) (explicate-assign exp v cont)]
  [(Begin es exp) (foldr explicate-effect (explicate-effect exp cont) es)]
  [(WhileLoop cnd body) (define loop (gensym 'loop)) (define cnd-res (explicate-pred cnd (explicate-effect body (Goto loop)) cont)) (set! basic-blocks (cons (cons loop cnd-res) basic-blocks)) (Goto loop)]
  [_ cont]
))

;; explicate-control : R1 -> C0
(define (explicate-tail e) (displayln e) (match e
  [(Var x) (Return (Var x))]
  [(Int n) (Return (Int n))]
  [(Bool b) (Return (Bool b))]
  [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
  [(If e1 e2 e3) (explicate-pred e1 (explicate-tail e2) (explicate-tail e3))]
  [(Prim op es) (Return (Prim op es))]
  [(SetBang v exp) (explicate-effect e (Return (Void)))]
  [(Begin es exp) (foldr explicate-effect (explicate-tail exp) es)]
  [(WhileLoop cnd body) (explicate-effect e (Return (Void)))]
  [else (error "explicate-tail unhandled case" e)]
))

(define (explicate-assign e x cont) (match e
  [(Var x_int) (Seq (Assign (Var x) (Var x_int)) cont)]
  [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
  [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
  [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
  [(If e1 e2 e3) (define cont-goto (create-block cont)) (Seq (Assign (Var x) (explicate-pred e1 e2 e3)) cont-goto)]
  [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
  [(SetBang v exp) (explicate-effect e (Seq (Assign (Var x) (Void)) cont))]
  [(Begin es exp) (foldr explicate-effect (explicate-assign exp x cont) es)]
  [(WhileLoop cnd body) (explicate-effect e (Seq (Assign (Var x) (Void)) cont))]
  [else (error "explicate-assign unhandled case" e)]
))

(define (explicate-control p) (set! basic-blocks '()) (match p
  [(Program info body) (CProgram info (append (list (cons 'start (explicate-tail body))) basic-blocks))]
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

(define (select-instructions-assign var exp) (match exp
  [(Prim 'not (list e)) (append (if (eq? (Var-name var) (Var-name e)) '() (list (Instr 'movq (list (select-instructions-atom e) var)))) (list (Instr 'xorq (list (Imm 1) var))))]
  [(Prim op (list e1 e2)) #:when (member op cmp-ops) (list (Instr 'cmpq (list (select-instructions-atom e1) (select-instructions-atom e2))) (Instr 'set (list (cdr (assoc op cmp-cond)) (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) var)))]
  [(Prim 'read '()) (list (Callq 'read_int 1) (Instr 'movq (list (Reg 'rax) var)))]
  [(Prim '- (list e)) (list (Instr 'movq (list (select-instructions-atom e) var)) (Instr 'negq (list var)))]
  [(Prim op (list e1 e2)) (list (Instr 'movq (list (select-instructions-atom e1) var)) (Instr (if (equal? op '+) 'addq 'subq) (list (select-instructions-atom e2) var)))]
  [_ (list (Instr 'movq (list (select-instructions-atom exp) var)))]
))

(define (select-instructions-statement stmt) (match stmt
  [(Goto lbl) (list (Jmp lbl))]
  [(Prim 'read '()) (list (Callq 'read_int 1))]
  [(IfStmt (Prim op (list e1 e2)) (Goto thn) (Goto els)) #:when (member op cmp-ops) (list (Instr 'cmpq (list (select-instructions-atom e1) (select-instructions-atom e2))) (JmpIf (cdr (assoc op cmp-cond)) thn) (Jmp els))]
  [(Return exp) (append (select-instructions-assign (Reg 'rax) exp) (list (Jmp 'conclusion)))]
  [(Seq (Assign var exp) cont) (append (select-instructions-assign var exp) (select-instructions-statement cont))]
))

(define (select-instructions p) (match p
  [(CProgram info body) (X86Program info (for/list ([func body]) (cons (car func) (Block '() (select-instructions-statement (cdr func))))))]
))

;; uncover-live : pseudo-x86 -> pseudo-x86
(define globalCFG (make-multigraph '()))

(define (clean-for-live-after vars) (list->set (for/list ([el vars] #:when (not (Imm? el))) el)))

(define (live-after-extract-writes exp) (match exp
  [(Instr 'movq es) (clean-for-live-after (cdr es))]
  [(Instr 'movzbq es) (clean-for-live-after (cdr es))]
  [(Instr 'addq es) (clean-for-live-after (cdr es))]
  [(Instr 'subq es) (clean-for-live-after (cdr es))]
  [(Instr 'xorq es) (clean-for-live-after (cdr es))]
  [(Instr 'negq es) (clean-for-live-after (list (car es)))]
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
  ; [(JmpIf cond lbl) (cdr (assoc 'label->live (hash-ref lbl-data lbl)))]
  ; [(Jmp lbl) (cdr (assoc 'label->live (hash-ref lbl-data lbl)))]
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

(define (preprocess-live-after body)
  (add-vertex! globalCFG 'start)
  (calculate-program-flow body)
  (define inverted-globalCFG (transpose globalCFG))
  (remove-vertex! inverted-globalCFG 'conclusion)

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
  (displayln live-before-blocks)

  (for/list ([func body]) (cons (car func) (match (cdr func) [(Block info bbody) (Block (list (if (hash-has-key? live-afters-blocks (car func)) (cons 'live-after (hash-ref live-afters-blocks (car func))) (cons 'no-process #t))) bbody)])))
)

(define (analyze-dataflow p) (set! globalCFG (make-multigraph '())) (match p
  [(X86Program info body) (X86Program info (preprocess-live-after body))]
))


;;Build interferece graph code
(define conflicts (undirected-graph '()))

(define (remove-reg-class var) (if (Reg? var) (Reg-name var) var))
(define (add_edges instr inp_set)
  (define d_set (if (and (Instr? instr) (or (equal? (Instr-name instr) 'movq) (equal? (Instr-name instr) 'movzbq))) (set (last (Instr-arg* instr))) (live-after-extract-writes instr)))
  (define v_set (if (and (Instr? instr) (or (equal? (Instr-name instr) 'movq) (equal? (Instr-name instr) 'movzbq))) (set-subtract inp_set (clean-for-live-after (Instr-arg* instr))) (set-subtract inp_set d_set)))
  ; (display d_set) (display "  ") (display v_set) (display "\n")
  ; (for ([d d_set]) (for ([v v_set]) (add-edge! conflicts (remove-reg-class d) (remove-reg-class v))))
  (for ([d d_set]) (for ([v v_set]) (add-edge! conflicts d v)))
)

(define (traverse_list set_input instr) (if (empty? set_input) null (let ([_ (add_edges (car instr) (car set_input))]) (traverse_list (cdr set_input) (cdr instr)))))

(define (compute-interference body)
  (for ([func body] #:when (not (assoc 'no-process (Block-info (cdr func))))) (traverse_list (cdr (assoc 'live-after (Block-info (cdr func)))) (Block-instr* (cdr func))))
)

(define (build-interference p) (set! conflicts (undirected-graph '())) (match p
  [(X86Program info body) (compute-interference body) (X86Program (cons (cons 'conflicts conflicts) info) body)]
))

(define available-regs (list (Reg 'rcx)))

;; Variable Allocation
(define (color-graph graph vars)
  (define colors (make-hash (list (cons (Reg 'rax) -1) (cons (Reg 'rsp) -2))))
  (define nodes (make-hash))
  (define handles (make-hash))
  (define pnode>=? (lambda (x y) (>= (set-count (hash-ref nodes x)) (set-count (hash-ref nodes y)))))
  (define W (make-pqueue pnode>=?))

  (for ([u vars] #:when (not (Reg? u))) (hash-set! nodes u (list->set (for/list ([v (get-neighbors graph u)] #:when (hash-has-key? colors v)) (hash-ref colors v)))))
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
  (for ([cpair (hash->list colors)] #:when (not (Reg? (car cpair)))) (hash-set! var-location (Var-name (car cpair)) (if (< (cdr cpair) (length available-regs)) (list-ref available-regs (cdr cpair)) (Deref 'rbp (* 8 (- (- (length available-regs) (cdr cpair)) 1))))))
  var-location
)

(define (assign-homes-int stmt var-locs) (match stmt
  [(Var v) (displayln var-locs) (hash-ref var-locs v)]
  [(Instr op args) (Instr op (for/list ([arg args]) (assign-homes-int arg var-locs)))]
  [(Block info body) (Block info (for/list ([stmt-int body]) (assign-homes-int stmt-int var-locs)))]
  [exp exp]
))

(define (allocate-registers p) (match p
  [(X86Program info body) (let ([var-locs (let ([g (cdr (assoc 'conflicts info))]) (color-graph g (get-vertices g)))]) (X86Program info (for/list ([func body]) (cons (car func) (assign-homes-int (cdr func) var-locs)))))]
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
          [(Instr 'movzbq (list arg1 (Deref 'rbp int_2))) (append (list (Instr 'movzbq (list arg1 (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref 'rbp int_2)))) (patch-instructions-new (cdr cmd-list)))]
          [(Instr 'cmpq (list arg1 (Imm int_2))) (append (list (Instr 'movq (list (Imm int_2) (Reg 'rax))) (Instr 'cmpq (list arg1 (Reg 'rax))))(patch-instructions-new (cdr cmd-list)))]
          [(Instr 'cmpq (list (Deref 'rbp int_1) (Deref 'rbp int_2))) (append (list (Instr 'movq (list (Deref 'rbp int_1) (Reg 'rax))) (Instr 'cmpq (list (Reg 'rax) (Deref 'rbp int_2)))) (patch-instructions-new (cdr cmd-list)))]
          [_ (append (list (car cmd-list)) (patch-instructions-new (cdr cmd-list)))]
        )]))

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
  ("shrink", shrink, interp-Lvec-prime)
  ("uniquify" ,uniquify, interp-Lvec-prime)
  ("expose allocation", expose-allocation, interp-Lvec-prime)
  ("uncover get!", uncover-get!, interp-Lvec-prime)
  ("remove complex opera*" ,remove-complex-opera*, interp-Lvec-prime)
  ("explicate control" ,explicate-control, interp-Cvec)
  ; ("instruction selection" ,select-instructions ,interp-x86-1)
  ; ("analyze dataflow", analyze-dataflow, interp-x86-1)
  ; ("build interference", build-interference, interp-x86-1)
  ; ("allocate registers", allocate-registers, interp-x86-1)
  ; ("patch instructions" ,patch-instructions ,interp-x86-1)
  ; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
))

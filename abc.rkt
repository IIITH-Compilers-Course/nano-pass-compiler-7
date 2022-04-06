(define (color-graph interference-graph)
    (define all-vars (for/list ([node (filter Var? (get-vertices interference-graph))]) (match node [(Var x) x])))
    (define regs-in-graph (filter Reg? (get-vertices interference-graph)))

    ; initialising already assigned colors for each var
    (define already_assigned_colors (make-hash))
    (for ([var all-vars]) (dict-set! already_assigned_colors var '()))

    (for ([reg regs-in-graph])
        (for ([node (in-neighbors interference-graph reg)])
        (match node
            [(Var child_var)
            (dict-set! already_assigned_colors
                        child_var
                        (set-add (dict-ref already_assigned_colors child_var)
                                (dict-ref reg-to-num
                                        (match reg
                                            [(Reg r) r]))))]
                                            [_ #f])))
    
    (define pq (make-pqueue (lambda (a b) (> (length (dict-ref already_assigned_colors a)) (length (dict-ref already_assigned_colors b))))))

    (define node_references (make-hash))

    (for/list ([var all-vars])
        (define node_ref (pqueue-push! pq var))
        (dict-set! node_references var node_ref))

    (define result (make-hash))

    ; traverse priority queue
    (for ([i (pqueue-count pq)])
        (let ([var (pqueue-pop! pq)])
            (define cols (dict-ref already_assigned_colors var))
            (define assigned-color (get-min-color cols 0))

            (dict-set! result var assigned-color)
            (for ([node (in-neighbors interference-graph (Var var))])
                (match node
                    [(Var child_var) ; doing only for (Var something) struct
                    (dict-set! already_assigned_colors child_var (set-add (dict-ref already_assigned_colors child_var) assigned-color))
                    (pqueue-decrease-key! pq (dict-ref node_references child_var))]
                    [_ #f]
                )
            )
        )
    )

    result
)
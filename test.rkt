#lang racket                  
                              
(require "./priority_queue.rkt")
                              
(struct foo (name [val #:mutable]) #:methods gen:custom-write [(define (write-proc node port mode) (fprintf port "(foo ~a ~b)" (foo-name node) (foo-val node)))])
(define foo-<                 
  (lambda (foo1 foo2)         
    (< (foo-val foo1) (foo-val foo2))))                      
(define foo1 (foo "bus" 1))   
(define foo2 (foo "cycle" 2)) 
                              
(define q (make-pqueue foo-<))
(define node1 (pqueue-push! q foo1))
(define node2 (pqueue-push! q foo2))
(let ([popped (pqueue-pop! q)]) (display popped))
; Example of modifying a node               
(define node2^ (pqueue-push! q foo2))
(set-foo-val! foo2 -1)        
(pqueue-decrease-key! q node2^)
(let ([popped (pqueue-pop! q)]) (display popped))
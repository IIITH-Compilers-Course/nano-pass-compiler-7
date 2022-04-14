#lang racket

(let ([x2 10])
(let ([y3 0])
(+ (+ (begin
(set! y3 (read))
(get! x2))
(begin
(set! x2 (read))
(get! y3)))
(get! x2))))
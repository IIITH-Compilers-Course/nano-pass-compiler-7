#lang racket
(display (foldl (lambda (a res) (display a) (displayln res) (if (eq? res a) (+ res 1) res)) 0 (list -2 0 1)))
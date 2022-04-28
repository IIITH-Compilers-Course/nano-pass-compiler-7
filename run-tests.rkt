#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cif.rkt")
(require "interp-Lif.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "type-check-Lvec.rkt")
(require "interp-Cfun.rkt")
(require "interp-Lfun.rkt")
(require "type-check-Lfun.rkt")
(debug-level 1)
(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

; (interp-tests "var" #f compiler-passes interp-Lvar "var_test" (tests-for "var"))
; (interp-tests "vectors" type-check-Lvec compiler-passes interp-Lvec-prime "vectors_test" (tests-for "vectors"))
; (interp-tests "functions" type-check-Lfun compiler-passes interp-Lfun "functions_test" (tests-for "functions"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
; (compiler-tests "temp" #f compiler-passes "temp_test" (tests-for "temp"))
; (compiler-tests "vectors" type-check-Lvec compiler-passes "vectors_test" (tests-for "vectors"))
(compiler-tests "functions" type-check-Lfun compiler-passes "functions_test" (tests-for "functions"))


;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname interpreter) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
(require 2htdp/abstraction)


; =============================
; data definitions


(define-struct add [x y])
; an Add is a [Number Number]
; it represents two quantities to be added
#;
(define (fn-on-add z)
  (+ (add-x z)) (add-y z))


(define-struct multiply [x y])
; a Multiply is a [Number Number]
; it represents two quantities to be multiplied
#;
(define (fn-on-multiply z)
  (+ (multiply-x z)) (mulyiply-y z))


; a BSL-Expr is one of
;     - Number
;     - (make-add [BSL-Expr] [BSL-Expr])
;     - (make-multiply [BSL-Expr] [BSL-Expr])
#;
(define (fn-on-bslexpr be)
  (match be
    [(? number?) be]
    [(add x y) (+ (fn-on-bslexpr x) (fn-on-bslexpr y))]
    [(multiply x y) (* (fn-on-bslexpr x) (fn-on-bslexpr y))]))


; ===============================
; functions

(define (eval-expression be)
  ; BSL-Expr -> Number
  ; converts a BSL expression into a numeric quantity
  (match be
    [(? number?) be]
    [(add x y) (+ (eval-expression x) (eval-expression y))]
    [(multiply x y) (* (eval-expression x) (eval-expression y))]))


; ============================
; checks
(define test1 (make-add 7 3))
(define test2 (make-multiply 10 25))
(define quant (make-multiply (make-add 7 3) (make-add 33 -8)))

(check-expect (eval-expression test1) 10)
(check-expect (eval-expression test2) 250)
(check-expect (eval-expression quant) 250)

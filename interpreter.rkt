;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname interpreter) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
(require 2htdp/abstraction)


; =============================
; data definitions


(define-struct add [x y])
; an Add is a [Number Number]
; it represents two quantities to be added


(define-struct multiply [x y])
; a Multiply is a [Number Number]
; it represents two quantities to be multiplied


(define-struct nd [x y])
; an And is a [Number Number]
; it represents the logical "and" of two booleans


(define-struct r [x y])
; an Or is a [Number Number]
; it represents the logical "or" of two booleans


(define-struct nt [x])
; a Not is a [Number]
; it represents the logical "not" of a booleans


(define-struct func-defn [name param body])
; a FunctionDefinition is a [Symbol Symbol BSL-Expr]
; it defines a function and what it does to its parameters
#;
(define (fn-on-func-defn f)
  (... (fn-on-symbol (func-defn-name f))
       ... (fn-on-symbol (func-defn-param f))
       ... (fn-on-bslexpr (func-defn-body f))))


(define-struct func-app [name arg])
; a FunctionApplication is a [Symbol BSL-Expr]
; it represents the application of a function, embedded in an expression
#;
(define (fn-on-func-app f)
  (... (fn-on-symbol (func-app-name f))
       ... (fn-on-bslexpr (func-app-arg f))))


; a BSL-Expr is one of
;     - Number
;     - Symbol
;     - (make-add [BSL-Expr] [BSL-Expr])
;     - (make-multiply [BSL-Expr] [BSL-Expr])
;     - (make-function [Symbol Symbol BSL-Expr])
#;
(define (fn-on-bslexpr be)
  (match be
    [(? number?) be]
    [(? boolean?) be]
    [(? symbol?) be]
    [(add x y) (+ (fn-on-bslexpr x) (fn-on-bslexpr y))]
    [(multiply x y) (* (fn-on-bslexpr x) (fn-on-bslexpr y))]
    [(function name body) (fn-on-function be)]))


; a BSL-Bool-Expr is one of
;     - Boolean
;     - Symbol
;     - (make-and [BSL-Bool-Expr] [BSL-Bool-Expr])
;     - (make-or [BSL-Bool-Expr] [BSL-Bool-Expr])
;     - (make-not [BSL-Bool-Expr])
;     - (make-function [Symbol Symbol BSL-Bool-Expr])
#;
(define (fn-on-bslboolexpr be)
  (match bbe
    [(? boolean?) bbe]
    [(? symbol?) bbe]
    [(nd x y) (and (fn-on-bslboolexpr x) (fn-on-bslboolexpr y))]
    [(r x y) (or (fn-on-bslboolexpr x) (fn-on-bslboolexpr y))]
    [(nt x) (not (fn-on-bslboolexpr x))]))


; an Association is a (list Symbol Number)
; it represents a variables along with an associated numeric value
#;
(define (fn-on-association assoc)
  (... (fn-on-symbol (firstassoc)) ... (fn-on-number (second assoc))))


; ===============================
; functions


(define (parse sexpr)
  ; S-Expr -> BSL-Expr
  ; takes an S-expression and converts it into a BSL-expression
  (match sexpr
    [(? number?) sexpr]
    [(? boolean?) sexpr]
    [(? symbol?) sexpr]
    [(? string?) (error "no strings allowed")]
    [(list '+ x y) (make-add (parse x) (parse y))]
    [(list '* x y) (make-multiply (parse x) (parse y))]
    [(list 'and x y) (make-nd (parse x) (parse y))]
    [(list 'or x y) (make-r (parse x) (parse y))]
    [(list 'not x) (make-nt (parse x))]
    [(list (? symbol?) expr) (make-func-app (parse (first sexpr))
                                            (parse expr))]
    [(list (list (? symbol?) (? symbol?)) expr)
     (make-func-defn (parse (first (first sexpr)))
                     (parse (second (first sexpr))) (parse expr))]))


(define (eval-expression be)
  ; BSL-Expr -> Number
  ; converts a BSL expression into a numeric quantity
  (match be
    [(? number?) be]
    [(add x y) (+ (eval-expression x) (eval-expression y))]
    [(multiply x y) (* (eval-expression x) (eval-expression y))]))


(define (eval-bool-expr bbe)
  ; BSL-Bool-Expr -> Boolean
  ; converts a BSL expression into a boolean value
  (match bbe
    [(? boolean?) bbe]
    [(nd x y) (and (eval-bool-expr x) (eval-bool-expr y))]
    [(r x y) (or (eval-bool-expr x) (eval-bool-expr y))]
    [(nt x) (not (eval-bool-expr x))]))


(define (subst be sym val)
  ; BSL-Expr Symbol Number -> BSL-Expr
  ; replace all occurrences of symbol with value
  (match be
    [(? number?) be]
    [(? symbol?) (if (symbol=? sym be) val be)]
    [(add x y) (make-add (subst x sym val) (subst y sym val))]
    [(multiply x y) (make-multiply (subst x sym val) (subst y sym val))]))


(define (numeric? be)
  ; BSL-Expr -> Boolean
  ; determine if the given expression is fully numeric,
  ; i.e., if it is ready for evaluation
  (match be
    [(? number?) #t]
    [(? symbol?) #f]
    [(add x y) (and (numeric? x) (numeric? y))]
    [(multiply x y) (and (numeric? x) (numeric? y))]))


(define (eval-variable* be lassoc)
  ; BSL-Expr [ListOf Association] -> [Maybe Number]
  ; traverse the list of associations, making substitutions in
  ; the BST-Expression for each variable one by one
  (cond
    [(empty? lassoc)
     (if (numeric? be) (eval-expression be)
         (error "there's undefined variables in here"))]
    [else (eval-variable*
           (subst be (first (first lassoc)) (second (first lassoc)))
           (rest lassoc))]))


(define (eval-var-lookup be lassoc)
  ; BSL-Expr [ListOf Association] -> [Maybe Number]
  ; traverse the BST-Expression, making substitutions from the
  ; list of associations each time a variable is encountered
  (local (
          (define (assq be lassoc)
            (match be
              [(? number?) be]
              [(? symbol?)
               (local (
                       (define (in? assoc)
                         ; Association -> Boolean
                         (symbol=? (first assoc) be)))
                 ; - IN -
                 (if (ormap in? lassoc) (second (first (filter in? lassoc)))
                     (error "there's undefined variables in here")))]
              [(multiply x y) (make-multiply (assq x lassoc) (assq y lassoc))]
              [(add x y) (make-add (assq x lassoc) (assq y lassoc))])))
    ; - IN -
    (eval-expression (assq be lassoc))))


(define (eval-definition be repl)
  ; BSL-Expr BSL-Expr -> [Maybe Number]
  ; takes an expression of, or containing, a function along with
  ; the expression of that function itself and returns the result
  (match be
    [(multiply (? number?) (? number?)) (* (multiply-x be) (multiply-y be))]
    [(add (? number?) (? number?)) (+ (add-x be) (add-y be))]
    [(multiply x y) (if (or (symbol? x) (symbol? y))
                        be
                        (eval-definition
                                    (make-multiply
                                     (eval-definition x repl)
                                       (eval-definition y repl))
                                    repl))]
    [(add x y) (if (or (symbol? x) (symbol? y))
                        be
                        (eval-definition
                                    (make-add
                                     (eval-definition x repl)
                                       (eval-definition y repl))
                                    repl))]
    [(? func-app?)
     (if (symbol=? (func-defn-name repl) (func-app-name be))
         (eval-definition
          (subst (func-defn-body repl)
                 (func-defn-param repl)
                 (func-app-arg be))
          repl)
         (error "need a proper definition for this function"))]
    [stuff stuff]))



; ============================
; checks
(define test1 (make-add 7 3))
(define test2 (make-multiply 10 25))
(define quant (make-multiply (make-add 7 3) (make-add 33 -8)))
(define bool1 (make-nd #f #t))
(define bool2 (make-r #f #t))
(define bool3 (make-nt #f))
(define buant (make-r (make-nt (make-nd #t #t))
                      (make-nt (make-nd #f #t))))
(define symbi (make-multiply (make-add 'x 3) (make-add 33 'y)))
(check-expect (eval-expression test1) 10)
(check-expect (eval-expression test2) 250)
(check-expect (eval-expression quant) 250)
(check-expect (eval-bool-expr bool1) #f)
(check-expect (eval-bool-expr bool2) #t)
(check-expect (eval-bool-expr bool3) #t)
(check-expect (eval-bool-expr buant) #t)
(check-expect (parse '(+ 7 3)) test1)
(check-expect (parse '(* 10 25)) test2)
(check-expect (parse '(* (+ 7 3) (+ 33 -8))) quant)
(check-expect (parse '(and #f #t)) bool1)
(check-expect (parse '(or #f #t)) bool2)
(check-expect (parse '(not #f)) bool3)
(check-expect (parse '(or (not (and #t #t)) (not (and #f #t)))) buant)
(check-expect (parse '(+ x 4)) (make-add 'x 4))
(check-expect (numeric? symbi) #f)
(check-expect (numeric? (subst symbi 'x 7)) #f)
(check-expect (numeric? (subst (subst symbi 'x 7) 'y -8)) #t)
(check-expect (eval-variable* symbi '((x 7) (y -8))) 250)
(check-error (eval-variable* symbi '((x 7)))
             "there's undefined variables in here")
(check-expect (eval-var-lookup symbi '((x 7) (y -8))) 250)
(check-error (eval-var-lookup symbi '((x 7)))
             "there's undefined variables in here")
(check-expect (parse '((k x) (+ x 4))) (make-func-defn 'k 'x (make-add 'x 4)))
(check-expect (eval-definition (parse '(k 3)) (parse '((k x) x))) 3)
(check-expect (eval-definition (parse '(k 3)) (parse '((k x) (+ x 4)))) 7)
(check-expect (eval-definition (parse '(* 1 (k 3))) (parse '((k x) (+ x 4)))) 7)
(check-expect (eval-definition (parse '(* 5 (k 3)))
                               (parse '((k x) (+ x 4)))) 35)
(check-expect (eval-definition (parse '(* 5 (k (+ 1 2))))
                               (parse '((k x) (+ x 4)))) 35)
(check-error (eval-definition (parse '(* 5 (k (+ 1 2))))
                              (parse '((p x) (+ x 4))))
             "need a proper definition for this function")
#; (check-expect (eval-definition (parse '(* 5 (k (+ 1 2))))
                               (parse '((k x) (+ y 4))))
              (make-multiply 5 (make-add 'y 4)))
(check-expect (eval-definition (parse '(* (+ 7 3) (+ 33 -8)))
                               (parse '((k x) x))) 250)
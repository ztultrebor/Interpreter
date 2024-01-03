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


; a BSL-Expr is one of
;     - Number
;     - Boolean
;     - Symbol
;     - (make-add [BSL-Expr] [BSL-Expr])
;     - (make-multiply [BSL-Expr] [BSL-Expr])
;     - (make-and [BSL-Bool-Expr] [BSL-Bool-Expr])
;     - (make-or [BSL-Bool-Expr] [BSL-Bool-Expr])
;     - (make-not [BSL-Bool-Expr])
#;
(define (fn-on-bslexpr be)
  (match be
    [(? number?) be]
    [(? boolean?) be]
    [(? symbol?) be]
    [(add x y) (+ (fn-on-bslexpr x) (fn-on-bslexpr y))]
    [(multiply x y) (* (fn-on-bslexpr x) (fn-on-bslexpr y))]
    [(nd x y) (and (fn-on-bslexpr x) (fn-on-bslexpr y))]
    [(r x y) (or (fn-on-bslexpr x) (fn-on-bslexpr y))]
    [(nt x) (not (fn-on-bslexpr x))]))


; an Association is a (list Symbol Number)
; ir represents a variables along with an associated numeric value
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
    [(list 'not x) (make-nt (parse x))]))


(define (eval-expression be)
  ; BSL-Expr -> Number
  ; converts a BSL expression into a numeric quantity
  (match be
    [(? number?) be]
    [(add x y) (+ (eval-expression x) (eval-expression y))]
    [(multiply x y) (* (eval-expression x) (eval-expression y))]))


(define (eval-bool-expr bbe)
  ; BSL-Expr -> Boolean
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
              [(add x y)
               (make-add (eval-var-lookup x lassoc) (eval-var-lookup y lassoc))]
              [(multiply x y) (make-multiply (eval-var-lookup x lassoc)
                                             (eval-var-lookup y lassoc))])))
    ; - IN -
    (eval-expression (assq be lassoc))))


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
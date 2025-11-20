#lang racket
(require syntax/parse/define)
(require "utils.rkt")
(require "type.rkt")
(module+ test (require rackunit))

(provide (struct-out expr)
         (struct-out vbl) define-vbls with-vbls fresh-vbl
         (struct-out cnst)
         ap ap? ap-head ap-arg
         ab ab? ab-param ab-body
         eq =
         the the? the-param the-body
         type-of expr-of-type/c vbl-of-type/c term? wff?
         sig? sig-of expr-of-sig/c
         FV closed? sentence?
         occurs-in? occur-count
         subst0 subst1 subst1-ok?
         ⇔ ⊤ ⊥ ¬ ≠ ∧ ∨ ⇒ ∀ ∃ ∃! undef branch)

; Expressions
(struct expr () #:transparent #:property prop:procedure (λ (e1 . e2s) (apply ap e1 e2s)))

; Variables
(struct/contract vbl expr ([name symbol?] [type type?]) #:transparent)

(define-syntax-parse-rule (define-vbl ?name:id ?type:expr)
  (define ?name (vbl '?name ?type)))

(define-syntax-parse-rule (define-vbls [?names:id ?types:expr] ...)
  (begin
    (define-vbl ?names ?types)
    ...))

(define-syntax-parse-rule (with-vbls ([?names:id ?types:expr] ...) ?body)
  (let ([?names (vbl '?names ?types)] ...)
    ?body))

#| Finds a "fresh" variable, satisfying a supplied predicate, which has the same type as, and whose
name is based on, a supplied original variable. (The name will be that of the original variable plus,
potentially, a numeric suffix.) |#
(define/contract (fresh-vbl x pred) (-> vbl? (-> any/c boolean?) vbl?)
  (match-define (vbl name A) x)
  (let loop ([n 0])
    (let* ([suffix (if (zero? n) "" (number->string n))]
           [fresh-name (string->symbol (string-append (symbol->string name) suffix))]
           [y (vbl fresh-name A)])
      (if (pred y)
          y
          (loop (add1 n))))))

; Constants
(struct/contract cnst expr ([name symbol?] [type type?]) #:transparent)

; Applications
(struct ap0 expr (head arg type) #:transparent
  #:guard
  (λ (head arg type _)
    (check-arguments 'ap [head expr?] [arg expr?] [type #f])
    (match* ((type-of head) (type-of arg))
      [((→ A B) A) (values head arg B)]
      [((→ A _) B) (raise-arguments-error
                    'ap "ill-typed application; expected argument type does not match actual"
                    "expected" A "actual" B)]
      [(A _)       (raise-arguments-error
                    'ap "ill-typed application; head type is not a function type"
                    "head type" A)])))

(define ap? ap0?)
(define ap-head ap0-head)
(define ap-arg ap0-arg)

(define/contract (ap-proc e1 . e2s) (->* (expr?) () #:rest (listof expr?) expr?)
  (foldl (λ (arg head) (ap0 head arg #f)) e1 e2s))

(define-match-expander ap
  (syntax-parser [(_ ?e:expr)                #'(? expr? ?e)]
                 [(_ ?e1s:expr ... ?e2:expr) #'(ap0 (ap ?e1s ...) ?e2 _)])
  (syntax-parser [(_ ?es:expr ...)           #'(ap-proc ?es ...)]
                 [_                          #'ap-proc]))

(module+ test
  (with-vbls ([R (→ Ind Ind Prop)] [x Ind] [y Ind])
    (check-equal? (R x y) (ap (ap R x) y))))

; Abstractions
(struct ab0 expr (param body type) #:transparent
  #:guard
  (λ (param body type _)
    (check-arguments 'ab [param vbl?] [body expr?] [type #f])
    (values param body (→ (type-of param) (type-of body)))))

(define ab? ab0?)
(define ab-param ab0-param)
(define ab-body ab0-body)

(define/contract (ab-proc . args) (->* () () #:rest (*list/c vbl? expr?) expr?)
  (match-define (list xs ... e) args)
  (foldr (λ (x e) (ab0 x e #f)) e xs))

(define-match-expander ab
  (syntax-parser [(_ ?e:expr)                #'(? expr? ?e)]
                 [(_ ?x:expr ?args:expr ...) #'(ab0 ?x (ab ?args ...) _)])
  (syntax-parser [(_ ?args:expr ...)         #'(ab-proc ?args ...)]
                 [_                          #'ab-proc]))

(module+ test
  (with-vbls ([x Ind] [y Ind] [z Ind])
    (check-equal? (ab x y z) (ab x (ab y z)))))

; Equations
(struct eq expr (lhs rhs) #:transparent
  #:guard
  (λ (lhs rhs _)
    (check-arguments '= [lhs expr?] [rhs expr?])
    (let ([A (type-of lhs)] [B (type-of rhs)])
      (when (not (equal? A B))
        (raise-arguments-error
         '= "LHS and RHS have different types"
         "LHS type" A "RHS type" B)))
    (values lhs rhs)))

(define-match-expander =
  (syntax-parser [(_ ?e1:expr ?e2:expr) #'(eq ?e1 ?e2)])
  (syntax-parser [(_ ?e1:expr ?e2:expr) #'(eq ?e1 ?e2)]
                 [_                     #'eq]))

(module+ test
  (with-vbls ([x Ind] [y Ind])
    (check-equal? (= x y) (eq x y))))

; Definite descriptions
(struct the0 (param body type) #:transparent
  #:guard
  (λ (param body type _)
    (check-arguments 'the [param vbl?] [body wff?] [type #f])
    (values param body (type-of param))))

(define the? the0?)
(define the-param the0-param)
(define the-body the0-body)

(define (the-proc param body) (the0 param body #f))

(define-match-expander the
  (syntax-parser [(_ ?param:expr ?body:expr) #'(the0 ?param ?body _)])
  (syntax-parser [(_ ?param:expr ?body:expr) #'(the-proc ?param ?body)]
                 [_                          #'the-proc]))

; The type of an expression
(define/contract (type-of e) (-> expr? type?)
  (match e
    [(vbl _ A)    A]
    [(cnst _ A)   A]
    [(ap0 _ _ A)  A]
    [(ab0 _ _ A)  A]
    [(eq _ _)     Prop]
    [(the0 _ _ A) A]))

(define/contract (expr-of-type/c A) (-> type? (-> any/c boolean?))
  (λ (obj)
    (and (expr? obj) (equal? (type-of obj) A))))

(define/contract (vbl-of-type/c A) (-> type? (-> any/c boolean?))
  (and/c vbl? (expr-of-type/c A)))

; Terms
(define term? (expr-of-type/c Ind))

; Formulas
(define wff? (expr-of-type/c Prop))

; Signatures
(define sig? (set/c cnst?))

(define/contract (sig-of e) (-> expr? (set/c cnst?))
  (match e
    [(? vbl? _)                (set)]
    [(? cnst? a)               (set a)]
    [(or (ap e1 e2) (= e1 e2)) (set-union (sig-of e1) (sig-of e2))]
    [(or (ab x e) (the x e))   (sig-of e)]))

; Expressions over a particular signature
(define/contract (expr-of-sig/c σ) (-> sig? (-> any/c boolean?))
  (λ (obj) (and (expr? obj) (subset? (sig-of obj) σ))))

; Free variables
(define/contract (FV e) (-> expr? (set/c vbl?))
  (match e
    [(? vbl? x)                (set x)]
    [(? cnst? _)               (set)]
    [(or (ap e1 e2) (= e1 e2)) (set-union (FV e1) (FV e2))]
    [(or (ab x e) (the x e))   (set-remove (FV e) x)]))

(define/contract (free? x e) (-> vbl? expr? boolean?)
  (set-member? (FV e) x))

(define/contract (closed? e) (-> expr? boolean?)
  (set-empty? (FV e)))

(define sentence? (and/c wff? closed?))

#| Occurrence of a variable in an expression (whether free or bound, and including occurrence in
binders) |#
(define/contract (occurs-in? x e) (-> vbl? expr? boolean?)
  (match e
    [(== x)                      #t]
    [(? (or/c vbl? cnst?) _)     #f]
    [(or (ap e1 e2) (= e1 e2))   (or (occurs-in? x e1) (occurs-in? x e2))]
    [(or (ab y e) (the y e))     (or (equal? x y) (occurs-in? x e))]))

#| Number of occurrences of a variable in an expression (whether free or bound, but excluding
occurrences in binders |#
(define/contract (occur-count x e) (-> vbl? expr? natural?)
  (match e
    [(== x)                    1]
    [(? (or/c vbl? cnst?) _)   0]
    [(or (ap e1 e2) (= e1 e2)) (+ (occur-count x e1) (occur-count x e2))]
    [(or (ab y e) (the y e))   (occur-count x e)]))

#| Fully naïve substitution --- replacing all occurrences of a variable in an expression, whether they
be free or bound occurrences, although not including occurrences in binders |#
(define/contract (subst0 arg param body) (->i ([arg expr?]
                                               [param (arg) (vbl-of-type/c (type-of arg))]
                                               [body expr?])
                                              [result (body) (expr-of-type/c (type-of body))])
  (match body
    [(== param)              arg]
    [(? (or/c vbl? cnst?) _) body]
    [(ap e1 e2)              (ap (subst1 arg param e1) (subst1 arg param e2))]
    [(ab x e)                (ab x (subst1 arg param e))]
    [(the x e)               (the x (subst1 arg param e))]))

#| Somewhat naïve substitution --- replacing all free occurrences of a variable in an expression |#
(define/contract (subst1 arg param body) (->i ([arg expr?]
                                               [param (arg) (vbl-of-type/c (type-of arg))]
                                               [body expr?])
                                              [result (body) (expr-of-type/c (type-of body))])
  (match body
    [(== param)              arg]
    [(? (or/c vbl? cnst?) _) body]
    [(ap e1 e2)              (ap (subst1 arg param e1) (subst1 arg param e2))]
    [(ab (== param) _)       body]
    [(ab x e)                (ab x (subst1 arg param e))]
    [(the (== param) _)      body]
    [(the x e)               (the x (subst1 arg param e))]))

; Capture-avoidingness of a somewhat naïve substitution
(define/contract (subst1-ok? arg param body) (->i ([arg expr?]
                                               [param (arg) (vbl-of-type/c (type-of arg))]
                                               [body expr?])
                                              [result boolean?])
  (match body
    [(? (or/c vbl? cnst?) _)   #t]
    [(or (ap e1 e2) (= e1 e2)) (and (subst1-ok? arg param e1) (subst1-ok? arg param e2))]
    [(or (ab x e) (the x e))   (or (not (free? param body))
                                 (and (not (free? x arg)) (subst1-ok? arg param e)))]))

; Biconditionals (these are just equations where both sides are wffs)
(define/contract (⇔ φ ψ) (-> wff? wff? wff?)
  (= φ ψ))

(define-vbls [φ Prop] [f (→ Prop Prop Prop)])

; The always-true wff
(define ⊤ (= (ab φ φ) (ab φ φ)))

; The always-false wff
(define ⊥ (= (ab φ ⊤) (ab φ φ)))

; Negation
(define/contract (¬ φ) (-> wff? wff?)
  (⇔ φ ⊥))

(define/contract (≠ e1 e2) (-> expr? expr? wff?)
  (¬ (= e1 e2)))

; Conjunction
(define/contract (∧ φ ψ) (-> wff? wff? wff?)
  (= (ab f (f ⊤ ⊤)) (ab f (f φ ψ))))

; Disjunction
(define/contract (∨ φ ψ) (-> wff? wff? wff?)
  (¬ (∧ (¬ φ) (¬ ψ))))

; Conditionals
(define/contract (⇒ φ ψ) (-> wff? wff? wff?)
  (∨ (¬ φ) ψ))

; Universal quantification
(define/contract (∀ x φ) (-> vbl? wff? wff?)
  (= (ab x φ) (ab x ⊤)))

; Existential quantification
(define/contract (∃ x φ) (-> vbl? wff? wff?)
  (¬ (∀ x (¬ φ))))

; Uniqueness quantification
(define/contract (∃! x φ) (-> vbl? wff? wff?)
  (let ([y (fresh-vbl x (λ (y) (not (occurs-in? y φ))))])
    (∃ x (∧ φ (∀ y (⇒ (subst1 y x φ) (= y x)))))))

; Undefined values
(define/contract (undef A) (->i ([A type?]) [result (A) (expr-of-type/c A)])
  (define-vbl x A)
  (the x (≠ x x)))

; If-then-else
(define/contract (branch φ e1 e2) (->i ([φ wff?] [e1 expr?] [e2 (e1) (expr-of-type/c (type-of e1))])
                                       [result (e1) (expr-of-type/c (type-of e1))])
  (define A (type-of e1))
  (define-vbl x A)
  (let ([x (fresh-vbl x (λ (x) (not (or (occurs-in? x φ) (occurs-in? x e1) (occurs-in? x e2)))))])
    (the x (∧ (⇒ φ (= x e1)) (⇒ (¬ φ) (= x e2))))))
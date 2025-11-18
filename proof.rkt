#lang racket
(require racket/generic)
(require "utils.rkt")
(require "type.rkt")
(require "expr.rkt")

(struct proof () #:transparent)

#| The "Truth Values" axiom schema. It says that a property holds for both ⊤ and ⊥ iff it holds for
all propositional values. Thus, ⊤ and ⊥ are effectively the only two propositional values. |#
(struct prop-vals0 proof (P φ conc) #:transparent
  #:guard
  (λ (P φ conc _)
    (check-arguments 'prop-vals [P (vbl-of-type/c (→ Prop Prop))] [φ (vbl-of-type/c Prop)] [conc #f])
    (values P φ (∀ P (⇔ (∧ (P ⊤) (P ⊥)) (∀ φ (P φ)))))))

#| The "Leibniz's Law" axiom schema. It says that equal things have the same properties. |#
(struct leibniz0 proof (x y P conc) #:transparent
  #:guard
  (λ (x y P conc _)
    (check-arguments 'leibniz [x vbl?] [y vbl?] [P vbl?] [conc #f])
    (let ([A (type-of x)] [B (type-of y)] [C (type-of P)])
      (when (not (equal? A B))
        (raise-arguments-error
         'leibniz "x and y have different types"
         "x type" A "y type" B))
      (match C
        [(→ D (== Prop)) (raise-arguments-error
                          'leibniz "type of x and y doesn't match argument type of P"
                          "x and y type" A "argument type of P" D)]
        [_               (raise-arguments-error
                          'leibniz "P is not a predicate variable"
                          "P type" C)]))
    (values x y P (∀ x y (⇒ (= x y) (∀ P (⇔ (P x) (P y))))))))

#| The "Extensionality" axiom schema. It says that two functions of the same type are equal iff they
map each possible argument to the same value. |#
(struct ext0 proof (f g x conc) #:transparent
  #:guard
  (λ (f g x conc _)
    (check-arguments 'ext [f vbl?] [g vbl?] [x vbl?] [conc #f])
    (let ([A (type-of f)] [B (type-of g)])
      (when (not (equal? A B))
        (raise-arguments-error
         'ext "f and g have different types"
         "f type" A "g type" B)))
    (match-let ([(→ A B) (type-of f)])
      (let ([C (type-of x)])
        (when (not (equal? A C))
          (raise-arguments-error
           "argument type of f and g doesn't match type of x"
           "argument type of f and g" A "type of x" C))))
    (values f g x (∀ f g (⇔ (= f g) (∀ x (= (f x) (g x))))))))

#| The "Beta-Reduction" axiom schema. It says that the result of applying an abstraction λx.e to an
expression is equal to the result of substituting the expression in place of x in e, as long as the
substitution is capture-avoiding. |#
(struct βred0 proof (param body arg conc) #:transparent
  #:guard
  (λ (param body arg conc _)
    (check-arguments 'βred [param vbl?] [body expr?] [conc #f])
    (let ([A (type-of param)])
      (check-argument 'βred arg (expr-of-type/c A)))
    (when (not (subst1-ok? arg param body))
      (raise-arguments-error
       'βred "illegal substitution"
       "argument" arg "parameter" param "body" body))
    (values param body arg (= ((ab param body) arg) (subst1 arg param body)))))

#| The "Proper Definite Description" axiom schema. It says that if there is a unique thing with some
property then that property is satisfied by the corresponding entity determined via Definite
Description. |#
(struct proper-dd0 proof (x φ conc) #:transparent
  #:guard
  (λ (x φ conc _)
    (check-arguments 'proper-dd [x vbl?] [φ wff?] [conc #f])
    (when (not (subst1-ok? (the x φ) x φ))
      (raise-arguments-error
       'proper-dd "illegal substitution"
       "argument" (the x φ) "parameter" x "body" φ))
    (values x φ (⇒ (∃! x φ) (subst1 (the x φ) x φ)))))

#| The "Improper Definite Description" axiom schema. It says that if there isn't a unique thing with
some property then the corresponding entity determined via Definite Description is the error value for
the appropriate type. |#
(struct improper-dd0 proof (x φ conc) #:transparent
  #:guard
  (λ (x φ conc _)
    (check-arguments 'improper-dd [x vbl?] [φ wff?] [conc #f])
    (values x φ (⇒ (¬ (∃! x φ)) (= (the x φ) (undef (type-of x)))))))

#| The "Equality Substitution" rule of inference. If two expressions are equal, then we may replace
a single occurrence of one with the other in a wff φ, as long as the replaced expression is not a
variable within a binder.

To specify the occurrence to replace we make use of an auxiliary "template wff" ψ and variable x, such
that x occurs exactly once in ψ, and the result of substituting the first expression in place of x in
ψ is φ. The location of the variable within the template corresponds to the occurrence within φ that
we will replace. We can obtain the wff resulting from the replacement by substituting the second
expression in place of x in ψ. |#
(struct =s0 proof (π1 π2 ψ x conc) #:transparent
  #:guard
  (λ (π1 π2 ψ x conc _)
    (check-arguments '=s [π1 proof?] [π2 proof?] [ψ wff?] [conc #f])
    (define-values (e1 e2)
      (match (conc π1)
        [(= e1 e2) (values e1 e2)]
        [e         (raise-arguments-error
                    '=s "first premiss is not an equation"
                    "first premiss" e)]))
    (define A (type-of e1))
    (check-arguments '=s [x (vbl-of-type/c A)])
    (define φ (conc π2))
    (when (not (wff? φ))
      (raise-arguments-error
       '=s "second premiss is not a wff"
       "second premiss" φ))
    (let ([n (occur-count x ψ)])
      (when (not (=? n 1))
        (raise-arguments-error
         '=s "variable doesn't occur exactly once in template"
         "variable" x "template" ψ "number of occurrences" n)))
    (define ψe1 (subst0 e1 x ψ))
    (when (not (equal? φ ψe1))
      (raise-arguments-error
       '=s "second premiss doesn't match template"
       "second premiss" φ "template after substitution" ψe1))
    (values π1 π2 ψ x (subst0 e2 x ψ))))


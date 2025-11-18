#lang racket
(require syntax/parse/define)

#| Useful macros for struct guard procedures. |#
(provide check-argument check-arguments
         =?
         flip)

(define-syntax-parse-rule (check-argument ?type-name:expr ?val:expr ?pred:expr)
  #:with ?pred-string #'(format "~a" (syntax->datum #'?pred))
  (when (not ((and/c ?pred) ?val)) (raise-argument-error ?type-name ?pred-string ?val)))

(define-syntax-parse-rule (check-arguments ?type-name:expr [?vals:expr ?preds:expr] ...)
  (begin
    (check-argument ?type-name ?vals ?preds)
    ...))

#| Allows us to use =? for testing numeric equality, freeing = up to use for other purposes, e.g. as a
constructor of equations. |#
(define =? =)

(define (flip f) (λ (x y) (f y x)))
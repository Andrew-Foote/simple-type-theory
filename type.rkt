#lang racket
(require racket/generic)
(require syntax/parse/define)
(require "utils.rkt")
(module+ test (require rackunit))

(provide (struct-out type)
         Ind Prop
         (struct-out fun-type)
         → →decomp
         type-e)

(struct type () #:transparent
  #:methods gen:custom-write
  [(define/generic super-write-proc write-proc)
   (define (write-proc obj port mode)
     (super-write-proc (type-e obj) port #f))])

; The type of individuals
(define Ind (let () (struct ind-type type () #:transparent) (ind-type)))

; The type of truth values
(define Prop (let () (struct prop-type type () #:transparent) (prop-type)))

; Function types
(struct/contract fun-type type ([arg-type type?] [ret-type type?]) #:transparent)

(define/contract (→proc . args) (->* () () #:rest (non-empty-listof type?) type?)
  (match-define (list As ... B) args)
  (foldr fun-type B As))

(define-match-expander →
  (syntax-parser [(_ ?A:expr)              #'(? type? ?A)]
                 [(_ ?A:expr ?Bs:expr ...) #'(fun-type ?A (→ ?Bs ...))])
  (syntax-parser [(_ ?As:expr ...)         #'(→proc ?As ...)]
                 [_                        #'→proc]))

(module+ test
  (check-equal? (→ (→ Ind Prop) Ind Prop) (fun-type (fun-type Ind Prop) (fun-type Ind Prop))))

(define/contract (→decomp A) (-> type? (cons/c (listof type?) type?))
  (let loop ([As '()] [B A])
    (match B
      [(→ A B) (loop (cons A As) B)]
      [_       (cons (reverse As) B)])))

(module+ test
  (check-equal? (→decomp (→ (→ Ind Prop) Ind Prop)) (cons (list (→ Ind Prop) Ind) Prop)))

(define type-e?
  (flat-rec-contract
   type-e?
   'Ind 'Prop
   (cons/c '→ (cons/c type-e? (non-empty-listof type-e?)))))

(define/contract (type-e A) (-> type? type-e?)
  (match A
    [(== Ind)                  'Ind]
    [(== Prop)                 'Prop]
    [(app →decomp (cons As B)) `(→ ,@(map type-e As) ,(type-e B))]))

(module+ test
  (check-equal? (type-e (→ (→ Ind Prop) Ind Prop)) '(→ (→ Ind Prop) Ind Prop)))
; ---------------------------------  ESTO TRABAJO (es una primera parte)------------------------------
#lang play

(struct obj (class values))


(define Root
  (λ (msg . vals)
    (case msg
      [(lookup)     (error "method not found")]
      [(all-fields) '()] 
      [else (error "root class: should not happen: " msg)])))

(define (object x y)
 (let* ([scls Root]
         ;[fields (append (scls 'all-fields)
         ;                (list (cons 'f init) ...))]
         [fields x]
         [methods y
          #|(local [(defmac (? fd) #:captures self
                    (vector-ref (obj-values self)
                                (find-last 'fd fields)))
                  (defmac (! fd v) #:captures self
                    (vector-set! (obj-values self)
                                 (find-last 'fd fields)
                                 v))
                  (defmac (--> md . args) #:captures self
                    (((scls 'lookup 'md) self) . args))]
            (list (cons 'm (λ (self)
                            (λ params body))) ...)
            )|#
          ]
         )
    (letrec ([class (λ (msg . vals)
                      (case msg
                        [(all-fields) fields]
                        [(create)
                         (let ([values (list->vector (map cdr fields))])
                           (begin
                             (printf "~v " fields)
                             (obj class values)))]
                        #;[(read)
                           (vector-ref (obj-values (first vals))
                                       (find-last (second vals) fields))]
                        #;[(write)
                           (vector-set! (obj-values (first vals))
                                        (find-last (second vals) fields)
                                        (third vals))]
                        #;[(invoke)
                           (let ((method (class 'lookup (second vals))))
                             (apply (method (first vals)) (cddr vals)))]
                        [(lookup)
                         (let ([found (assoc (first vals) methods)])
                           (begin
                             (printf "~v " methods)
                           (if found
                               (cdr found)
                               (scls 'lookup (first vals)))))]))])
      class)))

#;(define (new class . init-vals)
  (apply class 'create init-vals))

(define (new c)
  (c 'create))


;; ---------------- pequeña variación -------------
(define (send o arg vals)
  (((obj-class o) 'lookup arg) vals))

(define a (object '((x .1)(y . 2)) (list (cons 'x? (lambda(y) (+ 1 y)))(cons 'x! (lambda(x)(+(+ 2 3) x))))))
(define b (new (object (list (cons 'x 1)(cons 'y 2)) (list (cons 'x? (lambda(y) (+ 1 y)))(cons 'x! (lambda(x)(+(+ 2 3) x)))))))
(send b 'x! 5)

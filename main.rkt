#lang play

#|
<expr> ::= <num>
         | <id>
         | <bool>
         | (if <expr> <expr> <expr>)
         | (+ <expr> <expr>)
         | '< <expr> <expr>)
         | (* <expr> <expr>)
         | (= <expr> <expr>)
         | (- <expr> <expr>)
         | (and <expr> <expr>)
         | (or <expr> <expr>)
         | (not <expr> <expr>)         
         | (seqn <expr> <expr>)
         | (local { <def>*} <expr>)

<def>    ::= (define <id> <expr>)


;EXTENSION PARA CLASE Y OBJETOS
<expr> ::= ... (expresiones del lenguage entregado) ...
        | (class <member>*)
        | (new <expr>)
        | (get <expr> <id>)
        | (set <expr> <id> <expr>)
        | (send <expr> <id> <expr>*)
        | this
        | (class <: <expr> <member>* )
        | (super <id> <expr>*
 
<member>  ::= (field <id> <expr>)
         | (method <id> (<id>*) <expr>)
|#


(struct obj (class values))

(define Object
  (λ (msg . vals)
    (case msg
      [(lookup)     (error "method not found")]
      [(all-fields) '()]
      [(root) #t]
      [else (error "root class: should not happen: " msg)])))





(deftype Expr
  (num n)
  (bool b)
  (id s)   
  (binop f l r)
  (unop f s)
  (my-if c tb fb)  
  (seqn expr1 expr2)  
  (lcal defs body)
  (class e)
  (field id val)
  (method id args expr)
  (send object method arg)
  (new expr)
  (get expr id)
  (set e1 id e2)
  (super m arg))

;; values
(deftype Val
  (numV n)
  (boolV b))

(deftype Def
  (my-def id expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Environment abstract data type
 
empty-env        :: Env
env-lookup       :: Sym Env -> Val
multi-extend-env :: List<Sym> List<Val> Env -> Env
extend-frame-env! :: Sym Val Env -> Env 


representation BNF:
<env> ::= (mtEnv)
        | (aEnv <id> <val> <env>)
|#

(deftype Env
  (mtEnv)
  (aEnv hash env)) 

(def empty-env (mtEnv))

#|
env-lookup:: Sym Env -> Val
Busca un símbolo en el ambiente, retornando su valor asociado.
|#
(define (env-lookup x env)
  (match env
    [(mtEnv) (error 'env-lookup "free identifier: ~a" x)]
    [(aEnv hash rest)
     (if (hash-has-key? hash x)
         (hash-ref hash x)
         (env-lookup x rest))]))

#|
multi-extend-env:: List(Sym) List(Expr) Env -> Env
Crea un nuevo ambiente asociando los símbolos a sus valores.
|#
(define (multi-extend-env ids exprs env)
  (if (= (length ids) (length exprs))
      (aEnv (make-hash (map cons ids exprs)) env)
      (error "wrong_input, mismatched lengths")))

#|
extend-frame-env!:: Sym Val Env -> Void
Agrega un nuevo par (Sym, Val) al ambiente usando mutación.
Este método no crea un nuevo ambiente.
|#
(define (extend-frame-env! id val env)
  (match env
    [(mtEnv) (aEnv (make-hash (list (cons id val))) env)]
    [(aEnv h rEnv) (let* ([l (hash->list h)]
                          [la (cons (cons id val) l)])
                     (set-aEnv-hash! env (make-hash la)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; parse :: s-expr -> Expr
(define (parse s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]    
    [(? boolean?) (bool s-expr)]
    [(list '* l r) (binop * (parse l) (parse r))]
    [(list '+ l r) (binop + (parse l) (parse r))]
    [(list '- l r) (binop - (parse l) (parse r))]
    [(list '< l r) (binop < (parse l) (parse r))]
    [(list '= l r) (binop = (parse l) (parse r))]    
    [(list 'or l r) (binop (λ (i d) (or i d)) (parse l) (parse r))]
    [(list 'and l r) (binop (λ (i d) (and i d)) (parse l) (parse r))]
    [(list 'not b) (unop not (parse b))]
    [(list 'if c t f) (my-if (parse c)
                             (parse t)
                             (parse f))]
    [(list 'seqn e1 e2) (seqn (parse e1) (parse e2))]    
    [(list 'local (list e ...)  b)
     (lcal (map parse-def e) (parse b))]
    [(list 'class e ...) (class (map parse e) )]
    ;[(list 'class '<: id e ...)(class id (map parse e))]
    [(list 'send e id b ... )(send (parse e) id (map parse b))]
    [(list 'new e)(new (parse e))]
    [(list 'field x v)(field x (parse v))]
    [(list 'method x arg b)(method x arg (parse b))]
    [(list 'get o x)(get (parse o) x)]
    [(list 'set o x v)(set (parse o) x (parse v))]
    [(list 'super m arg ...)(super m (map parse arg))]
    ))


;; parse-def :: s-expr -> Def
(define (parse-def s-expr)
  (match s-expr
    [(list 'define id b) (my-def id (parse b))]))

;; interp :: Expr Env -> Val
(define (interp expr env)
  (match expr
    [(num n) (numV n)]    
    [(bool b) (boolV b)]    
    [(binop f l r) (make-val (f (open-val (interp l env))
                                (open-val (interp r env))))]
    [(unop f s) (make-val (f (open-val (interp s env))))]
    [(my-if c t f)
     (def (boolV cnd) (interp c env))
     (if cnd
         (interp t env)
         (interp f env))]
    [(id x) (env-lookup x env)]        
    [(seqn expr1 expr2) (begin 
                          (interp expr1 env)
                          (interp expr2 env))]
    [(lcal defs body)
     (let* ([new-env (multi-extend-env '() '() env)])
       (for-each (λ(x)
                   (let ([in-def (interp-def x new-env)])
                     (extend-frame-env! (car in-def) (cdr in-def) new-env)
                     #t)) defs)       
       (interp body new-env))     
     ]
    [(class e)
     
       (let* ([scls (if(id? (car e))
                       (interp (cadr e) env)
                  Object)]
              ;[fields (append (scls 'all-fields)
              ;                (list (cons 'f init) ...))]
              [fields (append (scls 'all-fields)
                       (if (id? (car e))
                           (make-fields (cddr e) #t)
                           (make-fields e #t)))]
              [methods (make-fields e #f)
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
                                  (printf "FIELDS ~v~n " fields)
                                  (printf "VALUES ~v~n " values)
                                  ;(set! fields (append fields (list (cons 'this (obj class values)))))
                                  ;(printf "~v class root " (scls 'root))
                                  ;(printf "~v " fields)
                                  ;(printf "this ~v " (append fields (list (cons 'this (obj class values)))))
                                  (obj class values)))]
                             [(read)
                              (begin
                                (printf "Vals ~v~n" vals)
                                (printf "obj-values ~v~n" (obj-class (first vals)))
                                (vector-ref (obj-values (first vals))
                                            (find-last (second vals) fields)))]
                             [(write)
                                (vector-set! (obj-values (first vals))
                                             (find-last (second vals) fields)
                                             (third vals))]
                             #;[(invoke)
                                (let ((method (class 'lookup (second vals))))
                                  (apply (method (first vals)) (cddr vals)))]
                             [(super)
                              (scls 'lookup (first vals))]
                             [(lookup)
                              (let ([found (assoc (first vals) methods)])
                                (begin
                                  ;(printf "~v " methods)
                                  (if found
                                      (begin
                                       (printf "valuessss ~v~n " values)
                                      (cons (class 'create) (cdr found)))
                                      ;(cdr found)
                                      (scls 'lookup (first vals)))))]))])
           class))
     ]
    [(get o x)(let ([val ((obj-class (interp o env)) 'read (interp o env) x)])
                (if (num? val)
                    (interp val env)
                    val))]
    [(set o x val)((obj-class(interp o env)) 'write (interp o env) x (interp val env))]
    [(new expr)((interp expr env) 'create )]
    [(send o m arg)(let([object (interp o env)])
                     (begin
                       ;(printf "object ~v~n" object)
                       (def cl-body1 ((obj-class object) 'lookup m object))
                       ;(printf "bodyyy ~v~n" cl-body1)
                       (def cl-body ((cdr cl-body1)))
                       ;(printf "cl-body ~v~n" cl-body)
                       ;(printf "cl-body1 ~v~n" ((car cl-body1)))
                       ;(printf "~v ~n" (multi-extend-env (car cl-body) arg env))
                       ;(def cl-body (cadr cl-body1))
                       (interp (cdr cl-body)
                               (multi-extend-env '(this) (if (equal? ((obj-class (car cl-body1)) 'root) #t)
                                                             (list ((obj-class object) 'lookup m object))
                                                             (list (car cl-body1)))
                               (multi-extend-env (car cl-body) (map (lambda(x) (interp x env)) arg) env))) ;(multi-extend-env (car cl-body) arg env)
                       )
                     )]
    [(super m arg)(let ([object (interp (id 'this) env)])
                    (printf "super ~v~n " object)
                    (let ([cl-body1 ((obj-class object) 'super m object)])
                      (def cl-body ((cdr cl-body1)))
                      (interp (cdr cl-body) (multi-extend-env (car cl-body) (map (lambda(x) (interp x env)) arg) env)))
                    
                   )]
    ))

;; open-val :: Val -> Scheme Value
(define (open-val v)
  (match v
    [(numV n) n]
    [(boolV b) b]
    ))

;; make-val :: Scheme Value -> Val
(define (make-val v)
  (match v
    [(? number?) (numV v)]
    [(? boolean?) (boolV v)]
    ))

;; interp-def :: Def, Env -> Expr
(define (interp-def a-def env)
  (match a-def
    [(my-def id body) (cons id (interp body env))]))

;; run :: s-expr -> Val
(define (run s-expr)
  (interp (parse s-expr) empty-env))

#|
run-val:: s-expr -> Scheme-Val + Val
Versión alternativa de run, que retorna valores de scheme para primitivas y
valores de MiniScheme para clases y objetos
|#
(define (run-val s-expr)
  (define val (interp (parse s-expr) empty-env))
  (match val
    [(numV n) n]
    [(boolV b) b]
    [(num x) x]
    [x x]))


(define (find-last name alist [rcont -1] [cont 0])
  (match alist
    ['() (if (equal? rcont -1) (error "field not found:" name) rcont)]
    [(cons (cons f v) t) (if (equal? name f)
                             (find-last name t cont  (+ cont 1))
                             (find-last name t rcont (+ cont 1)))]))

(define (make-fields l parameter)
  (if(empty? l)
     '()
     (if parameter
         (if (field? (car l))
             (cons (cons (field-id (car l))(field-val (car l)))(make-fields (cdr l) parameter))
             (make-fields (cdr l) parameter))
         (if (method? (car l))
             (cons (cons (method-id (car l))(lambda () (cons (method-args (car l))(method-expr (car l)))))(make-fields (cdr l) parameter))
             (make-fields (cdr l) parameter)))
     ))

(define (my-append l new-values)
  (if (empty? l)
      new-values
      (cons (car l)(my-append (cdr l) new-values)))
  )
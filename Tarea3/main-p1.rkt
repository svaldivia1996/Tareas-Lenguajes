#lang play

#|
<expr> ::= <num>
         | <id>
         | <bool>
         | {if <expr> <expr> <expr>}
         | {+ <expr> <expr>}
         | {< <expr> <expr>}
         | {* <expr> <expr>}
         | {= <expr> <expr>}
         | {- <expr> <expr>}
         | {and <expr> <expr>}
         | {or <expr> <expr>}
         | {not <expr> <expr>}
         | {begin <expr> <expr>}
         | {with {<def>+} <expr>}

<def>    ::= {<id> <expr>}


;EXTENSION PARA CLASE Y OBJETOS
<expr> ::= ... (expresiones del lenguage entregado) ...
        | {class {<id>*} <method>*}
        | {new <expr> <expr>*}
        | {get <expr> <id>}
        | {set <id> <expr>}
        | {-> <expr> <id> <expr>*}
        | self
        | null

<method> ::= {def <id> {<id>*} <expr>}
|#


(deftype Expr
  (num n)
  (bool b)
  (id s)
  (binop f l r)
  (unop f s)
  (my-if c tb fb)
  (begn expr1 expr2)
  (with defs body)
  ;nuevas definicones de expr
  (class atributes) ;(class fields methods)
  (new cls args)
  (get e fieldname)
  (set fieldname mythis fieldexpr)
  (-> objexpr methodname argexpr)
  (self)
  (null)
  (field id expr) ; campo aux para inicializar nulls
  )

(deftype Def
  (my-def id expr))

;; values
(deftype Val
  (numV n)
  (boolV b)
  (classV env field-list methods-list);(classV env parent-class field-list methods-list) idea
  (objectV class-ref))

;; methods
(deftype Met
  (method name args expr))

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
                          [la (append l (list (cons id val)))])
                     (set-aEnv-hash! env (make-hash la)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; parse :: s-expr -> Expr
(define (parse s-expr [inner #f])
  (match s-expr

    [(? number?) (num s-expr)]
    [(? symbol?) (if (equal? 'self s-expr)
                     (if inner
                         (self)
                         (error "Parse error: self definition outside class"))
                     (if (equal? 'null s-expr)(null)(id s-expr)))]
    [(? boolean?) (bool s-expr)]
    [(list '* l r) (binop * (parse l inner) (parse r inner))]
    [(list '+ l r) (binop + (parse l inner) (parse r inner))]
    [(list '- l r) (binop - (parse l inner) (parse r inner))]
    [(list '< l r) (binop < (parse l inner) (parse r inner))]
    [(list '= l r) (binop = (parse l inner) (parse r inner))]
    [(list 'or l r) (binop (λ (i d) (or i d)) (parse l inner) (parse r inner))]
    [(list 'and l r) (binop (λ (i d) (and i d)) (parse l inner) (parse r inner))]
    [(list 'not b) (unop not (parse b inner))]
    [(list 'if c t f) (my-if (parse c inner)
                             (parse t inner)
                             (parse f inner))]
    [(list 'begin e1 e2) (begn (parse e1 inner) (parse e2 inner))]
    [(list 'with (list e ...)  b)
     (with (map parse-def e) (parse b inner))]
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;nuevo
    ;[(list 'null) (null)]
    [(list 'self) (if inner
                      (self)
                      (error "Parse error: self definition outside class"))]
    [(list 'class flds mtds ...)

     (define fparsed (map preparse flds))  ;(define fparsed (map parse-membs flds))
     (define memb (append fparsed mtds))
     (define mparsed (map parse-membs memb))
     (class mparsed)]
    [(list 'get obj fld-name) (get (parse obj inner) (parse fld-name inner))]
    [(list 'set 'self fld-name new-val)
     (set (self) (parse fld-name inner) (parse new-val inner))]
    [(list 'set obj new-val) (parse (list 'set 'self obj new-val))]
    [(list '-> obj m-id args ...) (-> (parse obj inner) m-id args)]
    [(list 'new class-id args) (new (parse class-id inner) args)]
    [(list 'new class-id) (new (parse class-id inner) '{})]

    ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Funciones Auxiliares;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; preparse :: sym -> s-expr
;;funcion de parser aux para definicion de metodos e inicializacion de args
(define (preparse id)
  (match id
    ;[(? symbol?) (cons 'field (cons id (cons (null) '())))]
    [(? symbol?) (list 'field id 'null)]
    ))


;; parse-membs :: s-expr -> Membs
;;funcion de parser aux para definicion de metodos e inicializacion de args
(define (parse-membs s-expr)
  (match s-expr
    [(list 'field id value) (field id (parse value))]
    [(list 'def name args exp) (method name args (parse exp #t))]
    [(? symbol?) (field s-expr (null))] ; inicializacion de campos en null
    ;['() (method 'init '() '())] ; si no hay metodos declarados se crea el metodo init por defecto con 0 args
    ))



;;init-field ::= List[field] env -> List[Pair]
;;Crea una lista de pares id box para los valores de los args de los objetos
(define (init-field field-list env)
  (match field-list
    ['() '()]
    [(cons (field id val) next) (def field-value (box (interp val env)))
                                (cons (cons id field-value) (init-field next env))]))

;;field-lookup ::= symbol List[Pair] -> box
;;Lookup de un field en un objeto
(define (field-lookup id fields)
  (match fields
    ['()(error "field not found")]
    [(cons (cons x val) next)
     (if (equal? id x)
         val
         (field-lookup id next))]))

;;method-lookup ::= symbol List[method] -> (cons method class) /error if not found
;;Lookup para encontrar el metodo de un objeto
(define (method-lookup id myclass)
  (def (classV class-env f-list method-list) myclass)
  (match method-list
    ['()('undefined (error "method not found"))]
    [(cons (method m-name m-args m-body) next)
     (if (equal? m-name id)
         (cons (method m-name m-args m-body) myclass)
         (method-lookup id (classV class-env f-list next)))]))

;; get-fields :: List[<ids>] -> Hash
;funcion que crea un hash a partir de una lista de fields seteando su valor por defecto a null
(define (get-fields defs)
  (define fields (make-hash))
  (for-each
   (λ(x)
     (match x
       [(id val)
        (hash-set! fields val (null))])) defs)
  fields)


;; get-methods :: List[Membs] -> Hash
;funcion que crea un hash a partir de una lista de metodos
(define (get-methods defs)
  (define methods (make-hash))
  (for-each
   (λ(x)
     (match x
       [(method n a b)
        (define h (make-hash (list (cons 'args a) (cons 'body b))))
        (hash-set! methods n h)])) defs)
  methods)



;; parse-def :: s-expr -> Def
(define (parse-def s-expr)
  (match s-expr
    [(list id b) (my-def id (parse b))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; inicio de funciones auxiliares no usadas;;;;;;;;;;;;;;;;;

#|
;; get-fieldsMalo :: List[<ids>] -> Hash
;Crea un hash a partir de una lista de fields seteando su valor por defecto a null
(define (get-fieldsMalo defs)
  (define fields (make-hash))
  (for-each
   (λ(x)
     (match x
       [(id val)
        (hash-set! fields val (null))])) defs)
  fields)
;; get-methodsMalo :: List[Membs] -> Hash
;funcion que crea un hash a partir de una lista de metodos
(define (get-methodsMalo defs)
  (define methods (make-hash))
  (for-each
   (λ(x)
     (match x
       [(method n a b)
        (define h (make-hash (list (cons 'args a) (cons 'body b))))
        (hash-set! methods n h)])) defs)
  methods)

;; getFieldFromClass :: Hash x Symbol -> Hash/#f/error
;; emcuentra el valor id de la clase c
(define (getFieldFromClass c id)
  (define fld (hash-ref (hash-ref c 'fields) id #f) )
  (match fld
    ;[#f (error "getFieldFromClass: field not found exception")]
    [(null) (error "getFieldFromClass: field not found exception")]
    [_ fld]
  )
  )
  ;(error getFieldFromClass "field not found")(hash-ref (hash-ref o 'fields) id #f)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;interp;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; definicion de object
(define object-class (class '()))
;; interp :: Expr Env -> Val
(define (interp expr env [insideClass #f])
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
    [(begn expr1 expr2) (begin
                          (interp expr1 env)
                          (interp expr2 env))]
    [(with defs body)
     (let* ([new-env (multi-extend-env '() '() env)])
       (for-each (λ(x)
                   (let ([in-def (interp-def x new-env)])
                     (extend-frame-env! (car in-def) (cdr in-def) new-env)
                     #t)) defs)
       (interp body new-env))
     ]
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;Nuevo
    [(null) (null)]
    [(class members)
     (if (equal? '() members)
         (classV empty-env 'undefined '() '())
         (classV env (init-field (filter field? members) env) (filter method? members)))]
    [(new e args) (def (classV obj-env field-list method-list) (interp e env))
                  (def mythis (box 'undefined))
                  (begin
                    (extend-frame-env! 'self mythis obj-env)
                    (def object-created (objectV (classV obj-env  field-list method-list)))
                    (begin
                      (set-box! mythis object-created)
                      object-created))]
    [(self) (unbox (env-lookup 'self env))]

    [(get e field)
     (def (objectV  (classV obj-env  field-list method-list)) (interp e env))
     (def (id x) field)
     (match e
       [(self) (def (classV _  f-list _) (env-lookup 'this-class env))
               (unbox (field-lookup x f-list ))]
       [ _ (unbox (field-lookup x field-list ))])]

    [(set e field-id v)
     (def (objectV (classV obj-env  field-list method-list)) (interp e env))
     (def (id x) field-id)
     (def new-val (interp v env))
     (match e
       [(self) (def (classV _ f-list m-list) (env-lookup 'this-class env))
               (def exists (field-lookup x f-list))
               (set-box! exists new-val)]
       [_ (def exists (field-lookup x field-list ))
          (set-box! exists new-val)])]

    [(-> e method-name args)
     (def (objectV (classV obj-env field-list method-list)) (interp e env))
     (def (cons (method _ m-args m-body) (classV s-env  m-fields m-list)) (method-lookup method-name (classV obj-env field-list method-list)))
     (def m-env (multi-extend-env m-args (map (lambda (x) (interp x env)) (map parse args)) obj-env))
     (begin
       (extend-frame-env! 'this-class (classV m-env  m-fields m-list) m-env)
       (interp m-body m-env))]



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
    [x x]))








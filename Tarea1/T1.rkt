#lang play
(print-only-errors)





#|
<prog> ::= {<fundef>* <expr>}
|#
(deftype Prog
  (prog funLst prog-body))

#|
<type> ::= Num | Bool | {Pair <type> <type>}
|#
(deftype type
    (num)
    (bool)
    (pair t1 t2)
    )

#|
<arg> ::= {<id> : <type>}
|#
(deftype Arg
    (arg id type)
    )    

 
#| 
<fundef> ::= {define {<id> <id>*}  <expr>} pasa a ser por P2 <fundef> ::= {define {<id> <arg>*} [: <type>] <expr>} 
|#
(deftype FunDef
  (fundef name paramlst fundef-body))


; lookup-fundef : Sym List[FunDef] -> FunDef (o error)
;busca la definicion de funcion en una lista de definiciones
(define (lookup-fundef name fundefs)
  (match fundefs
    ['() (error "undefined function:" name)]
    [(cons fd fds)
     (if (equal? name (fundef-name fd))
         fd
         (lookup-fundef name fds))]))


#| 
<expr>   ::= <num>
           | <id>
           | <bool>
           | {cons <expr> <expr>}
           | {+ <expr> <expr>}
           | {< <expr> <expr>}
           | {= <expr> <expr>}
           | {fst <expr>}
           | {snd <expr>}
           | {if <expr> <expr> <expr>}
           | {with {{<id> <expr>}*} <expr>} a partir de P2 {with { {<id> [: <type>] <expr>}* } <expr>}
           | {<id> <expr>*}
Estructura que define una expresion de sintaxis abstracta
|#
(deftype Expr
    (Num n)
    (Id x)
    (Bool b)
    (Cons h t)
    (Add l r)
    (Less l r)
    (Equals l r)
    (Fst lst)
    (Snd lst)
    (If testExpr trueExpr falseExpr)
    (With x e b)
    (App f expr)
    ;(Define fun-name fun-args expr)
    )



; parse : Src -> Expr
;transforma sintaxis concreta a a sintaxis abstracta
(define (parse src)
    (match src
        [(? number?) (Num src)]
        [(? symbol?) (Id src)]
        [(? boolean?) (Bool src)]
        [(list 'cons h t) (Cons (parse h) (parse t))]
        [(list '+ s1 s2) (Add (parse s1) (parse s2))]
        [(list '< s1 s2) (Less (parse s1) (parse s2))]
        [(list '= s1 s2) (Equals (parse s1) (parse s2))]
        [(list 'fst lst) (Fst (parse lst))]
        [(list 'snd lst) (Snd (parse lst))]
        [(list 'if e t f) (If (parse e) (parse t) (parse f))]
        [(list 'with (list def) body) #:when (symbol? body) (With (car def) (parse (second def)) (parse body))]   
        [(list 'with (list def) body) (if (= 1 (length body)) (With (car def) (parse (second def)) (parse (car body))) (With (car def) (parse (second def)) (parse body)))]
        [(list 'with (list def1 rest  ...) body)  (With (car def1) (parse (second def1)) (parse (list 'with rest body)))]
        [(list f e) #:when (symbol? f) (App f (parse e))]
        ;[(list 'define (cons h t) e) (Define (parse h) (map parse t) (parse e))] 
        [(list 'define (cons h t) e) (fundef h t (parse e))]


    )
)


(test (parse 10) (Num 10))
(test (parse 'x) (Id 'x))
(test (parse #t) (Bool #t))
(test (parse #f) (Bool #f))
(test (parse '{cons 10 20}) (Cons (Num 10) (Num 20)))
(test (parse '{cons #t 20}) (Cons (Bool #t) (Num 20)))
(test (parse '{cons 1 #f}) (Cons (Num 1) (Bool #f)))
(test (parse '{cons #t #f}) (Cons (Bool #t) (Bool #f)))
(test (parse '{cons 1 {cons 2 3}}) (Cons (Num 1) (Cons (Num 2) (Num 3))))
(test (parse '{+ 1 3}) (Add (Num 1) (Num 3)))
(test (parse '{< 4 9}) (Less (Num 4) (Num 9)))
(test (parse '{= 2 7}) (Equals (Num 2) (Num 7)))
(test (parse '{fst {cons 1 2}}) (Fst (Cons (Num 1) (Num 2))))
(test (parse '{snd {cons 1 2}}) (Snd (Cons (Num 1) (Num 2))))
(test (parse '{if {< 4 9} 1 0}) (If (Less (Num 4) (Num 9)) (Num 1) (Num 0)))
(test (parse '{if #t 1 0}) (If (Bool #t) (Num 1) (Num 0)))
(test (parse '{if cond true false}) (If (Id 'cond) (Id 'true) (Id 'false)))
(test (parse '{with {{x 10}} {+ y z}}) (With 'x (Num 10) (Add (Id 'y) (Id 'z))))
(test (parse '{with {{x 3} {y 8}} {z}}) (With 'x (Num 3) (With 'y (Num 8) (Id 'z))))
(test (parse '{define {add2 x} {+ 2 x}}) (fundef 'add2 (list 'x) (Add (Num 2) (Id 'x))));parseo de definicion de funciones una arg
(test (parse '{define {sum x y z} {+ x {+ y z}}}) (fundef 'sum (list 'x 'y 'z) (Add (Id 'x) (Add (Id 'y) (Id 'z)))));parseo de definicion de funciones mult args




;; abstract data type env
#|
nombre de un tipo: Env
funciones sobre el tipo:
- empty-env : Env
- extend-env : Id Val Env -> Env
- lookup-env : Id Env -> Val
|#
(deftype Env
  (mtEnv)
  (aEnv id val env))

(define empty-env mtEnv)
(define extend-env aEnv)

(define (lookup-env x env)
  (match env
    [(mtEnv) (error "free identifier:" x)]
    [(aEnv y v rest)
     (if (equal? y x)
         v
         (lookup-env x rest))]))

; typecheck: Expr -> Type (o error)
;Recibe una expresion parseada y retorna type de lo que retorna o un error
(define (typecheck expr)
  (match expr
    [(Num n) (num)]
    [(Bool b) (bool)]
    [(Cons l r) (pair (typecheck l) (typecheck r))]
    [(Add l r) (let ([tl (typecheck l)]
                     [tr (typecheck r)])
                 (if (and (num? tl) (num? tr))
                     (num)
                     (if (or (bool? tl) (bool? tr));(error "Static type error: expected Num found otra cosa")
                      (error "Static type error: expected Num found Bool")
                      (error "Static type error: expected Num found Pair")
                     )
                  ))]
    [(Less l r) (let ([tl (typecheck l)]
                     [tr (typecheck r)])
                 (if (and (num? tl) (num? tr))
                     (bool) ;hice la suposicion de que typecheck retorna el tipo de la funcion aplicada en este caso (less) recibe num num -> bool
                     (if (or (bool? tl) (bool? tr));(error "Static type error: expected Num found otra cosa")
                      (error "Static type error: expected Num found Bool")
                      (error "Static type error: expected Num found Pair")
                     )
                  ))]
    [(Equals l r) (typecheck (Less l r))] ; en el arbol es equivalente al (less) ya que tiene que debe verificar num num -> bool

    [(Fst (Cons h t)) (typecheck h)]
    [(Fst lst) #:when (Num? lst) (error "Static type error: expected Pair found Num")]
    [(Fst lst) #:when (Bool? lst) (error "Static type error: expected Pair found Bool")]

    [(Snd (Cons h t)) (typecheck h)]
    [(Snd lst) #:when (Num? lst) (error "Static type error: expected Pair found Num")]
    [(Snd lst) #:when (Bool? lst) (error "Static type error: expected Pair found Bool")]

    [(If c t f) (let ([tc (typecheck c)]
                      [tt (typecheck t)]
                      [tf (typecheck f)])   
                 (match tc
                  [(num) (error "Static type error: expected Bool found Num")]
                  [(pair l r) (error "Static type error: expected Bool found Pair")]
                  [(bool) (if (equal? tt tf)
                    tt
                    ;(error "Static type error: expected" tt "found" tf)
                    (match tt
                      [(num) (if (equal? tf (bool)) (error "Static type error: expected Num found Bool") (error "Static type error: expected Num found Pair"))]
                      [(bool) (if (equal? tf (num)) (error "Static type error: expected Bool found Num") (error "Static type error: expected Bool found Pair"))]
                      [(pair l r) (if (equal? tf (num)) (error "Static type error: expected Pair found Num") (error "Static type error: expected Pair found Bool"))]
                    )
                  )]
                 )
                )
    ]
    
  ))



;Casos Bases
(test (typecheck (parse 10)) (num))
(test (typecheck (parse #t)) (bool))
(test (typecheck (parse #f)) (bool))
(test (typecheck (parse '{cons 1 2})) (pair (num) (num)))
(test (typecheck (parse '{cons 1 #t})) (pair (num) (bool)))
(test (typecheck (parse '{cons #t 1})) (pair (bool) (num)))
(test (typecheck (parse '{cons #t #f})) (pair (bool) (bool)))
(test (typecheck (parse '{+ 10 3})) (num))
(test (typecheck (parse '{+ 10 {+ 2 4}})) (num))
(test (typecheck (parse '{< 8 2})) (bool))
(test (typecheck (parse '{< 2 {+ 2 3}})) (bool))
(test (typecheck (parse '{= 2 2})) (bool))
(test (typecheck (parse '{= 12 23})) (bool))
(test (typecheck (parse '{fst {cons 1 2}})) (num))
(test (typecheck (parse '{fst {cons #f 2}})) (bool))
(test (typecheck (parse '{fst {cons #f #t}})) (bool))
(test (typecheck (parse '{snd {cons 1 2}})) (num))
(test (typecheck (parse '{snd {cons #f 2}})) (bool))
(test (typecheck (parse '{snd {cons #f #t}})) (bool))
(test (typecheck (parse '{if {< 4 9} 1 0})) (num))
(test (typecheck (parse '{if #t 1 0})) (num))
(test (typecheck (parse '{if #f 1 0})) (num))
(test (typecheck (parse '{if {< 4 9} #t #f})) (bool))
(test (typecheck (parse '{if {< 4 9} {cons 1 2} {cons 3 4}})) (pair (num) (num)))

;Casos error con +
(test/exn (typecheck (parse '{+ 10 #t})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{+ 10 #f})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{+ #f 10})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{+ #t 10})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{+ #t #t})) "Static type error: expected Num found Bool")

(test/exn (typecheck (parse '{+ 10 {cons 1 2}})) "Static type error: expected Num found Pair")
(test/exn (typecheck (parse '{+ {cons 1 2} 10})) "Static type error: expected Num found Pair")
(test/exn (typecheck (parse '{+ {cons 1 2} {cons 3 4}})) "Static type error: expected Num found Pair")

;Casos error con <
(test/exn (typecheck (parse '{< 8 #t})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{< #f 56})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{< #f #t})) "Static type error: expected Num found Bool")

(test/exn (typecheck (parse '{< 8 {cons 2 4}})) "Static type error: expected Num found Pair")
(test/exn (typecheck (parse '{< {cons 2 4} 7})) "Static type error: expected Num found Pair")
(test/exn (typecheck (parse '{< {cons 1 2} {cons 3 4}})) "Static type error: expected Num found Pair")

;Casos error con =
(test/exn (typecheck (parse '{= 54 #t})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{= #f 1})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{= #f #t})) "Static type error: expected Num found Bool")

(test/exn (typecheck (parse '{= 3 {cons 1 2}})) "Static type error: expected Num found Pair")
(test/exn (typecheck (parse '{= {cons 38 23} 7})) "Static type error: expected Num found Pair")
(test/exn (typecheck (parse '{= {cons 1 2} {cons 3 4}})) "Static type error: expected Num found Pair")

;Casos error con Fst
(test/exn (typecheck (parse '{fst 1})) "Static type error: expected Pair found Num")
(test/exn (typecheck (parse '{fst #t})) "Static type error: expected Pair found Bool")
(test/exn (typecheck (parse '{fst #f})) "Static type error: expected Pair found Bool")

;Casos error con Snd
(test/exn (typecheck (parse '{snd 2})) "Static type error: expected Pair found Num")
(test/exn (typecheck (parse '{snd #t})) "Static type error: expected Pair found Bool")
(test/exn (typecheck (parse '{snd #f})) "Static type error: expected Pair found Bool")

;Casos error con If
(test/exn (typecheck (parse '{if 3 1 0})) "Static type error: expected Bool found Num"); error en el condicional
(test/exn (typecheck (parse '{if {cons 1 2} 1 0})) "Static type error: expected Bool found Pair"); error en el condicional
(test/exn (typecheck (parse '{if #t #t 0})) "Static type error: expected Bool found Num") ; el error siempre arroja expected del typo de la rama true y el found de la rama false
(test/exn (typecheck (parse '{if #t #t {cons 1 2}})) "Static type error: expected Bool found Pair")
(test/exn (typecheck (parse '{if #t 1 #f})) "Static type error: expected Num found Bool")
(test/exn (typecheck (parse '{if #t 1 {cons 1 2}})) "Static type error: expected Num found Pair")
(test/exn (typecheck (parse '{if #t {cons 1 2} #f})) "Static type error: expected Pair found Bool")
(test/exn (typecheck (parse '{if #t {cons 1 2} 1})) "Static type error: expected Pair found Num")



; interp : Expr Env List[FunDef] -> number? (o error)
;evalua la expresion con las funciones definidas en la lista
(define (interp expr env fundefs)
  (match expr
    [(Num n) n]
    [(Id x) (lookup-env x env)]
    [(Bool b) b]
    [(Cons h t) (cons (interp h env fundefs) (interp t env fundefs))] ;; usa if para la verificacion de typo?
    [(Add l r) (+ (match (interp l env fundefs)
                    [(? cons?) (error "Runtime type error: Expected Number found Pair")]
                    [(? boolean?) (error "Runtime type error: Expected Number found Bool")]
                    [(? number?) (interp l env fundefs)])
                  (match (interp r env fundefs)
                    [(? cons?) (error "Runtime type error: Expected Number found Pair")]
                    [(? boolean?) (error "Runtime type error: Expected Number found Bool")]
                    [(? number?) (interp r env fundefs)])
                    )]
      
    [(Less l r) (< (match (interp l env fundefs)
                      [(? cons?) (error "Runtime type error: Expected Number found Pair")]
                      [(? boolean?) (error "Runtime type error: Expected Number found Bool")]
                      [(? number?) (interp l env fundefs)])
                    (match (interp r env fundefs)
                      [(? cons?) (error "Runtime type error: Expected Number found Pair")]
                      [(? boolean?) (error "Runtime type error: Expected Number found Bool")]
                      [(? number?) (interp r env fundefs)])
                    )]
    [(Equals l r) (= (match (interp l env fundefs)
                      [(? cons?) (error "Runtime type error: Expected Number found Pair")]
                      [(? boolean?) (error "Runtime type error: Expected Number found Bool")]
                      [(? number?) (interp l env fundefs)]) 
                      (match (interp r env fundefs)
                      [(? cons?) (error "Runtime type error: Expected Number found Pair")]
                      [(? boolean?) (error "Runtime type error: Expected Number found Bool")]
                      [(? number?) (interp r env fundefs)]) 
                  )]

    [(Fst lst) (car (match (interp lst env fundefs)
                      [(? boolean?) (error "Runtime type error: Expected Pair found Bool")]
                      [(? number?) (error "Runtime type error: Expected Pair found Number")]
                      [(? cons?) (interp lst env fundefs)])
                )]

    [(Snd lst) (cdr (match (interp lst env fundefs)
                      [(? boolean?) (error "Runtime type error: Expected Pair found Bool")]
                      [(? number?) (error "Runtime type error: Expected Pair found Number")]
                      [(? cons?) (interp lst env fundefs)])
                )]
    [(If c t f) (if (match (interp c env fundefs)
                      [(? number?) (error "Runtime type error: Expected Bool found Number")]
                      [(? cons?) (error "Runtime type error: Expected Bool found Pair")]
                      [(? boolean?) (interp c env fundefs)]
                      )
                (interp t env fundefs)
                (interp f env fundefs))]
    [(With x e b)
     (interp b
             (extend-env x (interp e env fundefs) env)
             fundefs)]
    
    [(App f e)
     (def (fundef _ arg b) (lookup-fundef f fundefs))
     (interp b
             (extend-env arg (interp e env fundefs) (empty-env)) ;; static scope!
             fundefs)]))




(define (run prog [fundefs '()])
  (interp (parse prog) (empty-env) fundefs))



(test (run 10) 10)
(test (run #t) #t)
(test/exn (run 'x) "free")
(test (run '{cons 1 2}) (cons 1 2))
(test (run '{+ 10 8}) 18)
(test (run '{+ 10 {+ 1 3}}) 14)
(test/exn (run '{+ {cons 1 2} {+ 1 3}}) "Expected Number found Pair");rama izq
(test/exn (run '{+ 1 {+ 1 {cons 1 2}}}) "Expected Number found Pair");rama dcha
(test/exn (run '{+ #t {+ 1 3}}) "Expected Number found Bool");rama izq
(test/exn (run '{+ 1 {+ 1 #f}}) "Expected Number found Bool");rama dcha
(test (run '{< 24 54}) #t)
(test (run '{< 54 12}) #f)
(test/exn (run '{< {cons 1 2} 3}) "Expected Number found Pair")
(test/exn (run '{< 1 {cons 1 2}}) "Expected Number found Pair")
(test/exn (run '{< #t 1}) "Expected Number found Bool")
(test/exn (run '{< 1 #f}) "Expected Number found Bool")

(test (run '{= 3 3}) #t)
(test (run '{= 3 2}) #f)
(test/exn (run '{= {cons 1 2} 3}) "Expected Number found Pair")
(test/exn (run '{= 3 {cons 1 2}}) "Expected Number found Pair")
(test/exn (run '{= #t #f}) "Expected Number found Bool");solo igualdad entre numeros
(test/exn (run '{= #t 1}) "Expected Number found Bool")
(test/exn (run '{= 1 #f}) "Expected Number found Bool")
(test (run '{fst {cons 1 2}}) 1)
(test/exn (run '{fst 1}) "Expected Pair found Number")
(test/exn (run '{fst #t}) "Expected Pair found Bool")
(test (run '{snd {cons 1 2}}) 2)
(test/exn (run '{snd 1}) "Expected Pair found Number")
(test/exn (run '{snd #t}) "Expected Pair found Bool")
(test (run '{if #t 1 0}) 1)
(test (run '{if #f 1 0}) 0)
(test (run '{if #t {+ 1 5} 0}) 6)
(test (run '{if #f 1 {+ 1 8}}) 9)
(test (run '{if {< 24 54} 24 54}) 24)
(test/exn (run '{if 54 1 0}) "Expected Bool found Number")
(test/exn (run '{if {cons 1 4} 1 0}) "Expected Bool found Pair")



(test (run '{with {{x 10}}
              {+ x x}})
      20)
(test (run '{with {{x 10}}
                  {+ 2 3}})
      5)

(test (run '{with {{x 10} {y 5}}
          x})

      10)
; local scope is indeed local
(test/exn (run '{with {{x {with {{y 10}}
                           {+ y y}}}}
                  {with {{z y}}
                        {+ x z}}})
          "free")

(test (run '{with {{x {with {{y 10}}
                           {+ y y}}}}
                  {with {{z {+ x x}}}
                        {+ x z}}})
      60)

(test (run '{f 1}
           (list (fundef 'f 'x (parse '{+ x x}))))
      2)



(test/exn (run '{f 1}) "undefined")

(test
 (run '{with {{x 10}}
                  {f {+ 2 x}}}
           (list (fundef 'f 'x (parse '{+ x x}))))

 24)

(test (run '{with {{x 10}}
                  {f {+ 2 x}}}
           (list (fundef 'f 'x (parse '{+ {g x}
                                          {g x}}))
                 (fundef 'g 'y (parse '{+ y y}))))
      48)

; queremos scope lexico
(test/exn (run '{with {{n 10}}
                      {f 1}}
               (list (fundef 'f 'x (parse '{+ x n}))))
          "free")


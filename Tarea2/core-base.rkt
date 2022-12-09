#lang play

(print-only-errors #t)

(require "env.rkt")

#|
<CL> ::= | <num>
         | {+ <CL> <CL>}
         | {if0 <CL> <CL> <CL>}
         | {with {<sym> <CL>} <CL>}
         | <id>
         | {<CL> <CL>}
         | {fun {<sym>} <CL>}
         | {mfun {<sym>} <CL>}
         | {printn <CL>}
|#
(deftype CL
  (num n)
  (add l r)
  (if0 c t f)
  (fun id body)
  (mfun id body) ;parte 2 - a
  (id s)
  (app fun-expr arg-expr)
  (printn e))

;; parse-cl :: s-expr -> CL
(define (parse-cl s-expr)
  (match s-expr
    [(? number?) (num s-expr)]
    [(? symbol?) (id s-expr)]
    [(list '+ l r) (add (parse-cl l) (parse-cl r))]
    [(list 'if0 c t f) (if0 (parse-cl c)
                            (parse-cl t)
                            (parse-cl f))]
    [(list 'with (list x e) b)
     (app (fun x (parse-cl b)) (parse-cl e))]
    [(list 'fun (list x) b) (fun x (parse-cl b))]
    [(list 'mfun (list x) b) (mfun x (parse-cl b))] ;parte 2 - a
    [(list 'printn e) (printn (parse-cl e))]
    [(list f a) (app (parse-cl f) (parse-cl a))]))

;; values
(deftype Val
  (numV n)
  (closV id body env)
  (mclosV id body env table)) ;parte 2 - b

;log
(define log (box '()))
(define log-p (make-parameter println))
;(define aux (make-parameter '()))

;; result
(deftype Result 
    (result val log))  ;parte 1 - a

;; println-g :: <num> -> void
;;Dado un numero lo agrega al log global
(define (println-g n)
 (set-box! log (cons n (unbox log))))

;; println-p :: <num> -> void
;;Dado un numero lo agrega al log global
;(define (println-p n)
  ;(parameterize [log-p (cons n (log-p))])
  ;)



;; interp :: Expr Env -> Val
(define (interp expr env)
  (match expr
    [(num n) (numV n)]
    [(fun id body) (closV id body env)]
    [(mfun id body) (define my-table (make-hash)) (mclosV id body env my-table)]; la idea aca es crear la tabla para mfun y asucialarla a su promesa  ;parte 2 - c
    [(add l r) (num+ (interp l env) (interp r env))]
    [(if0 c t f)
     (if (num-zero? (interp c env))
         (interp t env)
         (interp f env))]
    [(id x) (env-lookup x env)]
    [(printn e) 
      (def (numV n) (interp e env))
      ;(println-g n) ; (println n)<-antes de P1-parte 1 primer intento ; esta seccion la deje porsiacaso se quiera seguir probando el log con box
      ((log-p) n) ;P1-PARTE1
      (numV n)
      ]
    [(app fun-expr arg-expr)
     (match (interp fun-expr env)
       [(closV id body fenv)
        (interp body
                (extend-env id
                            (interp arg-expr env)
                            fenv))]
        [(mclosV id body fenv table)       ;idea: asociar las keys con la applicacion de la funcion para poder hashearla     ;parte 2 - c
        (if (hash-has-key? table body) ; si la llave ya existe
            (hash-ref table body) ; saca la el resultado
            (begin (hash-set! table body (interp body (extend-env id(interp arg-expr env)fenv)))(hash-ref table body))
            )]
                            )]))



(define (num+ n1 n2)
  (numV (+ (numV-n n1) (numV-n n2))))
 
(define (num-zero? n)
  (zero? (numV-n n)))

;; interp-g :: Expr -> Result
;;interpreta una exp y retorna su valor de tipo result. Ademas reinicia el log cada vez que se es llamado
(define (interp-g expr)
  (set-box! log '())
  (match (interp expr empty-env)
    [(numV n) (result n log)]
    [_ 'changos]
    ))

;; interp-p :: Expr -> Result
;;interpreta una exp y retorna su valor de tipo result. Ademas reinicia el log cada vez que se es llamado P1-PARTE2
(define (interp-p expr)
    (set-box! log '())
    (match (parameterize ([log-p println-g]) (interp expr empty-env))
      [(numV n) (result n log)]
      [_ 'changos]
      )
    )
  


 
;; interp-top :: CL -> number
;; interpreta una expresión y retorna el valor final
(define (interp-top expr)
  (match (interp expr empty-env)
    [(numV n) n]
    [_ 'procedure]))
    
;; run-cl :: s-expr -> number
(define (run-cl prog)
  (interp-top (parse-cl prog)))

;; run-g :: s-expr -> number
;;rutina para ejecutar una s-exprecion de manera mas comoda parsea e intepreta usando el box log en un "paso"
(define (run-g prog)
  (interp-g (parse-cl prog)))

;; run-p :: s-expr -> number
;;rutina para ejecutar una s-exprecion de manera mas comoda parsea e intepreta usando la parametrizacion en un "paso"
(define (run-p prog)
  (interp-p (parse-cl prog)))

;;resLog :: Result -> list[num]
;;extrea el contenido del box log de un Result, notar que el orden de la lista es desde el num mas nuevo al mas viejo
(define (resLog res)
  (match res
  [(result v b) (unbox b)]
  [_ (error "expected Result")])
   )




;; tests
(test (run-cl '{with {addn {fun {n}
                          {fun {m}
                            {+ n m}}}}
                 {{addn 10} 4}})
      14)
;; ...

;;------------PARTE 1-------------------
;;muchos de los test siguientes estan comentados para no llenar la consola con prints al ejecutar el archivo
;; estos testeos son del enunciado al momento de probar print, y un par de funciones que tuve definir de manera auxiliar por comidad


;Ejemplos de que no es posible testear print
#|
(test (run-cl '{with {x {printn 1}} x}) 
  1)

(test 
  (run-cl '{+ 1 {printn {+ 1 2}}})
  4)

(test (run-cl '{with {add1 {fun {x} {+ {printn x} 1}}}
                {add1 2}})
                3)
|#


;---------Agregando logs: primer intento------------------;


;-------- test run-g ----------------
#|
(test (run-g '{+ 1 {+ 1 2}}) 
      (result 4 '#&())) ; '#&()<-box vacio

(test (run-g '{with {add1 {fun {x} {+ x 1}}}
                {add1 2}})
                (result 3 '#&()))



;-------- test-reslog ---------------
Estos test para reslog ya no funcionan por modificacion que hice con run-p
pero los test con alcance dinamico usan resLog
(test (resLog (run-g '{+ 1 {+ 1 2}})) 
    '())

(test (resLog (interp-g (parse-cl '{+ 1 {+ {printn 1} {printn 1}}}))) 
    '(1 1))

(test (resLog (interp-g (parse-cl '{+ {printn 1} {+ {printn 2} {printn 3}}}))) 
    '(3 2 1))

(test (resLog (interp-g (parse-cl '{if0 0 1 {printn 2}}))) 
    '())

(test (resLog (interp-g (parse-cl '{if0 1 1 {printn 2}}))) 
    '(2))

|#


;---------Segundo intento alcance dinamico------------------;

;-------------tests---------;
;add
(test (resLog (run-p '{+ 1 {+ 1 3}})) '())
(test (resLog (run-p '{+ {printn 1} {+ 1 3}})) '(1))
(test (resLog (run-p '{+ {printn 1} {+ {printn 2} 3}})) '(2 1))
(test (resLog (run-p '{+ {printn 1} {+ {printn 2} {printn 3}}})) '(3 2 1))
(test (resLog (run-p '{+ {printn 1} {printn {+ 2 3}}})) '(5 1))
(test (resLog (run-p '{+ {printn 1} {printn {+ {printn 2} 3}}})) '(5 2 1))

;app fun
(test (resLog (run-p '{with {add1 {fun {x} {+ x 1}}}
                {add1 2}}))
                '())
(test (resLog (run-p '{with {add1 {fun {x} {+ x {printn 1}}}}
                {add1 2}}))
                '(1))
(test (resLog (run-p '{with {add1 {fun {x} {+ {printn x} 1}}}
                {add1 2}})) ; x = 2 
                '(2)) 
(test (resLog (run-p '{with {add1 {fun {x} {printn {+ {printn x} 1}}}}
                {add1 2}})) ; x = 2 luego la suma el 1 y el 2
                '(3 2))

;if0
(test (resLog (run-p '{if0 0 1 2}))
                '())
(test (resLog (run-p '{if0 1 1 2}))
                '())
(test (resLog (run-p '{if0 {printn 0} 1 2}))
                '(0))
(test (resLog (run-p '{if0 {printn 1} 1 2}))

                '(1))
(test (resLog (run-p '{if0 0 {printn 1} 2}))
                '(1))
(test (resLog (run-p '{if0 0 1 {printn 2}})) ; la rama f nunca alcanza a ejecutarse -> '()
                '())
(test (resLog (run-p '{if0 1 {printn 1} 2})) ; la rama f nunca alcanza a ejecutarse -> '()
                '())


               
;-----------------------Parte 2-----------------------------------;
;Testing de funciones memoizadas

(test (resLog (run-p '{with {double {mfun {x} {+ {printn x} x}}}
                  {+ {double 2}{double 2}}}))
                  '(2))

(test (resLog (run-p '{with {double {mfun {x} {+ {printn x} x}}}
                  {printn {+ {double 2}{double 2}}}}))
                  '(8 2))
(test (resLog (run-p '{with {double {mfun {x} {+ {printn x} x}}}
                  {printn {+ {printn {double 2}}{double 2}}}}))
                  '(8 4 2))


(test (resLog (run-p '{with {add1 {mfun {x} {+ x {printn 1}}}}
                {with {add2 {fun {x} {+ x {printn 2}}}}
                    {+ {+ {add1 2} {add1 2}} {+ {add2 2} {add2 2}}}}}))
                    '(2 2 1))

(test (resLog (run-p '{with {add1 {mfun {x} {+ x {printn 1}}}}
                {with {add2 {mfun {x} {+ x {printn 2}}}}
                    {+ {+ {add1 2} {add1 2}} {+ {add2 2} {add2 2}}}}}))
                    '(2 1))
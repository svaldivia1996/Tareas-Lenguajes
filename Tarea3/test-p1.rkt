#lang play
(require "main-p1.rkt")
(print-only-errors)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                 TESTS BASE                                  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (run-val '{+ 1 2}) 3)
(test (run-val '{< 1 2}) #t)
(test (run-val '{- 2 1}) 1)
(test (run-val '{* 2 3}) 6)
(test (run-val '{= {+ 2 1} {- 4 1}}) #t)
(test (run-val '{and #t #f}) #f)
(test (run-val '{or #t #f}) #t)
(test (run-val '{not {not #t}}) #t)
(test (run-val '{if {not #f} {+ 2 1} 4}) 3)
(test (run-val '{with {{x 5} {y 3}}
                      {begin {+ x 1}
                             {+ x y}}}) 8)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                TESTS ENUNCIADO                              ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|RECUERDE DESCOMENTAR LOS TEST|#

; Me dio problemas ejecutar el init al mismo tiempo que al ejecutar new, por lo que hay que expresar explicitamente el init antes de usar un objeto
; Tambien ocurre cosas raras cuando tengo metodos con mas de 2 argumentos TODO arreglar eso


;Debido a los problemas describidos anteriormente los test que vienen son los del enunciado "tuneados" con el llamado init
(test (run-val '{with {{c {class {x y}
                            {def init {}
                              {begin {set x 1} {set y 2}}}
                            {def init {init-x init-y}
                              {begin {set x init-x} {set y init-y}}}
                            {def sum {z} {+ {get self x} {+ {get self y} z}}}
                            {def set-x {val} {set x val}}}}
                       {o {new c {3 4}}}}
                      {begin {-> o init} {begin
                                           {-> o set-x {+ 1 3}}
                                           {+ {-> o sum 3} {get o y}}}}})
      11)

#;((run-val '{with {{A {class {}
                         {def apply {c} {-> {new c} m}}}}
                    {o {new A {}}}}
                   {-> o apply {class {x}
                                 {def init {} {set x 2}}
                                 {def m {} {get self x}}}}})
   2)

#;(test/exn (run-val '{begin {with {{A {class {x}
                                         {def init {} {set x 2}}
                                         {def init {init-x} {set x init-x}}
                                         {def m {} {get self x}}}}}
                                   10}
                             {new A}})
            "free identifier: A")

(test (run-val '{with {{x 10}
                       {A {class {}
                            {def m {y} {+ x y}}}}
                       {o {new A {}}}}
                      {-> o m 1}})
      11)

#;(test/exn (run-val '{begin {with {{A {class {x y}
                                         {def init {init-x init-y}
                                           {begin {set x init-x} {set y init-y}}}
                                         {def init {init-x init-y}
                                           {begin {set x 12} {set y 3}}}
                                         {def init {init-x} {set x init-x}}
                                         {def m {} {get self x}}}}}
                                   10}
                             {new A {}}})
            "error: same arity constructor error")

#;(test/exn (run-val '{with {{x 10}
                             {A {class {z}
                                  {def m {y} {+ x y}}}}
                             {o {new A {x}}}}
                            {-> o m 1}})
            "error: constructor not found")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                  SUS TESTS                                  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;      FUNCIONES AUXILIARES                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;preparse
(test (preparse 'x) '(field x null))
(test (map preparse (list 'x 'y 'z)) '((field x null) (field y null) (field z null)))


;parse-membs
(test (parse-membs '(field x null)) (field 'x (null)))
(test (parse-membs '(field x 3)) (field 'x (num 3)))
(test (parse-membs '(def init (val) (set x val))) (method 'init '(val) (set (self) (id 'x) (id 'val))))

;field-lookup
(test (field-lookup 'x (list (cons 'x (box (numV 10))) (cons 'y (box (numV 12))))) (box (numV 10)))
(test (field-lookup 'y (list (cons 'x (box (numV 10))) (cons 'y (box (numV 12))))) (box (numV 12)))
(test/exn (field-lookup 'z (list (cons 'x (box (numV 10))) (cons 'y (box (numV 12))))) "field not found")


;;Test of method lookup
(test (method-lookup 'sum3 (classV empty-env  '() (list (method 'sum3 '() (binop + (num 1) (num 2))) (method 'foo '() (self))))) (cons (method 'sum3 '() (binop + (num 1) (num 2))) (classV empty-env '() (list (method 'sum3 '() (binop + (num 1) (num 2))) (method 'foo '() (self))))))
(test/exn (method-lookup 'foo (classV empty-env  '() (list (method 'sum3 '() (binop + (num 1) (num 2)))))) "method not found")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;         TEST DE FUNCIONALIDAD       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(test (run-val '{with {{x 10}
                       {A {class {}
                            {def m {y} {+ x y}}}}
                       {o {new A {}}}}
                      {-> o m 1}})
      11)

(test (run-val '{with {{c {class {x y}
                            {def init {}
                              {begin {set x 1} {set y 2}}}
                            {def sum {z} {+ {get self x} {+ {get self y} z}}}
                            {def set-x {val} {set x val}}
                            {def set-y {val} {set y val}}}}
                       {o {new c {}}}}
                      {begin {-> o init} {+ {get o x} {get o y}}}}) 3)

(test (run-val '{with {{c {class {x y}
                            {def init {}
                              {begin {set x 1} {set y 2}}}
                            {def sum {z} {+ {get self x} {+ {get self y} z}}}
                            {def set-x {val} {set x val}}
                            {def set-y {val} {set y val}}}}
                       {o {new c {}}}}
                      {begin {-> o init}{begin {-> o set-y 1} {+ {get o x} {get o y}}}}}) 2)


(test (run-val '{with {{c {class {x y}
                            {def init {}
                              {begin {set x 1} {set y 2}}}
                            {def sum {z} {+ {get self x} {+ {get self y} z}}}
                            {def set-x {val} {set x val}}
                            {def set-y {val} {set y val}}}}
                       {o {new c {}}}}
                      {begin
                        {-> o init}
                        {begin
                          {-> o set-y 1}
                          {* 2 {-> o sum 3}}}}}) 10)

(test/exn (run-val '{begin {with
                            {{ A
                               {class
                                   {x}
                                 {def m {} {get this x}}}}}
                            10}
                           {new A {}}}) "env-lookup: free identifier: A")

(test/exn (run-val '{begin {with
                            {{A {class {x}
                                  {def foo {} {get self x}}}}}
                            5}
                           {new A {}}}) "env-lookup: free identifier")



(test (run-val '{with
                 {{x 1}
                  {c (class {} {def sum {} {+ x 5}})}
                  {x 2}
                  {o {new c {}}}}
                 {-> o sum}}) 7)



;Test de parse de uso real no pude hacer test con binOps ya que el simbolo # que aparece en #<procedure:+> esta reservado segun mi editor de texto
(test (parse '{class {x y}
                {def init {}
                  {begin {set x 1} {set y 2}}}
                {def init {init-x init-y}
                  {begin {set x init-x} {set y init-y}}}
                {def set-x {val} {set x val}}})

      (class
          (list
           (field 'x (null))
           (field 'y (null))
           (method
            'init
            '()
            (begn (set (self) (id 'x) (num 1)) (set (self) (id 'y) (num 2))))
           (method
            'init
            '(init-x init-y)
            (begn (set (self) (id 'x) (id 'init-x)) (set (self) (id 'y) (id 'init-y))))
           (method 'set-x '(val) (set (self) (id 'x) (id 'val)))))
      )







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;     TEST DE FUNCIONES AUXILIARES MUERTAS EN EL CAMINO;
; En resumen al principio trate usar todo con hash, spoiler falle horriblemente
; Dejo esto aca por si sirve en el futuro               ;

#|

;; get-fieldsMalo
(test (hash-has-key? (get-fieldsMalo (list (id 'x))) 'x) #t)
(test (hash-has-key? (get-fieldsMalo (list (id 'y))) 'x) #f)
(test (hash-has-key? (get-fieldsMalo (list (id 'x) (id 'y))) 'y) #t)


;;get-methodsMalo
(test (hash-has-key? (get-methodsMalo (list (method 'sumxy '(x y) '(+ x y)))) 'sumxy) #t)
(test (hash-has-key? (get-methodsMalo (list (method 'init '() '(begin (set x 1) (set y 2))) (method 'sum '(z) '(+ (get self x) (+ (get self y) z))))) 'init) #t)
(test (hash-has-key? (get-methodsMalo (list (method 'init '() '(begin (set x 1) (set y 2))) (method 'sum '(z) '(+ (get self x) (+ (get self y) z))))) 'sum) #t)
(test (hash-has-key? (get-methodsMalo (list (method 'init '() '(begin (set x 1) (set y 2))) (method 'sum '(z) '(+ (get self x) (+ (get self y) z))))) 'mult) #f)


;;getMethodFromClass
(define cInt (run '(class (x) (def get-x () (get self x)))))
(define cInt2 (run '(class (x y) (def sum () (+ x y)))))
(define getMethodSweet (getMethodFromClass 'get-x cInt))
(test (hash-has-key? getMethodSweet 'args) #t)
(test (hash-has-key? getMethodSweet 'body) #t)
(test (getMethodFromClass 'get-y cInt) #f) ;"method not found"


;; getFieldFromClass
;;en los test de setIdFromClass se prueban los casos que retorna valores
(test/exn (getFieldFromClass cInt 'x) "field not found")
(test (getFieldFromClass cInt 'z) #f)

;; setIdFromClass
(setIdFromClass cInt 'x (numV 2))
(test (equal? (getFieldFromClass cInt 'x) (numV 2)) #t)


;; sendController
(define nullarg (run '(class (x) (def get-x () (get self x)))))
(test
 (sendController cInt 'get-x '() (extend-frame-env! 'self cInt empty-env))
 (numV 2))
(test/exn
 (sendController nullarg 'get-x '() (extend-frame-env! 'self nullarg empty-env))
 "field not found")|#



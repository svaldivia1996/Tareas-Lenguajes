#lang play
(require "main-p2.rkt")
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

(test (run-val '{with {{c1 {class {}
                             {def f {z} {< z 7}}}}
                       {c {class : c1 {}}}
                       {o {new c}}}
                      {-> o f 20}})
      #f)

(test (run-val '{with {{c2 {class {}
                             {def h {x} {+ x 1}}}}
                       {c1 {class : c2 {}
                             {def f {} #f}}}
                       {c {class : c1 {}
                            {def g {} {super h 10}}}}
                       {o {new c}}}
                      {-> o g}})
      11)

#;(test (run-val '{with {{A {class {x y}
                              {def init {} {begin {set x 1} {set y 0}}}
                              {def ax {} {get self x}}}}
                         {B {class : A {x}
                              {def init {} {set x 2}}
                              {def bx {} {get self x}}}}
                         {b {new B {}}}}
                        {-> b ax}})
        1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                  SUS TESTS                                  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define obj (class 'undefined '()))

(test (parse '{class : c1 {}}) (class (id 'c1) '()))
(test (parse '{class : c1 {} {def  f {} {+ 1 2}}}) (class (id 'c1) (list (method 'f '() (binop + (num 1) (num 2))))))
(test (parse '{class : c1 {} {def  f {} {super h 9}}}) (class (id 'c1) (list (method 'f '() (super 'h '(9))))))
(test/exn (parse '{self}) "Parse error: self definition outside class")


;;Test de uso
(test (run-val '{with {{c2 {class {}
                             {def h {x} {+ x 1}}}}
                       {c1 {class : c2 {}
                             {def f {} {* 33 3}}}}
                       {o {new c1}}}
                      {-> o h 10}})
      11)

(test (run-val '{with {{c2 {class {}
                             {def h {x} {+ x 1}}}}
                       {c1 {class : c2 {}
                             {def f {} {* 33 3}}}}
                       {o {new c1}}}
                      {-> o f}})
      99)

(test/exn (run-val '{with {{c2 {class {}
                                 {def h {x} {+ x 1}}}}
                           {c1 {class : c2 {}
                                 {def f {} {* 33 3}}}}
                           {o {new c1}}}
                          {-> o g}})
          "method not found")

(test/exn (run-val '{with {{c2 {class {}
                                 {def h {x} {+ x 1}}}}
                           {c1 {class : c2 {}
                                 {def f {} #f}}}
                           {c {class : c1 {}
                                {def g {} {super g 10}}}}
                           {o {new c}}}
                          {-> o g}})
          "method not found")

(test (run-val '{with {{c2 {class {}
                                 {def h {x} {+ x 1}}}}
                           {c1 {class : c2 {}
                                 {def f {} #f}}}
                           {c {class : c1 {}
                                {def g {} {super f}}}}
                           {o {new c}}}
                          {-> o g}})
          #f)
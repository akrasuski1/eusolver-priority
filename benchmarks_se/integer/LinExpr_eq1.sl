(set-logic LIA)

(synth-fun eq1 ( (x Int) (y Int) (z Int) ) Int
    ((Start Int (x
                 y
		 z
                 0
                 1
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))

(define-fun iteB (( b1 Bool ) (b2 Bool ) (b3 Bool )) Bool ( or ( and b1 b2 ) ( and (not b1 ) b3 ) ) )
(define-fun plus2 ((b1 Int) (b2 Int)) Int ( + b1 b2))
(define-fun plus3 ((b1 Int) (b2 Int) (b3 Int)) Int ( +  ( + b1 b2) b3))
(define-fun plus4 ((b1 Int) (b2 Int) (b3 Int) (b4 Int)) Int ( +  ( plus3  b1 b2 b3) b4))
(define-fun plus5 ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int)) Int (+  ( plus4 b1 b2 b3 b4) b5))
(define-fun plus6 ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int) (b6 Int) ) Int (+  ( plus5 b1 b2 b3 b4  b5) b6  ))
(define-fun plus7 ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int) (b6 Int) (b7 Int)) Int (+  ( plus6 b1 b2 b3 b4  b5 b6 ) b7  ))
(define-fun plus_eight ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int) (b6 Int) (b7 Int) (be Int)) Int (+  ( plus7 b1 b2 b3 b4  b5 b6 b7) be  ))
(define-fun plus_nine ((b1 Int) (b2 Int) (b3 Int) (b4 Int) (b5 Int) (b6 Int) (b7 Int) (be Int) (bn Int)) Int (+  ( plus_eight b1 b2 b3 b4  b5 b6 b7 be) bn  ))

(define-fun or3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool ( or ( or b1 b2) b3))
(define-fun three-times  ((b1 Int )) Int ( plus3 b1 b1 b1))
(define-fun five-times  ((b1 Int )) Int ( plus5 b1 b1 b1 b1 b1 ))
(define-fun seven-times ((b1 Int )) Int ( plus7 b1 b1 b1 b1 b1 b1 b1 ))
(define-fun nine-times  ((b1 Int )) Int ( plus_nine b1 b1 b1 b1 b1 b1 b1 b1 b1))

(define-fun minus ((b1 Int)) Int ( - 0  b1 ))

(declare-var x Int ) 
(declare-var y Int ) 
(declare-var z Int ) 

; if ( 5x -3 <= -3y +7 + 9 z) then min(x,y,z) else max(x,y,z) endif

( constraint (  iteB ( <=  (  plus2 ( five-times x ) ( minus 3 ) )   ( plus3   ( minus ( three-times y ) )  7 ( nine-times z )  ) ) (  >=  ( eq1 x y z )  x )  ( <= (eq1 x y z ) x ) ) )
( constraint (  iteB ( <=  (  plus2 ( five-times x ) ( minus 3 ) )   ( plus3   ( minus ( three-times y ) ) 7 ( nine-times z )  ) ) (  >=  ( eq1 x y z )  y )  ( <= (eq1 x y z ) y ) ) )
( constraint (  iteB ( <=  (  plus2 ( five-times x ) ( minus 3 ) )   ( plus3   ( minus ( three-times y ) ) 7 ( nine-times z )  ) ) (  >=  ( eq1 x y z )  z )  ( <= (eq1 x y z ) z ) ) )
( constraint (  or3 (  =  ( eq1 x y z )  x ) (  =  ( eq1 x y z )  y ) (  =  ( eq1 x y z )  z ) ) )


(check-synth)



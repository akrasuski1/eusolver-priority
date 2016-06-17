(set-logic LIA)

(synth-fun max6 ((x1 Int)) Int
)

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)

(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(constraint (= (max6 x1) (f x1)))
(constraint (= (max6 x2) (f x2)))
(constraint (= (max6 x3) (f x3)))
(constraint (= (max6 x1) (g x1)))
(constraint (= (max6 x2) (g x2)))

(check-synth)



(set-logic LIA)

(synth-fun min ((a0 Int) (a1 Int)) Int)
(synth-fun max ((a0 Int) (a1 Int)) Int)

(declare-var x0 Int)
(declare-var x1 Int)


(constraint (>= (max x0 x1) x0))
(constraint (>= (max x0 x1) x1))
(constraint (<= (min x0 x1) x0))
(constraint (<= (min x0 x1) x1))
(constraint (or (= (max x0 x1) x0) (= (max x0 x1) x1)))
(constraint (or (= (min x0 x1) x0) (= (min x0 x1) x1)))

(check-synth)


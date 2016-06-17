(set-logic LIA)

(synth-fun max2 ((a0 Int) (a1 Int)) Int
    ((Start Int (a0
                 a1
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
(declare-var x0 Int)
(declare-var x1 Int)


(constraint (= (max2 x0 x1)
	(let (
		(d Int (- x0 x1))
		)
	(ite (> d 0) x0 x1)
	)
))

(check-synth)


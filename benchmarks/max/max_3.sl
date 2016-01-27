(set-logic LIA)

(synth-fun max3 ((a0 Int) (a1 Int) (a2 Int)) Int
    ((Start Int (a0
                 a1
                 a2
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
(declare-var x2 Int)


(constraint (>= (max3 x0 x1 x2) x0))
(constraint (>= (max3 x0 x1 x2) x1))
(constraint (>= (max3 x0 x1 x2) x2))
(constraint
    (or (= (max3 x0 x1 x2) x0)
    (or (= (max3 x0 x1 x2) x1)
        (= (max3 x0 x1 x2) x2))))

(check-synth)


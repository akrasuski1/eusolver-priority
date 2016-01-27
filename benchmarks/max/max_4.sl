(set-logic LIA)

(synth-fun max4 ((a0 Int) (a1 Int) (a2 Int) (a3 Int)) Int
    ((Start Int (a0
                 a1
                 a2
                 a3
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
(declare-var x3 Int)


(constraint (>= (max4 x0 x1 x2 x3) x0))
(constraint (>= (max4 x0 x1 x2 x3) x1))
(constraint (>= (max4 x0 x1 x2 x3) x2))
(constraint (>= (max4 x0 x1 x2 x3) x3))
(constraint
    (or (= (max4 x0 x1 x2 x3) x0)
    (or (= (max4 x0 x1 x2 x3) x1)
    (or (= (max4 x0 x1 x2 x3) x2)
        (= (max4 x0 x1 x2 x3) x3)))))

(check-synth)


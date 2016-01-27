(set-logic LIA)

(synth-fun max6 ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int) (a5 Int)) Int
    ((Start Int (a0
                 a1
                 a2
                 a3
                 a4
                 a5
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
(declare-var x4 Int)
(declare-var x5 Int)


(constraint (>= (max6 x0 x1 x2 x3 x4 x5) x0))
(constraint (>= (max6 x0 x1 x2 x3 x4 x5) x1))
(constraint (>= (max6 x0 x1 x2 x3 x4 x5) x2))
(constraint (>= (max6 x0 x1 x2 x3 x4 x5) x3))
(constraint (>= (max6 x0 x1 x2 x3 x4 x5) x4))
(constraint (>= (max6 x0 x1 x2 x3 x4 x5) x5))
(constraint
    (or (= (max6 x0 x1 x2 x3 x4 x5) x0)
    (or (= (max6 x0 x1 x2 x3 x4 x5) x1)
    (or (= (max6 x0 x1 x2 x3 x4 x5) x2)
    (or (= (max6 x0 x1 x2 x3 x4 x5) x3)
    (or (= (max6 x0 x1 x2 x3 x4 x5) x4)
        (= (max6 x0 x1 x2 x3 x4 x5) x5)))))))

(check-synth)


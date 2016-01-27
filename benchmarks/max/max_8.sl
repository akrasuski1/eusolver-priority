(set-logic LIA)

(synth-fun max8 ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int) (a5 Int) (a6 Int) (a7 Int)) Int
    ((Start Int (a0
                 a1
                 a2
                 a3
                 a4
                 a5
                 a6
                 a7
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
(declare-var x6 Int)
(declare-var x7 Int)


(constraint (>= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x0))
(constraint (>= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x1))
(constraint (>= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x2))
(constraint (>= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x3))
(constraint (>= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x4))
(constraint (>= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x5))
(constraint (>= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x6))
(constraint (>= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x7))
(constraint
    (or (= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x0)
    (or (= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x1)
    (or (= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x2)
    (or (= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x3)
    (or (= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x4)
    (or (= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x5)
    (or (= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x6)
        (= (max8 x0 x1 x2 x3 x4 x5 x6 x7) x7)))))))))

(check-synth)


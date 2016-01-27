(set-logic LIA)

(synth-fun max7 ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int) (a5 Int) (a6 Int)) Int
    ((Start Int (a0
                 a1
                 a2
                 a3
                 a4
                 a5
                 a6
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


(constraint (>= (max7 x0 x1 x2 x3 x4 x5 x6) x0))
(constraint (>= (max7 x0 x1 x2 x3 x4 x5 x6) x1))
(constraint (>= (max7 x0 x1 x2 x3 x4 x5 x6) x2))
(constraint (>= (max7 x0 x1 x2 x3 x4 x5 x6) x3))
(constraint (>= (max7 x0 x1 x2 x3 x4 x5 x6) x4))
(constraint (>= (max7 x0 x1 x2 x3 x4 x5 x6) x5))
(constraint (>= (max7 x0 x1 x2 x3 x4 x5 x6) x6))
(constraint
    (or (= (max7 x0 x1 x2 x3 x4 x5 x6) x0)
    (or (= (max7 x0 x1 x2 x3 x4 x5 x6) x1)
    (or (= (max7 x0 x1 x2 x3 x4 x5 x6) x2)
    (or (= (max7 x0 x1 x2 x3 x4 x5 x6) x3)
    (or (= (max7 x0 x1 x2 x3 x4 x5 x6) x4)
    (or (= (max7 x0 x1 x2 x3 x4 x5 x6) x5)
        (= (max7 x0 x1 x2 x3 x4 x5 x6) x6))))))))

(check-synth)


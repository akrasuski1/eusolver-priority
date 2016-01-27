(set-logic LIA)

(synth-fun max9 ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int) (a5 Int) (a6 Int) (a7 Int) (a8 Int)) Int
    ((Start Int (a0
                 a1
                 a2
                 a3
                 a4
                 a5
                 a6
                 a7
                 a8
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
(declare-var x8 Int)


(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x0))
(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x1))
(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x2))
(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x3))
(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x4))
(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x5))
(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x6))
(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x7))
(constraint (>= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x8))
(constraint
    (or (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x0)
    (or (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x1)
    (or (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x2)
    (or (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x3)
    (or (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x4)
    (or (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x5)
    (or (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x6)
    (or (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x7)
        (= (max9 x0 x1 x2 x3 x4 x5 x6 x7 x8) x8))))))))))

(check-synth)


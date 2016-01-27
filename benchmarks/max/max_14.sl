(set-logic LIA)

(synth-fun max14 ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int) (a5 Int) (a6 Int) (a7 Int) (a8 Int) (a9 Int) (a10 Int) (a11 Int) (a12 Int) (a13 Int)) Int
    ((Start Int (a0
                 a1
                 a2
                 a3
                 a4
                 a5
                 a6
                 a7
                 a8
                 a9
                 a10
                 a11
                 a12
                 a13
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
(declare-var x9 Int)
(declare-var x10 Int)
(declare-var x11 Int)
(declare-var x12 Int)
(declare-var x13 Int)


(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x0))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x1))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x2))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x3))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x4))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x5))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x6))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x7))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x8))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x9))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x10))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x11))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x12))
(constraint (>= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x13))
(constraint
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x0)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x1)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x2)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x3)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x4)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x5)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x6)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x7)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x8)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x9)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x10)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x11)
    (or (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x12)
        (= (max14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) x13)))))))))))))))

(check-synth)


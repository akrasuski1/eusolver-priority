(set-logic LIA)

(synth-fun max5 ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int)) Int
    ((Start Int (a0
                 a1
                 a2
                 a3
                 a4
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


(constraint (>= (max5 x0 x1 x2 x3 x4) x0))
(constraint (>= (max5 x0 x1 x2 x3 x4) x1))
(constraint (>= (max5 x0 x1 x2 x3 x4) x2))
(constraint (>= (max5 x0 x1 x2 x3 x4) x3))
(constraint (>= (max5 x0 x1 x2 x3 x4) x4))
(constraint
    (or (= (max5 x0 x1 x2 x3 x4) x0)
    (or (= (max5 x0 x1 x2 x3 x4) x1)
    (or (= (max5 x0 x1 x2 x3 x4) x2)
    (or (= (max5 x0 x1 x2 x3 x4) x3)
        (= (max5 x0 x1 x2 x3 x4) x4))))))

(check-synth)


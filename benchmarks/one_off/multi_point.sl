(set-logic LIA)

(synth-fun f ((a0 Int)) Int
    ((Start Int (a0
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

(declare-var x Int)


(constraint (= (f 0) 0))
(constraint (= (f 10) 1))
(constraint (=> (= (f x) 1) (= (f (+ x 1)) 1)))

(check-synth)


; Hacker's delight 08, minimal grammar
; Form a mask that identifies the trailing zeros

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd08 ((x (BitVec 32))) (BitVec 32) (bvand (bvnot x) (bvsub x #x00000001)))

(synth-fun f ((x (BitVec 32))) (BitVec 32)
    ((Start (BitVec 32) ((bvsub Start Start)
(if0 Start Start Start)
						 (bvnot Start)
                         (bvand Start Start)
						 #x00000001
                         x))))

(declare-var x (BitVec 32))
(constraint (= (hd08 x) (f x)))
(check-synth)


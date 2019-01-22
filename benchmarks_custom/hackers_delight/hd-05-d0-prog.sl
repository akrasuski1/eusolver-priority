; Hacker's delight 05, minimal grammar
; Right propagate the rightmost one bit

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd05 ((x (BitVec 32))) (BitVec 32) (bvor x (bvsub x #x00000001)))

(synth-fun f ((x (BitVec 32))) (BitVec 32)
    ((Start (BitVec 32) ((bvsub Start Start)
(if0 Start Start Start)
                         (bvor Start Start)
						 #x00000001
                         x))))

(declare-var x (BitVec 32))
(constraint (= (hd05 x) (f x)))
(check-synth)


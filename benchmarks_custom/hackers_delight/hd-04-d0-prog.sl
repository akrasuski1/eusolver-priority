; Hacker's delight 04, minimal grammar
; Form a bit mask that identifies the rightmost one bit and trailing zeros

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd04 ((x (BitVec 32))) (BitVec 32) (bvxor x (bvsub x #x00000001)))

(synth-fun f ((x (BitVec 32))) (BitVec 32)
    ((Start (BitVec 32) ((bvsub Start Start)
(if0 Start Start Start)
                         (bvxor Start Start)
						 #x00000001
                         x))))

(declare-var x (BitVec 32))
(constraint (= (hd04 x) (f x)))
(check-synth)


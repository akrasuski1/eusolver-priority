; Hacker's delight 09, minimal grammar
; Absolute value function

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd09 ((x (BitVec 32))) (BitVec 32) (bvsub (bvxor x (bvashr x #x0000001F)) (bvashr x #x0000001F)))

(synth-fun f ((x (BitVec 32))) (BitVec 32)
    ((Start (BitVec 32) ((bvsub Start Start)
(if0 Start Start Start)
						 (bvashr Start Start)
                         (bvxor Start Start)
						 #x0000001F
                         x))))

(declare-var x (BitVec 32))
(constraint (= (hd09 x) (f x)))
(check-synth)


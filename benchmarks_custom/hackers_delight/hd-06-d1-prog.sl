; Hacker's delight 06, difficulty 1
; Turn on the right most 0 bit

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd06 ((x (BitVec 32))) (BitVec 32) (bvor x (bvadd x #x00000001)))

(synth-fun f ((x (BitVec 32))) (BitVec 32)
    ((Start (BitVec 32) ((bvadd Start Start)
(if0 Start Start Start)
						 (bvsub Start Start)
						 (bvxor Start Start)
						 (bvand Start Start)
						 (bvneg Start)
                         (bvor Start Start)
						 #x00000000
						 #xFFFFFFFF
						 #x00000001
                         x))))

(declare-var x (BitVec 32))
(constraint (= (hd06 x) (f x)))
(check-synth)


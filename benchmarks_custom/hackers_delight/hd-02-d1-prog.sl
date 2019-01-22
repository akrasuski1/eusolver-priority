; Hacker's delight 02, difficulty 1
; Test if unsigned int is of form 2^n - 1

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd02 ((x (BitVec 32))) (BitVec 32) (bvand x (bvadd x #x00000001)))

(synth-fun f ((x (BitVec 32))) (BitVec 32)
    ((Start (BitVec 32) ((bvand Start Start)
(if0 Start Start Start)
                         (bvsub Start Start)
						 (bvor Start Start)
						 (bvadd Start Start)
						 (bvxor Start Start)
                         x
						 #x00000000
						 #xFFFFFFFF
                         #x00000001))))

(declare-var x (BitVec 32))
(constraint (= (hd02 x) (f x)))
(check-synth)


; Hacker's delight 11, minimal grammar
; Test if (nlz x) < (nlz y) where nlz is the number of leading zeros

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd11 ((x (BitVec 32)) (y (BitVec 32))) Bool (bvugt (bvand x (bvnot y)) y))

(synth-fun f ((x (BitVec 32)) (y (BitVec 32))) Bool
    ((Start Bool ((bvugt StartBV StartBV)))
(if0 Start Start Start)
	 (StartBV (BitVec 32) ((bvand StartBV StartBV)
						   (bvnot StartBV)
						   x
						   y))))

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))
(constraint (= (hd11 x y) (f x y)))
(check-synth)


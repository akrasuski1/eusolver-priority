; Hacker's delight 12, difficulty 1
; Test if (nlz x) <= (nlz y) where nlz is the number of leading zeros

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd12 ((x (BitVec 32)) (y (BitVec 32))) Bool (bvule (bvand x (bvnot y)) y))

(synth-fun f ((x (BitVec 32)) (y (BitVec 32))) Bool
    ((Start Bool ((bvule StartBV StartBV)
(if0 Start Start Start)
				  (bvult StartBV StartBV)))
	 (StartBV (BitVec 32) ((bvand StartBV StartBV)
						   (bvor StartBV StartBV)
						   (bvnot StartBV)
						   (bvadd StartBV StartBV)
						   (bvsub StartBV StartBV)
						   (bvneg StartBV)
						   (bvnot StartBV)
						   #x00000000
						   #x00000001
						   #xFFFFFFFF
						   x
						   y))))

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))
(constraint (= (hd12 x y) (f x y)))
(check-synth)


; Hacker's delight 18, difficulty 5
; determine if power of two

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd18 ((x (BitVec 32))) Bool (and (not (bvredor (bvand (bvsub x #x00000001) x))) (bvredor x)))

(synth-fun f ((x (BitVec 32))) Bool
    ((Start Bool ((bvule StartBV StartBV)
(if0 Start Start Start)
				  (bvult StartBV StartBV)
				  (bvslt StartBV StartBV)
				  (bvsle StartBV StartBV)
				  (= StartBV StartBV)))
	 (StartBV (BitVec 32) ((bvnot StartBV)
						   (bvxor StartBV StartBV)
						   (bvand StartBV StartBV)
						   (bvor StartBV StartBV)
						   (bvneg StartBV)
						   (bvadd StartBV StartBV)
						   (bvmul StartBV StartBV)
						   (bvudiv StartBV StartBV)
						   (bvurem StartBV StartBV)
						   (bvlshr StartBV StartBV)
						   (bvashr StartBV StartBV)
						   (bvshl StartBV StartBV)
						   (bvsdiv StartBV StartBV)
						   (bvsrem StartBV StartBV)
						   (bvsub StartBV StartBV)
						   x))))

(declare-var x (BitVec 32))
(constraint (= (hd18 x) (f x)))
(check-synth)


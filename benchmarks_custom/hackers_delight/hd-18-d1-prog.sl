; Hacker's delight 18, difficulty 1
; determine if power of two

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd18 ((x (BitVec 32))) Bool (and (not (bvredor (bvand (bvsub x #x00000001) x))) (bvredor x)))

(synth-fun f ((x (BitVec 32))) Bool
		   ((Start Bool ((and Start Start)
(if0 Start Start Start)
						 (not Start)
						 (or Start Start)
						 (bvredor StartBV)))
			(StartBV (BitVec 32) ((bvand StartBV StartBV)
								  (bvsub StartBV StartBV)
								  (bvadd StartBV StartBV)
								  (bvor StartBV StartBV)
								  (bvneg StartBV)
								  (bvnot StartBV)
								  (bvxor StartBV StartBV)
								  x
								  #x00000001
								  #x00000000
								  #xFFFFFFFF))))

(declare-var x (BitVec 32))
(constraint (= (hd18 x) (f x)))
(check-synth)


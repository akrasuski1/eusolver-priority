(set-logic BV)
(define-fun E ((x (BitVec 8))) (BitVec 8) (ite (bvule x #x19) (bvadd x #x41) (
						ite (bvule x #x33) (bvadd x #x47) (
							ite (bvule x #x3d) (bvsub x #x04) (
								ite (= x #x3e) #x2b #x2f)))))

(define-fun DD ((x (BitVec 8))) (BitVec 8) (ite (= x #x2f) #x3f (
						ite (= x #x2b) #x3e (
							ite (bvule x #x39) (bvadd x #x04) (
								ite (bvule x #x5a) (bvsub x #x41) (bvsub x #x47))))))



(define-fun B ((h (BitVec 8)) (l (BitVec 8)) (v (BitVec 8))) (BitVec 8)
   	(bvlshr (bvshl v (bvsub #x07 h)) (bvsub #x07 (bvsub h l))))

(define-fun d ((x (BitVec 8))) Bool (bvule x #x3f))

(synth-fun D ((x (BitVec 8)) (y (BitVec 8))) (BitVec 8)
    	((Start (BitVec 8) (
			DDStart
			(bvshl Start Const)
			(bvor Start Start)
			(B Const Const Start)
			))
	 (DDStart (BitVec 8) ((DD x) (DD y))) 
	 (Const (BitVec 8) (#x01 #x03 #x06 #x07 #x04 #x05 #x02))
))

(declare-var x (BitVec 8))
(constraint  (= x (D (E (B #x07 #x02 x) ) (E (bvshl (B #x01 #x00 x) #x04)))) )
(check-synth)    



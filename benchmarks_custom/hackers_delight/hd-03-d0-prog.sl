; Hacker's delight 03, minimal grammar
; Isolate the right most one bit

(set-logic BV)
(define-fun if0 ((x (BitVec 32)) (y (BitVec 32)) (z (BitVec 32))) (BitVec 32) (ite (= x #x00000001) y z))

(define-fun hd03 ((x (BitVec 32))) (BitVec 32) (bvand x (bvneg x)))

(synth-fun f ((x (BitVec 32))) (BitVec 32)
    ((Start (BitVec 32) ((bvneg Start)
(if0 Start Start Start)
                         (bvand Start Start)
                         x))))

(declare-var x (BitVec 32))
(constraint (= (hd03 x) (f x)))
(check-synth)


(set-logic SLIA)

(synth-fun f ((firstname String) (lastname String)) String
 ((Start String (ntString))
  (ntString String (firstname lastname " "
		    (str.++ ntString ntString)
		    (str.replace ntString ntString ntString)
		    (str.at ntString ntInt)
		    (int.to.str ntInt)
		    (str.substr ntString ntInt ntInt)))
  (ntInt Int (0 1 2
	      (+ ntInt ntInt)
	      (- ntInt ntInt)
	      (str.len ntString)
	      (str.to.int ntString)
	      (str.indexof ntString ntString ntInt)))
  (ntBool Bool (true false
		(str.prefixof ntString ntString)
		(str.suffixof ntString ntString)
		(str.contains ntString ntString)))))

(declare-var name String)

(constraint (= (f "Nancy" "FreeHafer") "Nancy FreeHafer"))
(constraint (= (f "Andrew" "Cencici") "Andrew Cencici"))
(constraint (= (f "Jan" "Kotas") "Jan Kotas"))
(constraint (= (f "Mariya" "Sergienko") "Mariya Sergienko"))

(check-synth)

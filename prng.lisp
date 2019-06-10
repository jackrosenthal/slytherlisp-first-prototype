(defun lehmer-prng (seed)
  (setq x seed)
  (defun next ()
    (setq x (mod (* 16807 x) 2147483647))))

(setq rng0 (lehmer-prng 1))
(setq rng1 (lehmer-prng 1))

(print "--> Testing RNG0 <--")
(print (rng0))
(print (rng0))
(print (rng0))
(print (rng0))

(print "--> Testing RNG1 <--")
(print (rng1))
(print (rng1))
(print (rng1))
(print (rng1))

(print "--> Testing RNG0 <--")
(print (rng0))
(print (rng0))
(print (rng0))
(print (rng0))

(print "--> Testing RNG1 <--")
(print (rng1))
(print (rng1))
(print (rng1))
(print (rng1))

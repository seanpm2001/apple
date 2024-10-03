(import apple)

(def dp (apple/jit "[(+)/ ((*)`(x::Vec n float) y)]"))
(assert (= (dp @[1.0 3.0 5.0] @[2.0 4.0 6.0]) 44.0))

(def moving-average (apple/jit ``([((+)/x)%ℝ(:x)]\`7)``))
(assert (deep= (moving-average @[1.0 2.0 3.0 4.0 5.0 6.0 7.0 8.0 9.0 10.0]) @[4.0 5.0 6.0 7.0]))

(def is-prime (apple/jit ``λn.¬((∨)/ₒ #f ([(n|x)=0]'(⍳ 2 (⌊(√(ℝn))) 1)))``))
(assert (is-prime 7))
(assert (not (is-prime 8)))
(assert (not (is-prime 9)))

(def prime-mask (apple/jit ``λN. (λn.¬((∨)/ₒ #f ([(n|x)=0]'(⍳ 2 (⌊(√(ℝn))) 1))))'(irange 2 N 1)``))
(assert (deep= (prime-mask 9) @[true true false true false true false false]))

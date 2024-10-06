import apple

p=apple.jit("λn.¬((∨)/ₒ #f ([(n|x)=0]'(⍳ 2 (⌊(√(ℝn))) 1)))")
assert not(p(8))
assert p(7)

import numpy as np

d=apple.jit("λxs. ⸎n ⟜ 𝓉 xs; }:((*)`(𝒻 (ℝn-1) 0 n) xs)")
assert (d(np.array([1.,2,1]))==np.array([2.,2])).all()

xs=np.array([[0.,4,2],[0,1,3]])

def softmax(x):
    exp_element=np.exp(x-x.max())
    return exp_element/np.sum(exp_element,axis=0)

ssoftmax=apple.jit('''
λxs.
  { m ⟜ (⋉)/* _1 xs; a ⟜ [e:(x-m)]`{0} xs
  ; sum ← [(+)/x]
  ; n ⟜ sum`{1} (a::M float)
  ; |:(([(%x)'y]`{0,1} n a))
  }
''')
assert (ssoftmax(xs)==softmax(xs)).all()

luhn=apple.jit('''
λxs.
  { digitSum ← [?x>10,.x-9,.x]
  ; t ← (+)/ [digitSum (x*y)]`(~(}:xs)) (}: (cyc. ⟨2,1::int⟩ 8))
  ; 10-(t|10)=}.xs
  }
''')
assert luhn(np.array([4,0,1,2,8,8,8,8,8,8,8,8,1,8,8,1]))

def unstring(isbn):
    return np.array([int(c) for c in isbn.replace('-','')])

isbn13=apple.jit('''
λxs. {t ← (+)/ (*)`xs (}:(cyc. ⟨1,3::int⟩ 7)); (t|10)=0}
''')

assert isbn13(unstring("978-0596528126"))
assert not(isbn13(unstring("978-1788399083")))

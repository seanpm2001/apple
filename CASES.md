- [ ] fold-of-seed on scalar?
- [ ] fold-of-array
- [ ] scan-of-array
```
 > \xs.\ys.[(+)`x y]Λ xs
λxs. (λys. ((λx. (λy. ((+) ` x y))) Λ xs)) : ( IsNum c ) :=> Arr (i + 1 `Cons` sh) (Vec i c) → a → Arr (i + 1 `Cons` sh) (Vec i c)
 > \xs.\ys.[(+)`x y]Λ (xs::M int)
1:9: could not unify 'int' with 'Vec i c' in expression 'xs :: Arr (i × j) int'
```
- [ ] rank for scalars...
  - [ ] : 0.0 (size)
- [ ] scan-of-tup
- [ ] fold-tup
- [x] snoc array, cons array
- [ ] fold, producing tuple
- [ ] filter-on-array
- [ ] zip on array?
- [x] don't crash when stack-allocated tuples, arrays containing bools
- [x] equality on arrays
  - [ ] equality on tup
# Types
- [ ] scan-with-seed accept differently typed seed
- [ ] fold-with-seed generalize type
- [ ] also the folds ^ are backwards lol
- [ ] `hasbits` instance for boolean arrays?

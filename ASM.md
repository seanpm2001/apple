- https://developer.arm.com/documentation/dui0056/d/using-the-procedure-call-standard
- [ ] floor function: https://stackoverflow.com/a/37573707/11296354
    -- check parity: AND with 00010 or w/e
- [ ] note: fused multiply-add etc. for doubles
- [ ]  https://disasm.pro/
- [ ] sign by parity: AND with 0x1 to find parity, then use this to set sign bit? lol.
  (-1)^n
- [ ] avx512 has: https://www.felixcloutier.com/x86/vexp2pd
- [ ] https://www.felixcloutier.com/x86/leave
- [ ] cneg is cool.
- [ ] https://learn.microsoft.com/en-us/cpp/build/arm64-windows-abi-conventions?view=msvc-170#floating-pointsimd-registers
- [ ] https://developer.arm.com/documentation/dui0801/a/Advanced-SIMD-and-Floating-point-Programming/Views-of-the-Advanced-SIMD-register-bank-in-AArch64-state
- [ ] https://developer.arm.com/documentation/ddi0602/2024-09/Base-Instructions/CBLE--immediate---Compare-signed-less-than-or-equal-immediate-and-branch--an-alias-of-CB-cc---immediate--
- [ ] Special instructions: Cbcc (cble, smin)
- [ ]
```
sysctl hw.optional.arm.FEAT_FP16
sysctl -a | rg '^hw\.optional'
```
# Min/max
- [ ] http://web.archive.org/web/20130821015554/http://bob.allegronetwork.com/prog/tricks.html
  - [ ] quick absolute value
  - [ ] min/max?
- [ ] http://graphics.stanford.edu/~seander/bithacks.html
- [ ] https://stackoverflow.com/questions/227383/how-do-i-programmatically-return-the-max-of-two-integers-without-using-any-compa
- [ ] https://stackoverflow.com/questions/476800/comparing-two-integers-without-any-comparison?noredirect=1&lq=1

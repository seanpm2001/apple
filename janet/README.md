Only works on vectors, may crash ingloriously on higher-rank inputs.

```
jpm install --local
jpm -l janet -e '(import apple)' -r
repl:2:> (def moving-average (apple/jit ``([((+)/x)%ℝ(:x)]\`7)``))
<jit 0x6000014240C0>
repl:3:> (moving-average @[1.0 2.0 3.0 4.0 5.0 6.0 7.0 8.0 9.0 10.0])
@[4 5 6 7]
```

# Documentation

```janet
repl:1:> (import apple)
@{_ @{:value <cycle 0>} apple/jit @{:private true} apple/tyof @{:private true}}
repl:2:> (doc apple)


    module (native)
    /Users/vanessa/dev/haskell/apple/janet/jpm_tree/lib/apple.so

    no documentation found.


nil
repl:3:> (doc apple/jit)


    cfunction

    Compile source string into Janet callable


nil
```

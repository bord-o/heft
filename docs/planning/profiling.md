# Profiling

All ran after building --rel with `hyperfine 'dune exe heft --rel'`

before: (baseline for everything)
`
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel'
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      7.083 s ±  0.161 s    [User: 6.722 s, System: 0.361 s]
  Range (min … max):    6.789 s …  7.228 s    10 runs
`

## Monomorphic compare in kernel

Here I'm trading out OCaml's polymorphic 'compare' function for monomorphic ones made by ppx_deriving.ord

after:
`
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel'
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      7.431 s ±  0.217 s    [User: 7.071 s, System: 0.360 s]
  Range (min … max):    6.962 s …  7.699 s    10 runs
`

I guess it slowed things down, unexpected, but ok.

## Monomorphic equality in kernel

Same as above but with ppx_deriving.eq where applicable. I reverted the ord changes before doing this.

I changed quite a few compare x y = 0 calls, as well as structural equality in some places and List.equals instead.

after:
`
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel'
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      9.896 s ±  0.176 s    [User: 9.540 s, System: 0.355 s]
  Range (min … max):    9.522 s … 10.050 s    10 runs
`

This seems to have slowed things down, likely the structural equality is just simply better in a lot of these cases

I'm going to try with ppx_compare now

after:
`
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel'
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      7.597 s ±  0.197 s    [User: 7.216 s, System: 0.380 s]
  Range (min … max):    7.230 s …  7.918 s    10 runs
`

and now with leaving in the structural equality optimization but using the ppx for the rest:

after:
`
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      7.092 s ±  0.149 s    [User: 6.721 s, System: 0.371 s]
  Range (min … max):    6.772 s …  7.249 s    10 runs
`

and now using the ppx for comparisons too:

after:
`
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel'
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      6.930 s ±  0.187 s    [User: 6.549 s, System: 0.381 s]
  Range (min … max):    6.663 s …  7.211 s    10 runs
`

A small speedup, I'll leave it in for now but not sure this is worth it really.

One more try, this time keeping poly compare/eq but not using compare x y = 0 

after:
`
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel'
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      7.215 s ±  0.162 s    [User: 6.848 s, System: 0.366 s]
  Range (min … max):    6.956 s …  7.437 s    10 runs
`

Strange that this isn't faster, I'll just keep what I have and revisit this after more pressing optimizations

## Quieting printing functions

Lets make a global reference to control accumulation of unused formatting during search and when proofs complete

after
`
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel'
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      2.935 s ±  0.045 s    [User: 2.630 s, System: 0.303 s]
  Range (min … max):    2.870 s …  2.996 s    10 runs
`

This shows a ton of our time (>50%) is spent on formatting. We need a good way to control this, as you only really want the proof you're actively working on to give this information

Ultimately I'll trade out the mutable reference for either using the prove function as a source of truth through an effect handler, or maybe something else

## Deduplicate rules_from_def in simplifiers

after
`
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel' --warmup 1
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      1.267 s ±  0.007 s    [User: 0.971 s, System: 0.297 s]
  Range (min … max):    1.257 s …  1.278 s    10 runs
`

Another huge win

after using an effect instead of mutable ref, we get this

after
`bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel' --warmup 1
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      1.358 s ±  0.029 s    [User: 1.027 s, System: 0.330 s]
  Range (min … max):    1.329 s …  1.397 s    10 runs
`

A bit of overhead added but I'm happy with this because it keeps away from global state, I might use an effect level cache for this type of thing in the future anyway

## Inlining + hand rolled type/term eq

before
```
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel' --warmup=1
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      1.523 s ±  0.012 s    [User: 1.162 s, System: 0.359 s]
  Range (min … max):    1.508 s …  1.541 s    10 runs

```

after
```
bordo@brick:~/Git/heft $ hyperfine 'dune exe heft --rel' --warmup=1
Benchmark 1: dune exe heft --rel
  Time (mean ± σ):      1.502 s ±  0.016 s    [User: 1.162 s, System: 0.340 s]
  Range (min … max):    1.468 s …  1.523 s    10 runs

```

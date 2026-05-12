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

## Baseline with quiet theories tests
```
 To display the perf.data header info, please use --header/--header-only options.
#
#
# Total Lost Samples: 0
#
# Samples: 883  of event 'cycles:P'
# Event count (approx.): 3153703004
#
# Overhead  Symbol                                      IPC   [IPC Coverage]
# ........  ..........................................  ....................
#
     9.06%  [.] Heft.Rewrite.go_877                     -      -            
            |
            ---Heft.Rewrite.go_877
               |          
                --1.51%--Heft.Rewrite.go_877

     6.34%  [.] Heft.Rewrite.term_match_750             -      -            
            |
            ---Heft.Rewrite.term_match_750
               |          
                --0.70%--Heft.Rewrite.go_877

     6.24%  [.] _int_malloc                             -      -            
            |          
            |--3.24%--asm_exc_page_fault
            |          
             --2.76%--_int_malloc
                       |          
                        --2.64%--__libc_malloc2
                                  alloc_for_stack (inlined)
                                  alloc_size_class_stack_noexc
                                  |          
                                   --0.81%--caml_alloc_stack
                                             Heft.Tactic.798

     5.81%  [k] __irqentry_text_end                     -      -            
            |
            ---__irqentry_text_end
               |          
                --5.47%--_int_malloc
                          __libc_malloc2
                          alloc_for_stack (inlined)
                          alloc_size_class_stack_noexc (inlined)
                          |          
                           --1.51%--caml_alloc_stack
                                     |          
                                      --1.29%--Heft.Tactic.798

     4.74%  [.] compare_val                             -      -            
            |          
            |--3.81%--do_compare_val (inlined)
            |          compare_val
            |          
             --0.81%--compare_val

     3.59%  [.] Heft.Rewrite.rewrite_at_root_inner_850  -      -            
            |
            ---Heft.Rewrite.rewrite_at_root_inner_850
               |          
                --0.59%--Heft.Rewrite.rewrite_at_root_inner_850

     3.22%  [.] caml_perform                            -      -            
            |
            ---caml_perform
               |          
                --2.41%--caml_runstack
                          caml_runstack

     2.45%  [k] native_irq_return_iret                  -      -            
            |          
             --2.10%--_int_malloc
                       __libc_malloc2
                       alloc_for_stack (inlined)
                       alloc_size_class_stack_noexc

     1.85%  [.] caml_scan_stack                         -      -            
            |          
             --1.62%--scan_stack_frames (inlined)
                       caml_scan_stack

```

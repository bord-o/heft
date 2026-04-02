# PPX Usage Examples

```ocaml

[%%inductive
type nat = 
    | Zero 
    | Suc of nat
]

let%subtype int (p : (nat * nat) pair) =
    match p with
    | Pair (a, b) ->
        a = 0n || b = 0n
    
let match_term = [%term 
    match (n:nat) with
    | Zero -> nil
    | Suc (n':nat) -> cons 0n nil
]

let%primrec plus (n:nat) (m:nat) =
    match n with
    | Zero -> m
    | Suc (n':nat) -> Suc (plus n' m)

let%def plus2 (n:nat) = plus n 2n
```

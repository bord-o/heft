open Heft
open Kernel
open Tactic
open Auto

let%primrec sum_upto (n : nat) : nat =
  match n with Zero -> 0n | Suc n' -> plus (Suc n') (sum_upto n')

let%thm sum_upto_test = sum_upto 4n = 10n

and proof =
  begin
    simp
  end
  [@quiet]

let auto = with_no_automation_trace auto_dfs

let%thm mult_anil (n : nat) = mult n 0n = 0n

and proof =
  begin
    induct @>> auto
  end
  [@quiet] [@simp]

let%thm mult_sucr (n : nat) (m : nat) = mult n (Suc m) = plus n (mult n m)

and proof =
  begin
    induct
    >>= [
          auto;
          intros /* "hIH" >> simp >> apply_at "eq_cong"
          >> with_repeat @@ ac_norm "plus"
          >> refl;
        ]
  end
  [@quiet]

let%thm mult_comm (n : nat) (m : nat) = mult n m = mult m n

and proof =
  begin
    noop >> induct
    >>= [
          auto;
          noop >> intros /* "hIH" >> simp >> rewrite_at "mult_sucr" >> refl;
        ]
  end
  [@quiet]

let%thm schoolboy (n : nat) = mult 2n (sum_upto n) = mult n (Suc n)

and proof =
  begin
    induct
    >>= [
          simp;
          intros /* "hIH"
          >> rewrite_at ~position:1 "mult_comm"
          >> with_repeat @@ with_first @@ rewrite_at ~position:1 "mult"
          >> beta
          >> with_first (with_named_rule [ "hIH" ] @@ with_flip_rules rewrite)
          >> simp
          >> with_repeat @@ ac_norm "plus"
          >> refl;
        ]
  end
  [@quiet]

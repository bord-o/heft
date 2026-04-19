open Heft
open Kernel

let () = print_endline "initializing theory lists"
let a = make_vartype "a"
let list_ty = TyCon ("list", [ a ])
let list_a = TyCon ("list", [ a ])

[%%inductive type 'a list = Nil | Cons of 'a * 'a list]

let%primrec length (l : 'a list) : nat =
  match l with Nil -> Zero | Cons (x, xs) -> Suc (length xs)

let _ = length

let%primrec append (xs : 'a list) (ys : 'a list) : 'a list =
  match xs with Nil -> ys | Cons (z, zs) -> Cons (z, append zs ys)

let _ = append

let%primrec reverse (l : 'a list) : 'a list =
  match l with Nil -> Nil | Cons (x, xs) -> append (reverse xs) [ x ]

let _ = reverse

let%primrec insert (l : nat list) (n : nat) : nat list =
  match l with
  | [] -> Cons (n, Nil)
  | x :: xs -> if nat_le x n then x :: insert xs n else n :: x :: xs

let%primrec isort (l : nat list) : nat list =
  match l with Nil -> Nil | Cons (x, xs) -> insert (isort xs) x

let%primrec sorted (l : nat list) : bool =
  match l with
  | Nil -> true
  | Cons (x, xs) ->
      (match (xs : nat list) with Nil -> true | Cons (y, ys) -> nat_le x y)
      && sorted xs

let%primrec take (n : nat) (l : nat list) : nat list =
  match n with
  | Zero -> Nil
  | Suc n' -> (
      match l with Nil -> Nil | Cons (x, xs) -> Cons (x, take n' xs))

let%primrec drop (n : nat) (l : nat list) : nat list =
  match n with
  | Zero -> l
  | Suc n' -> ( match l with Nil -> Nil | Cons (x, xs) -> drop n' xs)

let%primrec merge_aux (fuel : nat) (xs : nat list) (ys : nat list) :
    nat list option =
  match fuel with
  | Zero -> None
  | Suc left -> (
      match xs with
      | None -> Some ys
      | Cons (h, t) -> (
          match ys with
          | Nil -> Some (Cons (h, t))
          | Cons (y', ys') -> (
              if nat_lt h y' then
                match (merge_aux left t ys : nat list option) with
                | None -> None
                | Some zs -> Some (Cons (h, zs))
              else
                match (merge_aux left xs ys' : nat list option) with
                | None -> None
                | Some zs -> Some (Cons (y', zs)))))

let%def merge (xs : nat list) (ys : nat list) : nat list =
  match
    (merge_aux (Suc (plus (length xs) (length ys))) xs ys : nat list option)
  with
  | None -> Nil
  | Some z -> z

let%primrec merge_sort_aux (fuel : nat) (xs : nat list) : nat list option =
  match fuel with
  | Zero -> None
  | Suc left ->
      if nat_le (length xs) 1n then Some xs
      else
        (fun (half_length : nat) ->
          match
            (merge_sort_aux left (take half_length xs) : nat list option)
          with
          | None -> None
          | Some left -> (
              match
                (merge_sort_aux left (drop half_length xs) : nat list option)
              with
              | None -> None
              | Some right -> Some (merge left right)))
          (div (length xs) 2n)

let%def merge_sort (xs : nat list) : nat list =
  match (merge_sort_aux (Suc (length xs)) xs : nat list option) with
  | None -> Nil
  | Some z -> z

let list_def = Hashtbl.find the_inductives "list"
let nil = make_const "Nil" [] |> Result.get_ok
let cons = make_const "Cons" [] |> Result.get_ok
let length = make_const "length" [] |> Result.get_ok
let append = make_const "append" [] |> Result.get_ok
let reverse = make_const "reverse" [] |> Result.get_ok

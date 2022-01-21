module Tuto1

type filename = string

let canWrite (f: filename) =
    match f with
    | "tmp" -> true
    | _ -> false

let canRead (f: filename) =
    canWrite f 
    ||
    f = "README"

let readable = f:filename{canRead f}
let writable = f:filename{canWrite f}

(*
val read : readable -> ML string
let read f = FStar.IO.print_string ("Dummy read of " ^ f ^ "\n"); f
*)

val append : #a:Type -> list a -> list a -> Tot (list a)
let rec append #a l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append #a tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]

val map: ('a -> FStar.All.ML 'b) -> list 'a -> FStar.All.ML (list 'b) 
let rec map f l=
    match l with
    | [] -> []
    | hd :: tl -> (f hd) :: (map f tl)

let print_list l = map FStar.IO.print_string l
    
let _ = print_list ["42"; "69"; "420"; "\n"]

let rec find #a (f: a -> bool) (l: list a):
    Tot (option (x: a{f x})) =
    match l with 
    | [] -> None
    | hd :: tl -> if f hd then Some hd else find f tl

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

(* This is to justify omitting the Nil constructor in the match in `nth` *)
let length_null #a (l: list a) :
    Lemma (requires (0 < length l))
          (ensures (Cons? l)) = ()

let rec nth #a (l: list a) (n: nat{n < length l}) : a =
    match l with 
    | hd :: tl -> if n = 0 then hd else nth tl (n - 1)

let rec fibo (n: nat): Tot (m:nat{m >= n /\ m >= 1}) =
    if n <= 1 then 1
    else fibo (n - 2) + fibo (n - 1)

let rec fib a b (n: nat): Tot nat (decreases n) =
    match n with 
    | 0 -> a
    | _ -> fib b (a + b) (n - 1)


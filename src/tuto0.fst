module Tuto0

open FStar.Mul

let even = x:int{x % 2 = 0}
let odd = x:int{x % 2 = 1}

let twice (x:int) = (2 * x <: even)

let max (x:int) (y:int): (z:int{z >= x && z >= y && (z = x || z = y)}) =
    if x > y then x
    else y

let rec fibo (n: nat): Tot (m:nat{m >= n /\ m >= 1}) =
    if n <= 1 then 1
    else fibo (n - 2) + fibo (n - 1)

let fibo_positive (n: nat): unit = assert (fibo n > 0)

let sqr_positive (x: int) = assume (x <> 0); assert (x * x > 0)

let rec length #a (l: list a): (n: nat{n > 0 \/ Nil? l}) =
    match l with 
    | [] -> 0
    | _ :: tl -> 1 + (length tl)


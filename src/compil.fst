module Compil

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

let rec nth #a (l: list a) (n: nat{n < length l}) : a =
    match l with 
    | hd :: tl -> if n = 0 then hd else nth tl (n - 1)

type deBruijn =
    | Var: nat -> deBruijn
    | Lambda: t:deBruijn -> deBruijn
    | App: deBruijn -> deBruijn -> deBruijn

let rec genClosure (t: deBruijn) (n: nat) =
    match t with 
    | Var i -> i < n
    | Lambda t' -> genClosure t' (n + 1)
    | App t' t'' -> (genClosure t' n) && (genClosure t'' n)

let isClosed (t: deBruijn) = genClosure t 0

let rec genClosure_trans_step (t: deBruijn) (n: nat):
    Lemma (requires (genClosure t n))
          (ensures (genClosure t (n + 1))) =
    match t with 
    | Var _ -> ()
    | Lambda t' -> genClosure_trans_step t' (n + 1)
    | App t' t'' -> genClosure_trans_step t' n; genClosure_trans_step t'' n

let rec genClosure_trans (t: deBruijn) (n: nat) (i: nat{i > n}):
    Lemma (requires (genClosure t n))
          (ensures (genClosure t i)) =
    if i = n + 1 then () 
    else 
        genClosure_trans t n (i - 1); 
        genClosure_trans_step t (i - 1);
        ()

let closed_universal (t: deBruijn{isClosed t}) (n: nat) : 
    Lemma (ensures (genClosure t n)) = 
    if n = 0 then () else genClosure_trans t 0 n

let rec substitution (t: deBruijn) (idx: nat) (u: deBruijn): deBruijn =
    match t with 
    | Var n -> if n = idx then u else t
    | Lambda t' -> Lambda (substitution t' (idx + 1) u)
    | App t' t'' -> App (substitution t' idx u) (substitution t'' idx u)

let closure_lambda_aux (n: nat) (t: deBruijn{(genClosure t n) /\ (Lambda? t)}):
    Lemma (ensures (genClosure (Lambda?.t t) (n + 1))) = 
    match t with 
    | Lambda t' -> ()

let rec subst_clos_aux (n: nat) (t: deBruijn{genClosure t n}) (u: deBruijn):
    Lemma (ensures ((substitution t n u) = t)) (decreases %[t; n]) =
    match t with 
    | Var i -> ()
    | App t' t'' -> subst_clos_aux n t' u; subst_clos_aux n t'' u
    | Lambda t' -> subst_clos_aux (n + 1) t' u

let subst_clos (n: nat) (t: deBruijn{isClosed t}) (u: deBruijn):
    Lemma (ensures ((substitution t n u) = t)) (decreases %[t; n]) =
    closed_universal t n;
    match t with 
    | Var i -> ()
    | App t' t'' -> subst_clos_aux n t' u; subst_clos_aux n t'' u
    | Lambda t' -> subst_clos_aux (n + 1) t' u

let rec subst_mult_aux (t: deBruijn) (idx: nat) 
    (u: list deBruijn): deBruijn =
    let l = length u in
    match t with 
    | Var n -> 
        if (n >= idx) && (n < l + idx) then nth u (n - idx)
        else t
    | Lambda t' -> 
        Lambda (subst_mult_aux t' (idx + 1) u)
    | App t' t'' -> 
        App (subst_mult_aux t' idx u) (subst_mult_aux t'' idx u)

let substMult (t: deBruijn) (idx: nat) (u: list deBruijn) =
    subst_mult_aux t idx u

let rec subst_mult_nil (t: deBruijn) (idx: nat):
    Lemma (ensures ((substMult t idx []) = t)) =
    match t with 
    | Var n -> () 
    | Lambda t' -> 
        subst_mult_nil t' (idx + 1)
    | App t' t'' -> 
        subst_mult_nil t' idx; subst_mult_nil t'' idx

let rec subst_mult_wd (t: deBruijn) (idx: nat) (u: deBruijn):
    Lemma (ensures (
        substitution t idx u = substMult t idx [u]
    )) = 
    match t with 
    | Var i -> ()
    | App t' t'' -> 
        subst_mult_wd t' idx u; subst_mult_wd t'' idx u
    | Lambda t' -> subst_mult_wd t' (idx + 1) u

let rec subst_mult_close (i: nat) (t: deBruijn{genClosure t i})
    (u: list deBruijn) :
    Lemma (ensures ((substMult t i u) = t))
    (decreases %[t; i]) = 
    match t with
    | Var n -> ()
    | App t' t'' -> subst_mult_close i t' u; subst_mult_close i t'' u
    | Lambda t' -> subst_mult_close (i + 1) t' u

let rec list_closed (l: list deBruijn) (n: nat) =
    match l with
    | [] -> True
    | t :: tl -> (genClosure t n) /\ (list_closed tl n)

let rec subst_mult_pc (t: deBruijn) (n: nat) 
    (ul: (list deBruijn){list_closed ul n}):
    Lemma (ensures (
        genClosure (substMult t n ul) n
    )) = 
    admit()

let rec subst_mult_master (t: deBruijn) (n: nat)
    (ul: (list deBruijn){list_closed ul n}) (u: deBruijn) :
    Lemma (ensures (
        (substMult t n (u :: ul)) = (substitution (substMult t (n + 1) ul) n u)
    )) = 
    match ul with 
    | [] -> 
        subst_mult_nil t n; 
        subst_mult_pc t (n + 1) []; 
        subst_mult_wd t n u; ()
    | _ -> admit()
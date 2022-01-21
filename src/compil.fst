module Compil

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
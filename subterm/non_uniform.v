From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst.

Require Import Arith.PeanoNat.
Import List Nat Bool.

(* duplicates marcels code? *)

Fixpoint countOfCtor (indref maxparam :nat) (c:term) : bool * nat :=
  match c with
    tRel _ => (false, maxparam)
  | tProd _ t1 t2 =>
    let (b1, v1) := countOfCtor indref maxparam t1 in
    let (b2, v2) := countOfCtor (S indref) maxparam t2 in
    (false, min v1 v2)
  | tApp (tRel m1) tm =>
    if (m1 =? indref)
    then (match tm with
          | (tRel m2) =>
            let r := if (m2 =? indref - 1) then 1 else 0
            in (r <? maxparam, r)
          | _ => (false, 0)
    end)
    else (false, maxparam)

  | tApp ta (tRel m) =>
    let (b, r) := countOfCtor indref maxparam ta in
    if (b && (m =? (indref - r - 1)))
    then (true, min (S r) maxparam)
    else (false, min r maxparam)
  | tApp ta tl =>
    let (b1, v1) := countOfCtor indref maxparam ta in
    let (b2, v2) := countOfCtor (S indref) maxparam tl in
    (false, min v1 v2)
  | _ => (false, maxparam)
  end.

Definition getParamCount (ind:one_inductive_body) (n0:nat) : nat :=
  fold_left (fun m c => min m (snd (countOfCtor 0 m (snd(fst c))))) ind.(ind_ctors) n0.

Definition getPCount (ind:mutual_inductive_body) (c:nat) : option nat :=
  match nth_error ind.(ind_bodies) c with
    None => None
  | Some b => Some (getParamCount b ind.(ind_npars))
  end.

From MetaCoq.PCUIC Require TemplateToPCUIC PCUICToTemplate.
From MetaCoq.Template Require Import config monad_utils utils TemplateMonad.
From MetaCoq.Template Require Ast.
Import MCMonadNotation String.

Definition getP (tm : Ast.term)
  : TemplateMonad unit
  := match tm with
     | Ast.tInd ind0 univ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
            c <- tmEval lazy (getPCount (TemplateToPCUIC.trans_minductive_body decl) ind0.(inductive_ind));;
            tmPrint c
     | _ => tmFail "not inductive"
    end.


Inductive nnat (A : Type) : Type :=
  n_zero : nnat A
| n_one : (nat -> nnat (list A)) -> nnat A.

Inductive finn A : list(A) -> nat -> Type :=
  F1n : forall (l : list A) (n : nat), finn A l (S n)
| FSn : let p := A in forall (l : list p) (n : nat), finn p l n -> finn p l (S n).

From MetaCoq.Template Require Import All.
MetaCoq Run (getP <%nnat%>).
MetaCoq Run (getP <%finn%>).

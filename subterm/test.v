From Local Require Import subterm.

From MetaCoq.Template Require Import config monad_utils utils TemplateMonad.
From MetaCoq.Template Require Ast BasicAst.
Import MCMonadNotation.

Require Import String List.
Import ListNotations.

Require Import Equations.Equations.

Definition inductive_printer (tm : Ast.term)
  : TemplateMonad unit
  :=  match tm with
     | Ast.tInd ind0 _ =>
       d <- tmQuoteInductive (BasicAst.inductive_mind ind0);;
       tmPrint d
     | _ => tmFail "sorry"
     end.

Section Test.
  Variable p : Type.
  Variable pc : p.
  Inductive test : p -> Type:= .
End Test.

From MetaCoq.Template Require Import All.

MetaCoq Run (inductive_printer <%test%>).

MetaCoq Run (inductive_printer <%list%>).
MetaCoq Run (subterm <%list%>).
(*Derive Subterm for list.*)

MetaCoq Run (inductive_printer <%list_direct_subterm%>).
Print list_direct_subterm.

Inductive even : nat -> Prop :=
| even_O : even 0
| even_S : forall n, even n -> even (S n)
with  dummy : nat -> Prop :=
| dummyc : forall n, dummy n
with odd : nat -> Prop :=
| odd_S : forall n, even n -> odd (S n).


MetaCoq Run (inductive_printer <%even%>).

MetaCoq Run (subterm <%odd%>).
Print odd_direct_subterm.


Inductive finn A : list(A) -> nat -> Type :=
  F1n : forall (l : list A) (n : nat), finn A l (S n)
| FSn : let p := list A in forall (l : p) (n : nat), finn A l n -> finn A l (S n).

Inductive fin : nat -> Type :=
  F0 : forall n, fin n
| FS : forall n : nat, fin n -> fin (S n).

MetaCoq Run (inductive_printer <%finn%>).

MetaCoq Run (subterm <%finn%>).
(*Derive Subterm for finn.*)
MetaCoq Run (inductive_printer <%finn_direct_subterm%>).
Print finn_direct_subterm.


MetaCoq Run (p <- tmQuote fin;; tmPrint p ).

Definition scope := nat.
Inductive scope_le : scope -> scope -> Set :=
| scope_le_n : forall {n m}, n = m -> scope_le n m
| scope_le_S : forall {n m}, scope_le n m -> scope_le n (S m)
| scope_le_map : forall {n m}, scope_le n m -> scope_le (S n) (S m)
.

MetaCoq Run (subterm <%scope_le%>).

Print scope_le_direct_subterm.
(*
Inductive
scope_le_direct_subterm
    : forall H H0 H1 H2 : scope, scope_le H H0 -> scope_le H1 H2 -> Set :=
    scope_le_S_subterm0 : forall (n m : scope) (H : scope_le n m),
                          scope_le_direct_subterm n m n (S m) H (scope_le_S H)
  | scope_le_map_subterm0 : forall (n m : scope) (H : scope_le n m),
                            scope_le_direct_subterm n m 
                              (S n) (S m) H (scope_le_map H)
*)

Inductive nnat (A : Type) : Type :=
  n_zero : nnat A
| n_one : (nat -> nnat (list A)) -> nnat A.

Fail MetaCoq Run (subterm <%nnat%>).

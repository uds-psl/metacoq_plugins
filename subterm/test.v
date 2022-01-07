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
Print list_direct_subterm.

Inductive G : Set := guard (h:nat -> G).
MetaCoq Run (subterm <%G%>).
Print G_direct_subterm.
Inductive Rose (X:Type) : Set := tree (xs:List (Rose X)) (y:Rose X).
MetaCoq Run (subterm <%List%>).
Print List_direct_subterm.
MetaCoq Run (subterm <%Rose%>).
Print Rose_direct_subterm.

Inductive Vec (X:Set) : nat -> Set := NilVec : Vec X 0 | ConsVec (x:X) n (xs:Vec X n) : Vec X (S n).
Inductive RoseVec (X:Type) : Set := treeVec n (h:Vec (RoseVec X) n) (y:RoseVec X).
MetaCoq Run (subterm <%RoseVec%>).
Print RoseVec_direct_subterm.

Inductive RoseInd (X:Type) : nat -> Set := treeInd n (h:List (RoseInd X n)) (y:RoseInd X n): RoseInd X (S n).
MetaCoq Run (subterm <%RoseInd%>).
Print RoseInd_direct_subterm.

From MetaCoq.Translations Require Import param_all.
(* MetaCoq Run Derive Translations for List. *)
MetaCoq Run Derive Translations for Vec.

Inductive Rose_direct_subterm_nest : forall X : Type, Rose X -> Rose X -> Prop :=
	tree_subterm_nest0 : forall (X : Type) (h : List (Rose X)) (y : Rose X),
                    Rose_direct_subterm_nest X y (tree X h y)
  | tree_subterm_nest1 : forall (X : Type) (h : List (Rose X)) (y : Rose X),
                    forall (z:Rose X),
                      Listᴱ (Rose X) (fun x => x=z) h ->
                    Rose_direct_subterm_nest X z (tree X h y).

Inductive RoseInd_direct_subterm_nest
	: forall (X : Type) (H H0 : nat), RoseInd X H -> RoseInd X H0 -> Prop :=
    treeInd_subterm0_nest : forall (X : Type) (n : nat) 
                         (h : List (RoseInd X n)) 
                         (y : RoseInd X n),
                       RoseInd_direct_subterm_nest X n (S n) y (treeInd X n h y)
  | treeInd_subterm1_nest : forall (X : Type) (n : nat) 
                         (h : List (RoseInd X n)) 
                         (y : RoseInd X n),
                         forall (z:forall m, RoseInd X m),
                       Listᴱ (RoseInd X n) (fun x => x=z n) h ->
                       forall m,
                       (False + (m=n)) ->
                       RoseInd_direct_subterm_nest X m 
                         (S n) (z m) (treeInd X n h y).

Definition rose_subterm := fun A =>
  Relation_Operators.clos_trans (rose A)
                                (RoseInd_direct_subterm_nest A).


Inductive nonUniDepTest (A:Type) (N:nat) (*non-uni:*) (xs:list A) : bool -> nat -> Type :=
    | CD1: forall (H1:nonUniDepTest A N [] false 1) (a:A) (M:nat) (H2:nonUniDepTest A N [] false 0), nonUniDepTest A N xs true N
    (* . *)
    | CD2: forall (k:nat) 
    (* (f:forall (a:A), nonUniDepTest A N [] true 0) *)
    (* (g:forall b, nonUniDepTest A N [] b 0) *)
    (* (h:forall n b, nonUniDepTest A N [] b n) *)
    (a:A)
    (HA:nonUniDepTest A N (a::xs) true 0), nonUniDepTest A N xs false 1.
MetaCoq Run (subterm <%nonUniDepTest%>).
Print nonUniDepTest_direct_subterm.

From Equations Require Import Equations.

(* Derive Subterm for list. *)

Definition list_subterm := 
  fun A : Type => Relation_Operators.clos_trans (list A) (list_direct_subterm A).

Lemma well_founded_list_subterm : forall A : Type, WellFounded (list_subterm A).
Proof.
  solve_subterm.
Qed.

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons n : A -> vector A n -> vector A (S n).

Derive NoConfusionHom for vector.
(* Derive Subterm for vector. *)

MetaCoq Run (subterm <%vector%>).

Require Import sigma.

(* From MetaCoq.Template Require Import All. *)

Unset Strict Unquote Universe Mode.

MetaCoq Run (tmBind (pack_inductive <% vector %>) (tmMkDefinition "vector_packed")).
Print vector_packed.

Definition vector_subterm :=
  fun A : Type =>
    Relation_Operators.clos_trans (vector_packed A)
                              (fun x y : (vector_packed A) =>
                                 vector_direct_subterm A (pr1 x) (pr1 y) (pr2 x) (pr2 y)).

Lemma well_founded_vector_subterm : forall A : Type, WellFounded (vector_subterm A).
Proof.
  unfold vector_subterm, vector_packed.
  solve_subterm.
Qed.

Inductive fin (A : Type) : nat -> Type :=
| fin0 : forall n, fin A n
| finS : forall n, fin A n -> fin A (S n).

MetaCoq Run (pack_inductive <%fin%> >>= tmMkDefinition "fin_packed").
Print fin_packed.

MetaCoq Run (subterm <% fin %>).
Print fin_direct_subterm.


Definition fin_subterm := fun A =>
  Relation_Operators.clos_trans (fin_packed A)
                                (fun x y : (fin_packed A) =>
                                   fin_direct_subterm A (pr1 x) (pr1 y) (pr2 x) (pr2 y)).

Derive NoConfusionHom for fin.

Lemma well_founded_fin_subterm : forall A : Type, WellFounded (fin_subterm A).
Proof.
  unfold fin_subterm, fin_packed.
  solve_subterm.
Qed.

Inductive rose (A: Type) := rleaf (a: A) | rtree (l: list (rose A)).
MetaCoq Run (inductive_printer <%rose%>).
(* MetaCoq Run (subterm <%rose%>). *)
(* Print rose_direct_subterm. *)

(* MetaCoq Run (subterm <%nat%>). *)

Inductive nat_direct_subterm : nat -> nat -> Prop :=
    S_subterm0 : forall H H2 : nat, eq H H2 -> nat_direct_subterm H (S H2).

Inductive rose_direct_subterm (A : Type) : rose A -> rose A -> Prop :=
| C1 (t : rose A) l :
  let RIn := (fun x l => Exists (Relation_Operators.clos_refl (rose A) (rose_direct_subterm A) x) l) in
  RIn t l -> rose_direct_subterm A t (rtree A l).

(*
  choices:

  - the above
  - use Relation_Operators.clos_refl_trans instead
  - define rose_direct_subterm with 2 constructors for refl and trans
 *)

Definition rose_subterm := fun A =>
  Relation_Operators.clos_trans (rose A)
                                (rose_direct_subterm A).

Goal forall A t, rose_subterm A t (rtree A [rtree A [rtree A [t]]]).
Proof.
  intros.
  eapply Relation_Operators.t_step.
  eapply C1. econstructor.
  eapply Relation_Operators.r_step.
  eapply C1. econstructor.
  eapply Relation_Operators.r_step.
  eapply C1. econstructor.
  eapply Relation_Operators.r_refl.
Qed.

Print rose_direct_subterm.

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

(* Inductive fin : nat -> Type := *)
(*   F0 : forall n, fin n *)
(* | FS : forall n : nat, fin n -> fin (S n). *)

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

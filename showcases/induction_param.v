(* Inductive List (X:Set) : Set := Nil | Cons (x:X) (xs:List X).
Inductive rose (X:Type) : Set := tree (h:List (rose X)). *)
Inductive List (X:Type) : Type := Nil | Cons (x:X) (xs:List X).
Inductive rose (X:Type) : Type := tree (h:List (rose X)).

Require Import MetaCoq.Induction.MetaCoqInductionPrinciples.
MetaCoq Run Set Nested Inductives.

MetaCoq Run Scheme Induction for rose.
Print rose_ind_MC.

From MetaCoq.Translations Require Import param_all.
Unset Strict Unquote Universe Mode.

(* MetaCoq Run Derive full Parametricity for List. *)
(* Print Listᵗ. *)
(* MetaCoq Run Scheme Induction for rose.
Print rose_ind_MC0. *)
MetaCoq Run Derive Container for List.
MetaCoq Run Scheme Induction for rose.
Print rose_ind_MC0.
Print Listᵗ.
Print Listᵗ0.
MetaCoq Run Derive Container for rose. (* TODO: error List^t exists *)
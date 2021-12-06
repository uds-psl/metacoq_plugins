(* 
 * Define some inductive types  (they will be pickable)
 *)
 Require Import gherkin. 
 Require Import gentree.
 Require Import String List.

Inductive containerTestType := (* a dummy type which uses some containers *)
  A: option containerTestType -> containerTestType
| B.
(* Propositional Logic *)
Inductive form := Imp (a b: form) | Var (a: nat) | And (a b: form) | Or  (a b: form) | Bot.

(* Rose Trees *)
Inductive rosetree (A: Type)  :=
| leaf:  A -> rosetree A
| node: (list (rosetree A)) -> rosetree A.

(* More fun with containers *)
Inductive containerFun (A B: Type) :=
  contMe : option ( prod (option A) (option B)) -> containerFun A B.
(* Binary Trees *)
Inductive BinTree (A: Type)  := BinNode : A -> A -> BinTree A  | BinLeaf: A -> BinTree A . 

(* Binary Trees ML-Style (using prod) *)
Inductive mlBinTree2 (A: Type)  := mlBinNode2 : (prod A A) -> mlBinTree2 A. 

Inductive triple (A B C: Type) := tripleC: A -> B -> C -> triple A B C.
Inductive tripleAsContainer (A: Type) :=
  tcA : option (triple A nat nat) -> tripleAsContainer A
| tcB: tripleAsContainer A -> prod nat (option nat) -> tripleAsContainer A. 

Inductive strangetree (C A B: Type) :=
  tCon: strangetree C B A  -> strangetree C A B |
  tLeafA: A -> strangetree C A B .
Inductive listyfun A:=
  nilL: listyfun A
| one: A -> listyfun A |
consA: A -> (listyfun A) -> (listyfun A)  -> listyfun A.

Inductive doubleNat := dnO : doubleNat | dnS: doubleNat -> doubleNat -> doubleNat.
Inductive strangeInd (A: Type) := s0: A -> A -> A -> A -> A -> strangeInd A. 
Inductive specialtriple (A: Type) := spt: A -> A -> A -> specialtriple A.
(* uniform: 2 , nonuniform: 3*)
Inductive mix (A B C D E: Type) := mixA: mix A B C E D -> mix A B C D E. 

Inductive mixl (A B C D E F G H I: Type) := mixAl: mixl A B C E D I H G F -> mixl A B C D E F G H I.
Inductive inhabiNon (A: Type) := asimpl2:  inhabiNon A.
Inductive selfreference (A: Type) := sA: A -> selfreference A -> selfreference A.
Inductive selfreference' (A: Type) := sA':  selfreference' A -> A ->  selfreference' A.
Inductive tType := tA | tB | tC | tD.
Inductive inhabited (A: Type) := asimpl: A -> inhabited A.


(** These types can not be pickled just yet **)

Inductive Vector A: nat -> Type :=
| nilV: Vector A 0
| consV (n: nat): A -> Vector A n -> Vector A (S n).

Inductive Countdown : nat -> Type :=
| initCtr: Countdown 1000
| downCtr: forall n,Countdown (S n) -> Countdown n.
(** The plugin also does *not* support mutual inductive types **)
Inductive tree (A B: Type) := Tnode : A -> forest A B -> tree A B
with forest (A B: Type) :=
| Fleaf : B -> forest A B
| Fcons : tree A B -> forest A B -> forest A B.



MetaCoq Run Derive Pickle for nat.

MetaCoq Run Derive Pickle for bool. 
MetaCoq Run Derive Pickle for form. 
MetaCoq Run Derive Pickle for option. 
MetaCoq Run Derive Pickle for prod. 
MetaCoq Run Derive Pickle for strangetree. 
MetaCoq Run Derive Pickle for list. 
MetaCoq Run Derive Pickle for Ntree. 
MetaCoq Run Derive Pickle for triple.
MetaCoq Run Derive Pickle for listyfun. 
MetaCoq Run Derive Pickle for mlBinTree2.
MetaCoq Run Derive Pickle for mix.
MetaCoq Run Derive Pickle for tripleAsContainer. 
MetaCoq Run Derive Pickle for rosetree. 
MetaCoq Run Derive Pickle for strangeInd. 
MetaCoq Run Derive Pickle for doubleNat. 
MetaCoq Run Derive Pickle for specialtriple.

(* MetaCoq Run Derive pickle for containerFun with [<% option %>; <% prod %>]. *) 

MetaCoq Run Derive Unpickle for nat.
MetaCoq Run Derive Unpickle for bool. 
MetaCoq Run Derive Unpickle for form. 
MetaCoq Run Derive Unpickle for option. 
MetaCoq Run Derive Unpickle for prod. 
MetaCoq Run Derive Unpickle for strangetree. 
MetaCoq Run Derive Unpickle for list. 
MetaCoq Run Derive Unpickle for Ntree. 
MetaCoq Run Derive Unpickle for triple.
MetaCoq Run Derive Unpickle for listyfun. 
MetaCoq Run Derive Unpickle for mlBinTree2.
MetaCoq Run Derive Unpickle for mix.
MetaCoq Run Derive Unpickle for tripleAsContainer. 
MetaCoq Run Derive Unpickle for rosetree. 
MetaCoq Run Derive Unpickle for strangeInd. 
MetaCoq Run Derive Unpickle for doubleNat. 
MetaCoq Run Derive Unpickle for specialtriple.

From MetaCoq.Template Require Import All.
(* Example where the automatic inference of containered types fails, but the types can be supplied manually *)
Inductive T1 := tnull : T1.
Inductive T2 := ttest : T1 -> T2.
Inductive T3 := ttest2 : T2 -> T3.

Inductive T4 := ttest3 : T3 -> T4.
Require Import List.
Import ListNotations.
MetaCoq Run (Derive pickle for T4 with [<% T1 %>; <% T2 %>; <% T3 %>]).
MetaCoq Run (Derive unpickle for T4 with [<% T1 %>; <% T2 %>; <% T3 %>]).

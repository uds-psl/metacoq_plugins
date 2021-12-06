 Require Import gherkin. 
 Require Import gentree.
 Require Import String List Lia.
 Import ListNotations.
(** 
 * First we define some inducitve types
 *)
 Inductive form := Var (n: nat) | Imp (f1 f2: form) | Box (f: form) | And (f1 f2: form) .

Inductive mlbin (A: Type):= node: A *  A -> mlbin A | bleaf: A -> mlbin A .


Inductive Vector (A : Type) : nat -> Type :=
    nilV : Vector A 0
  | consV : forall n : nat, A -> Vector A n -> Vector A (S n).
Print Ntree. 
(* Let's generate a pickle function for form. 
   The generated function will embed forms into a general tree type called Ntree.

   Ltrees can either be a leaf with a natural number attached or a branch, that is a number and a list of subtrees 
                     * 4
                   /  | \
                  /   |  \
                 /    |   \
                * 3   2    1
   can be represented as NBranch 4 [NLeaf 3; NLeaf 2; NLeaf 1]
 *)
MetaCoq Run Derive Pickle for form.
(* When form is pickled, nat is automatically pickeled too, but not remembered yet.
   The nested inductives are currently only analyzed 1 level deep 
   (i.e. ind T := a :  T1 -> T ; ind T1 := t1: T2 -> T1 ; ind T2 , when trying to pickle T, it would not be inferred that T has to be picklable)
 *)
MetaCoq Run Derive Pickle for nat.
MetaCoq Run Derive Pickle for prod.
MetaCoq Run Derive Pickle for mlbin.

Fail MetaCoq Run Derive Pickle for Vector.
(* Let's take a look at the generated functions:
   They basically remember the constructor number and recursively pickle the constructors fields.

  Note that parameters are also dealt with.
*)
Print Pickle_form.
Print Pickle_mlbin.
(* The inverse function unpickle can also be generated. Since pickle must only be injective and not surjective,  it maps from Ntrees into option T.

 However this plugin has limitations: Types having indices (i.e. deduction systems, Vectors, etc.) can currently not be pickled, so Dark Dieter will have to pickle his type by hand.

Lots of interesting types are contained in moreExamples.v
 *)

MetaCoq Run Derive Unpickle for form. 
MetaCoq Run Derive Unpickle for nat.
MetaCoq Run Derive Unpickle for prod.
MetaCoq Run Derive Unpickle for mlbin.

(* Let's take a look at those too *)
Print Unpickle_form.

Fail MetaCoq Run Derive Unpickle for Vector.

(**
 * Now that we have the pickle functions all that is left to do inorder to proof countability / equality deciders is to show that the generated functions have a certain
 * cancellation property:
 * unpickle (pickle p)) = (Some p)
 * We can show this using an easy induction. It could be further automated by using some clever Ltac / could be generated automatically.
 *)
Lemma CancelNat : pcancel Pickle_nat Unpickle_nat. 
Proof.
  intro n. induction n.
   - reflexivity.
   - simpl Unpickle_nat.  rewrite IHn. auto.
Defined.

Lemma CancelProd (A: Type) pA upA (H1: pcancel pA upA) (B: Type) pB upB (H2: pcancel pB upB) : pcancel (Pickle_prod A pA B pB) (Unpickle_prod A upA B upB).  
Proof.
  intro p. induction p.
   - simpl Unpickle_prod. rewrite H1. rewrite H2. 
   reflexivity.
Defined.

Lemma CancelForm : pcancel Pickle_form Unpickle_form. 
Proof.
  intro f.
  induction f.
  -   simpl Unpickle_form. pose (CancelNat n). unfold Pickle_nat in e. (* This is a bit hard to do without automation, but could use some clever ltac / automatic generation of principles *)
      unfold Unpickle_nat in e. rewrite e. reflexivity.
  -   simpl Unpickle_form. rewrite IHf1.  rewrite IHf2. reflexivity.
  -   simpl Unpickle_form. rewrite IHf.  reflexivity.
  -   simpl Unpickle_form. rewrite IHf1. rewrite IHf2.  reflexivity.
  Show Proof.     
Defined.

Lemma CancelMlbin (A: Type) pA upA (H: pcancel pA upA) : pcancel (Pickle_mlbin A pA) (Unpickle_mlbin A upA). 
Proof.
  intro b.
  induction b.
  -   pose (CancelProd A pA upA H A pA upA H).  unfold pcancel in p0.  unfold Pickle_prod in p0. unfold Unpickle_prod in p0.
      simpl Unpickle_mlbin. simpl Pickle_mlbin.  
      rewrite (p0 p). reflexivity.
  -   cbv. rewrite H. reflexivity. 
Qed.

(** 
 * Now we can quite easily obtain equality deciders for the types.
 *)


Lemma EqDecMlbin (A: Type) (pA: Pickle A) upA (H: pcancel pA upA) : forall (x y: mlbin A), {x = y} + {x <> y}. 
Proof.
  intros x y.
  decide ((Pickle_mlbin A pA x) = (Pickle_mlbin A pA y)).
  left.  apply (f_equal (Unpickle_mlbin A upA)) in e. repeat rewrite (CancelMlbin A pA upA H) in e. inversion e. auto.
   right. intro. apply n. apply (f_equal (Pickle_mlbin A pA)) in H0. congruence.
Qed.


(**
   Since the equality decider proofs are quite generic, we use a short Ltac script to generate them.
 **)
Ltac prove_equality p up cancel := intros a b ; decide ((p a) = (p b)); [left;
                                                                         (match  goal with
    | [ H : ?a = ?b  |- _ ] => idtac H; apply (f_equal (up)) in H; repeat rewrite cancel in H; inversion H; reflexivity
    | _ => idtac
  end)

                                                                        |
                                                                        right; intro;
                                                                        (match  goal with
    | [ H : (?a) = (?b)  |- _ ] =>   apply (f_equal p) in H; congruence
    | _ => idtac
  end)
                                                                         
                                                                        ].

(** Yay! Now we can get an equality decider  for free
     
 *)
Lemma form_eq_dec: forall (f1 f2: form), {f1 = f2} + {f1 <> f2}.
Proof.
  prove_equality Pickle_form Unpickle_form CancelForm.
Defined.   

Lemma EqDecMlbin' (A: Type) (pA: Pickle A) upA (H: pcancel pA upA) : forall (x y: mlbin A), {x = y} + {x <> y}.
  
  prove_equality (Pickle_mlbin A pA) (Unpickle_mlbin A upA) (CancelMlbin A pA upA H).
Defined.


Definition form_bool_dec (f1 f2: form) := if form_eq_dec f1 f2 then true else false.
(* The generated equality deciders work as expected. *)
Compute (form_bool_dec (Var 10) (Var 11)). (* false *)
Compute (form_bool_dec (Imp (Var 10) (Var 400)) (Imp (Var 10) (Var 400))). (* true *)


(* We use the following notion of countability for a type
   with this notion of countability, the countability proofs are easier to obtain. 

 *)
Section Countability. 
Definition countable_list__T T := {f: nat -> list T | forall t, exists n, In t (f n)}.  
(*
  In the file gentree.v, it is proven that Ltrees can be embedded into list (nat * nat + nat)
  we can directly construct a list enumerator for this type. 
 *)
Definition listEnumerator (n: nat) : list ((nat * nat)+nat) :=

  (List.map (@inl (nat*nat) nat) (list_prod (seq 0 n) (seq 0 n))) ++ (List.map (@inr (nat*nat) nat) (seq 0 n)).

Lemma countableNatNatOpt : countable_list__T ((nat * nat)+nat).
  exists listEnumerator.
  intro t.
  - destruct t.
    destruct p.  exists (S (max n n0)). unfold listEnumerator. rewrite in_app_iff. left.
    apply in_map_iff. exists (n, n0).  rewrite list_prod_spec. split; auto. split.
    simpl fst. apply in_seq.  lia.
    simpl snd. apply in_seq. lia. 
    exists (S n). unfold listEnumerator. rewrite in_app_iff. right. apply in_map_iff. exists n. split; eauto. apply in_seq.  lia.
Defined.
(** We still need to proof, that if A is countable, so is list A *)
Section ListEnumerator.
  Variable (X: Type).
  Variable (L: nat -> list X).
  Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).
  Notation "[ s | p ∈ A ]" :=
    (map (fun p => s) A) (p pattern).
  
  Fixpoint L_list (n : nat) : list (list X) :=
	  match n
	  with
	  | 0 => [ [] ]
	  | S n => L_list n ++ [x :: L | (x,L) ∈ (cumul L n × L_list n)]
	  end.
End ListEnumerator.
Lemma  countable_list {X} : countable_list__T X -> countable_list__T (list X).
Proof.
  intros [L H].
  eexists (L_list X L).
  intro l.
  induction l.
  - exists 0. cbn. eauto.
  - destruct IHl as [n IH].  destruct (cumul_spec__T H a) as [m ?].
    exists (1 + n + m). cbn. intros. in_app 2.
    in_collect (a,l).
    all: eapply cum_ge'; eauto using L_list_cumulative; lia.
Defined.    
(** We show that having a pickle / unpickle function works well with list enumerators **)

(* Removes all None Elements from a list and deSomes the other *)
Fixpoint deOptionize {A: Type} (l: list (option A)) : list A :=
  match l with
    (Some x :: xr) => x::(deOptionize xr)
  | (_::xr) => deOptionize xr
  | nil => nil end.


Lemma deOptIn {A: Type} l (x: A): In x (deOptionize l) <-> In (Some x) l.
Proof.
  induction l. simpl deOptionize. tauto.
  split. intro. destruct a.
  simpl deOptionize in H. destruct H. rewrite H. left. auto. right. rewrite<- IHl. auto.
  right. apply IHl. apply H.
  intro. destruct H. rewrite H. simpl deOptionize. left. reflexivity. destruct a. simpl deOptionize. right. apply IHl. exact H. simpl deOptionize. apply IHl. exact H.
Qed.  
Lemma countableDecodeEncode (A B: Type)
      (code: A -> B)
      (decode: B -> option A)
      (H1:forall a, (decode (code a)) = Some a)
      (enumB: countable_list__T B)
  : countable_list__T A.
Proof.
  unfold enumerable__T.
  destruct enumB as [fb Hb].
  exists (fun n => (deOptionize (List.map decode (fb n)))).
  intro a. specialize (H1 a).
  specialize (Hb (code a)).
  destruct Hb. exists x. apply deOptIn. rewrite<- H1. apply in_map_iff. exists (code a).  split; tauto.
Defined.
(* Now we can show, that Ntrees are countable *)
Lemma enumLtree: countable_list__T Ntree. 
Proof.
  apply (@countableDecodeEncode Ntree (list ((nat*nat)+nat)) ntree_to_list (ntree_of_list [])  ).
  intro.
  pose (ntree_of_to_list [] [] a).
  rewrite app_nil_r in e.
  rewrite e.
  simpl ntree_of_list.
  reflexivity.
  apply countable_list.
  apply countableNatNatOpt. 
Defined.

(* With these lemmas in place, we can now obtain list counters for the types *)
Lemma form_countable: countable_list__T form.
  apply (@countableDecodeEncode form Ntree Pickle_form Unpickle_form CancelForm enumLtree).
Defined.

Lemma mlbin_countable (A: Type) (pA: Pickle A) (upA: Unpickle A) (H: pcancel pA upA)  : countable_list__T (mlbin A).
  apply (@countableDecodeEncode (mlbin A) Ntree (Pickle_mlbin A pA) (Unpickle_mlbin A upA) (CancelMlbin A pA upA H) enumLtree).
Defined.

Definition count_form (n: nat) := ( (proj1_sig (form_countable)) n).
Compute (count_form 7).

End Countability.

(** Finally let us take a look at rose trees **)
Inductive rose (A: Type) := rleaf (a: A) | rtree (l: list (rose A)).
Hypothesis roseInd' :
  forall A, forall (P: rose A -> Prop), (forall xs, (forall x, In x xs -> P x) -> P (rtree A xs)) -> (forall a, P (rleaf A a)) ->
                          forall (x: rose A), P x.
MetaCoq Run Derive Pickle for rose. 
MetaCoq Run Derive Unpickle for rose. 

MetaCoq Run Derive Pickle for list. 
MetaCoq Run Derive Unpickle for list. 

Print Pickle_rose.
Print Unpickle_rose.

(** Let us verify that the generated functions work as intended *)
Compute (Unpickle_rose nat Unpickle_nat (Pickle_rose nat Pickle_nat (rtree nat [rleaf nat 2; rtree nat [rleaf nat 1; rleaf nat 200]]))).
(* We need a stronger cancellation lemma for lists 
   (i.e. we do not need (Unpickle_A (Pickle_A a)) = Some a for every a 
   but only for the elements in the list *)
Lemma List_PCancel (A: Type) (pA: Pickle A) (upA: Unpickle A) (l: list A):
  (forall a, In a l -> (upA (pA a)) = Some a) -> (Unpickle_list A upA (Pickle_list A pA l)) = Some l.
Proof.
  intro.
  induction l.
  - cbv. auto.
  - simpl Pickle_list.  simpl Unpickle_list. rewrite IHl. rewrite H. reflexivity.
    auto. intros h H1. apply H. right. auto.
Qed.
(* Proving the cancellation property for rose is quite difficult.
 * It needs the stronger version of the cancellation lemma for Lists.
 *)

Lemma CancelRose (A: Type) (pA: Pickle A) (upA: Unpickle A) (H: pcancel pA upA):
  pcancel (Pickle_rose A pA) (Unpickle_rose A upA).
Proof.
  
  intro r.
  induction r using roseInd'.
  -  simpl Pickle_rose. unfold Unpickle_rose.  
     
    induction xs. simpl. reflexivity.
     
    destruct (Nat.eqb 1 1) eqn:h1.  destruct (Nat.eqb 0 1) eqn:h2. 
    + assert (Nat.eqb 0 1 = false) by eauto. congruence.
    +  cbv. cbn.  
       simpl.   simpl. unfold Unpickle_rose in IHxs. unfold Pickle_rose in IHxs.
     repeat rewrite (List_PCancel (rose A) (Pickle_rose A pA) (Unpickle_rose A upA)).
     rewrite (List_PCancel (rose A) (Pickle_rose A pA) (Unpickle_rose A upA)) in IHxs.

     cbn in IHxs. rewrite H0.   reflexivity.
     left. reflexivity.
     intros a1 Ha1. apply H0.
     right. auto.
     intros a1 Ha1. apply H0.
     right. auto.
    + inversion h1.
  -  cbv. rewrite H. reflexivity.
Qed.     

(* We now get decidability + countability for free *)
Lemma rose_countable (A: Type) (pA: Pickle A) (upA: Unpickle A) (H: pcancel pA upA): countable_list__T (rose A).
  apply (@countableDecodeEncode (rose A) Ntree (Pickle_rose A pA) (Unpickle_rose A upA) (CancelRose A pA upA H) enumLtree).
Defined.

Definition count_nat_rosetree (n: nat) := ( (proj1_sig (rose_countable nat Pickle_nat Unpickle_nat CancelNat)) n).

Lemma rose_eq_dec (A: Type) (pA: Pickle A) (upA: Unpickle A) (H: pcancel pA upA) : forall (r1 r2: rose A), {r1 = r2} + {r1 <> r2}.
Proof.
  prove_equality (Pickle_rose A pA) (Unpickle_rose A upA) (CancelRose A pA upA H).
Defined.   

(** That concludes our demo of the gherkin plugin,
    Some more examples of 'harder to pickle' types are contained in the file examples.v    
 **)

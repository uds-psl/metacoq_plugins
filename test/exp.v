Require Import Nat.

Inductive brtree A : nat -> Type :=
| Leaf (a : A) : brtree A 0
| Node (n : nat) (l : list (brtree A n)) : brtree A (S n).

Require Import MetaCoq.Induction.MetaCoqInductionPrinciples.

MetaCoq Run Set Nested Inductives.

MetaCoq Run Scheme Induction for brtree.
Check brtree_ind_MC.

(* Definition ident := nat.
Definition int := nat. *)
Variable (ident int float float32 
    ibinop icmp fcmp conversion_type fast_math fbinop: Type).

Inductive exp (T : Type) : Type :=
	EXP_Ident : ident -> exp T
  | EXP_Integer : int -> exp T
  | EXP_Float : float32 -> exp T
  | EXP_Double : float -> exp T
  | EXP_Hex : float -> exp T
  | EXP_Bool : bool -> exp T
  | EXP_Null : exp T
  | EXP_Zero_initializer : exp T
  | EXP_Cstring : list (T * exp T) -> exp T
  | EXP_Undef : exp T
  | EXP_Struct : list (T * exp T) -> exp T
  | EXP_Packed_struct : list (T * exp T) -> exp T
  | EXP_Array : list (T * exp T) -> exp T
  | EXP_Vector : list (T * exp T) -> exp T
  | OP_IBinop : ibinop -> T -> exp T -> exp T -> exp T
  | OP_ICmp : icmp -> T -> exp T -> exp T -> exp T
  | OP_FBinop : fbinop -> list fast_math -> T -> exp T -> exp T -> exp T
  | OP_FCmp : fcmp -> T -> exp T -> exp T -> exp T
  | OP_Conversion : conversion_type -> T -> exp T -> T -> exp T
  | OP_GetElementPtr : T -> T * exp T -> list (T * exp T) -> exp T
  | OP_ExtractElement : T * exp T -> T * exp T -> exp T
  | OP_InsertElement : T * exp T -> T * exp T -> T * exp T -> exp T
  | OP_ShuffleVector : T * exp T -> T * exp T -> T * exp T -> exp T
  | OP_ExtractValue : T * exp T -> list int -> exp T
  | OP_InsertValue : T * exp T -> T * exp T -> list int -> exp T
  | OP_Select : T * exp T -> T * exp T -> T * exp T -> exp T
  | OP_Freeze : T * exp T -> exp T.

Inductive exp2 : Type :=
    | OP2 (h:nat * exp2).

Inductive exp3 (T:Type) : Type :=
    | OP3 (h:nat * exp3 T).

Inductive exp4 (T:Type) : Type :=
    | OP4 (h:T * exp4 T).

From MetaCoq.Induction Require Import destruct_lemma.
Require Import String.
Local Open Scope string_scope.

Require Import MetaCoq.Template.All.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import PCUICToTemplate.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.

Require Import List String.
Import ListNotations MCMonadNotation Nat.
Require Import MetaCoq.Template.Pretty.
Require Import MetaCoq.PCUIC.PCUICPretty.

From MetaCoq.Induction Require Import helperGen.

Require Import MetaCoq.Template.All.
Import ListNotations MCMonadNotation Nat.

Print TemplateToPCUIC.

MetaCoq Run (
    t <- tmQuote exp4;;
    match t with
    tInd {|inductive_mind := k |} _ => 
    ib <- tmQuoteInductive k;;
    match ib.(ind_bodies) with 
    | oind::_ => 
        let oindPC := TemplateToPCUIC.trans_one_ind_body oind in
        (* let il := getInd oindPC in *)
        il <- getInds oindPC;;
        t <- tmEval lazy il;;
        f <- createFunction t;;
         tmPrint f
    | _ => tmMsg ""
    end
    | _ => tmMsg ""
    end
).


MetaCoq Run Scheme Induction for exp2.
Print exp2_ind_MC.
MetaCoq Run Scheme Induction for exp3.
Print exp3_ind_MC.
Print helperGen.assumption.
Print helperGen.assumptionType.
Print standardNested.prodInst.
Print standardNested.prodAssumption.
MetaCoq Run (runElim exp4 true false None None).
MetaCoq Run Scheme Induction for exp4.
(*
assumption applied to 
    Type -> Type -> Type
    prod
    prodInst : registered prod
    T 
    ---
    exp4 T
    (fun H => P H)
    h : T*exp4 T
*)
Print exp4_ind_MC.

(* helperGen.assumption.
    forall X (ty:X) (reg:registered ty), assumptionType

    fun X (PX: X->Type) Y (PY:Y->Type) ((x,y):X*Y) => PX x * PY y
helperGen.assumptionType.
    forall X (ty:X) (reg:registered ty), Type

    forall X (PX: X->Type) Y (PY:Y->Type), X*Y -> Type
standardNested.prodInst.
standardNested.prodAssumption. *)

MetaCoq Run (runElim exp true false None None).
(* MetaCoq Run (runElim T true true None None). *)
(* MetaCoq Run Scheme Induction for exp. *)
Check exp_ind_MC.


(* 
λ (T : tSort ?). λ (p : ∀ (inst : (exp4 R0)), tSort ?). 
λ (H_OP4 : 
    ∀ (h : ((prod R1) (exp4 R1))), 
            prod T (exp T)
    ∀ (IH_h : ((((((
        (assumption 
            (my_projT1 ((existT_typed_term ∀ (A : tSort ?), ∀ (B : tSort ?), tSort ?) prod))) 
            (my_projT2 ((existT_typed_term ∀ (A : tSort ?), ∀ (B : tSort ?), tSort ?) prod))) 
            prodInst) R2) - (exp4 R2)) λ (_ : (exp4 R2)). (R2 R0)) R0)),
                      T   - (exp T)      a  : exp  T      (p a)   h

      (R2 ((OP4 R3) R1))).
      p    (OP4 T h) 
*)
(** the plugin for induction principles **)

Require Import MetaCoq.Template.All.

From MetaCoq.PCUIC Require Import 
     PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration.

From MetaCoq.PCUIC Require Import PCUICToTemplate.


Require Import List.
Import ListNotations MCMonadNotation Nat.
Require Import MetaCoq.Template.Pretty.
Require Import MetaCoq.PCUIC.utils.PCUICPretty.

Open Scope list_scope.
Open Scope nat_scope.

Require Import non_uniform.
From MetaCoq.Induction Require Import de_bruijn_print.

Require Import Even.
Require Import Recdef.

Scheme Equality for allowed_eliminations.

Definition canElim := allowed_eliminations_beq.


Unset Strict Unquote Universe Mode. 

Definition trans_empty_env := TemplateToPCUIC.trans_global_env Ast.Env.empty_global_env.
Definition topcuic := TemplateToPCUIC.trans trans_empty_env.

  (* convert max elimination level into term *)
Definition getMaxElim (xs : allowed_eliminations) :PCUICAst.term :=
  topcuic
  (if canElim IntoAny xs then <% Type %> else (* todo: is this always the correct Level? *)
    if canElim IntoSetPropSProp xs then <% Set %> else
      <% Prop %>).

Fixpoint collect_prods (t:term) : list (context_decl) :=
  match t with
  | tProd n t1 t2 => (vass n t1)::collect_prods t2
  | _ => []
  end.
Fixpoint collect_lambdas (t:term) : list (context_decl) :=
  match t with
  | tLambda n t1 t2 => (vass n t1)::collect_lambdas t2
  | _ => []
  end.

Definition count_prods (t : term) : nat := #|collect_prods t|.


Definition replaceLastLambda (t:term) (u:term) := it_mkLambda_or_LetIn (rev(collect_lambdas u)) t.
Definition replaceLastProd (t:term) (u:term) := it_mkProd_or_LetIn (rev(collect_prods u)) t.
Definition replaceLastLambda' (t:term) (u:term) := replaceLastLambda u t.
Definition replaceLastProd' (t:term) (u:term) := replaceLastProd u t.

Definition mapProdToLambda (u:term) : term :=
  let prods := collect_prods u in
  it_mkLambda_or_LetIn (rev prods) (remove_arity #|prods| u).


Definition createAppChainOff (o:nat) (t:term) (count:nat) :=
              (mkApps t
                (nat_rect
                    _
                    []
                    (fun n a => cons (tRel (o+n)) a)
                    count
                )
              ).

Definition createAppChain := createAppChainOff 0.

Definition id {X:Type} := fun (x:X) => x.



Definition hasSat (xs:list bool) := fold_left orb xs false.

(* test if a reference k is found in u *)
Fixpoint findRel (nested: kername -> nat -> option (term×term)) (k:nat) (u:term) :=
  match u with
  | tRel n => Nat.eqb n k
  | tEvar ev args => hasSat(map (findRel nested k) args)
  | tProd na A B => orb (findRel nested k A) (findRel nested (S k) B)
  | tLambda na T M => orb (findRel nested k T) (findRel nested (S k) M)
  | tLetIn na b ty b' => orb (orb (findRel nested k b) (findRel nested k ty)) (findRel nested (S k) b')
  | tApp t1 t2 =>
    orb (findRel nested k t1) (findRel nested k t2)
  | tCase ind p c brs => orb (orb (test_predicate (fun _ => false)  (findRel nested k) p) (findRel nested k c)) (hasSat (map (fun p => findRel nested k p.(bbody)) brs))
  | tProj p c => (findRel nested k c)
  | tFix mfix idx =>
      let k' := #|mfix| + k in
      let k' := #|mfix| + k in let mfix' := map (fun a => orb a.(dtype) a.(dbody)) (map (map_def (findRel nested k) (findRel nested k')) mfix) in hasSat mfix'
  | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      let k' := #|mfix| + k in let mfix' := map (fun a => orb a.(dtype) a.(dbody)) (map (map_def (findRel nested k) (findRel nested k')) mfix) in hasSat mfix'
  | _ => false
  end.


Definition trans := TemplateToPCUIC.trans.

(* dummy predicates used for arguments in assumption functions *)
Definition trivialPred (X:Type) (x:X) := True.
Definition trivialProof (X:Type) (x:X) : trivialPred X x := I.
Definition tr1 := topcuic <% trivialPred %>.
Definition tr2 := topcuic <% trivialProof %>.



Definition extendName pre na :=
  {| 
  binder_name :=
  match na.(binder_name) with
    nAnon => nAnon
  | nNamed s => nNamed (pre +s s)
  end;
  binder_relevance := na.(binder_relevance)
  |}.

(* predicate calls with indices and arguments *)
Definition generatePCall2 paramCount recpos ppos app appList n args : option term :=
      if Nat.eqb n recpos then
        Some(
            mkApps
              (
                mkApps (tRel ppos) (skipn paramCount args)
              )
              [mkApps app appList]
          )
      else
        None.

From MetaCoq.PCUIC Require Import PCUICSize.


Lemma fold_right_map {X Y Z:Type} (f:X->Y) (g:Y->Z->Z) a xs:
  fold_right (fun t x => g (f t) x) a xs =
  fold_right (fun t x => g t x) a (map f xs).
Proof.
  induction xs.
  - reflexivity.
  - cbn.
    f_equal.
    apply IHxs.
Defined.

Definition isProd t :=
match t with 
tProd _ _ _ => true
| _ => false
end.

(* simple size function for needed terms *)
Fixpoint termsize (t:term) : nat :=
  match t with
    tEvar _ xs => 1+fold_right (fun t x => termsize t + x) 0 xs
  | tProd _ t1 t2 => 1+termsize t1 + termsize t2
  | tLambda _ t1 t2 => 1+termsize t1 + termsize t2
  | tLetIn _ t1 t2 t3 => 1+termsize t1 + termsize t2 + termsize t3
  | tApp t1 t2 => 1+termsize t1 + termsize t2
  | tCase _ t1 t2 xs => 1+fold_right (fun t x => termsize t.(bbody) + x) 
    (predicate_size termsize t1 + termsize t2) xs
  | tProj _ t1 => 1+ termsize t1
  | _ => 1
  end.

Lemma list_size_all {A} (f g : A -> nat) (l : list A) :
  All (fun x => f x = g x) l ->
  list_size f l = list_size g l.
Proof.
  induction 1; cbn; auto. lia.
Qed.

Lemma termSizeLifting t n k: 
  termsize (lift n k t) = termsize t.
Proof.
  induction t in k |- * using term_forall_list_ind;cbn;try congruence.
  - f_equal.
    induction X.
    + reflexivity.
    + cbn. now rewrite IHX.
  - f_equal.
    rewrite fold_right_map.
    symmetry;rewrite fold_right_map;symmetry.
    f_equal.
    + f_equal.
      * unfold predicate_size. f_equal. f_equal.
        destruct X. rewrite list_size_map.
        apply list_size_all. solve_all.
        apply X.
      * apply IHt.
    + red in X0.
      rewrite !map_map_compose.
      solve_all.
Qed.

Require Import Lia.

Lemma fold_right_sum_leq {X} (f:X->nat) a n xs:
  In a xs ->
  f a <= fold_right (fun t (x : nat) => f t + x) n xs.
Proof.
  intros H.
  induction xs.
  - now contradict H.
  - destruct H as [<- | H].
    + cbn.
      lia.
    + cbn.
      specialize (IHxs H).
      lia.
Defined.

(* computational size induction principle useable to define functions *)
Lemma size_induction X (f:X->nat) (P:X->Type):
  (forall x, (forall y, f y<f x -> P y) -> P x) ->
  forall x, P x.
Proof.
  intros. apply X0.
  assert(forall n y, f y < n -> P y).
  {
    induction n.
    - lia.
    - intros.
      apply X0.
      intros.
      apply IHn.
      lia.
  }
  apply X1.
Defined.

Definition term_size_ind := size_induction term termsize.

(* extract inner element (transforms to TemplateCoq application) *)
Fixpoint getInner (t:term) (xs:list term) : term*list term :=
  match t with
  | tApp t1 t2 => getInner t1 (t2::xs)
  | _ => (t,xs)
  end.

    Require Import Arith.

Lemma lt_plus_S_l n m: n<S(n+m).
Proof.
  apply le_lt_n_Sm, le_plus_l.
Defined.

Lemma lt_plus_S_r n m: n<S(m+n).
Proof.
  apply le_lt_n_Sm, le_plus_r.
Defined.

Import ListNotations.

Open Scope list_scope.

Definition dummyName : aname :=
  {|
  binder_name := nAnon;
  (* binder_relevance := Irrelevant *)
  binder_relevance := Relevant
  |}.

(* generated induction hypotheses, constructor cases, and proof terms *)
Definition generateInductiveAssumptions
  (paramCount : nat) (nested : kername -> nat -> option (term × term))
  (generateInduction : bool) (recpos ppos fpos : nat) 
  (app : term) (appList : list term)
  (generateDummy generateProof mainApp isInner : bool) 
  (body : term) : option term.
revert 
  paramCount nested 
  generateInduction recpos ppos fpos 
  app appList 
  generateDummy generateProof mainApp isInner.
refine (term_size_ind _ _ body).
clear body.
intros.
rename x into body.
revert X.
refine(
  let dummyResult :=
      if generateDummy then
        if generateProof then
          Some (mkApps (tApp tr2 body) [mkApps app appList])
        else
          Some (mkApps (tApp tr1 body) [mkApps app appList])
      else
        None
  in
    match body with
    | tRel n => (* inductive *)
      fun generateInductiveAssumptions =>
      if mainApp then
        Some (mkApps app appList)
      else
        match generatePCall2 paramCount recpos (if generateProof then fpos else ppos) app appList n [] with
        | None => dummyResult
        | h => h
        end

        (* inner call when nested induction is needed *)
    | tInd {| inductive_mind := name; inductive_ind := idx |} u =>
      fun generateInductiveAssumptions =>
      if isInner then
        match nested name idx with
          None => dummyResult
        | Some (t1,t2) =>
          Some (if generateProof then t2 else t1)
        end
      else
        dummyResult
    | tConst name u =>
        (* inner call when nested induction for constants is needed *)
      fun generateInductiveAssumptions =>
      if isInner then
        match nested name 0 with
          None => dummyResult
        | Some (t1,t2) =>
          Some (if generateProof then t2 else t1)
        end
      else
        dummyResult

        (* application with possible nesting (recursion in t1) *)
    | tApp t1 t2 =>
      fun generateInductiveAssumptions =>
      match getInner body [] with
      | (tRel n, args) => (* don't apply all but only indices *)
        if mainApp then
          Some(mkApps app appList)
        else
          generatePCall2 paramCount recpos (if generateProof then fpos else ppos) app appList n args
      | (tInd _ _, _) | (tConst _ _, _) =>
        let isRec := findRel nested recpos body in
        if andb (negb isInner) (negb isRec) then
        (* ignore not registered constants that are applied in app position of nestings and not recursive *)
                        match t1 with
                          tConst name _ =>
                          match nested name 0 with 
                          None => None
                          | _ => dummyResult
                          end
                        | _ => dummyResult
                        end
        else
        (* generate the hypothesis for t1 *)
          match generateInductiveAssumptions t1 _ paramCount nested generateInduction (recpos) (ppos) (fpos) (tRel 0) [] false generateProof mainApp true with
            None => dummyResult
          | Some x =>
            Some (mkApps x
            (* extend with application to t2 and possible hypotheses and proofs *)
                    ([t2] ++
                    match generateInductiveAssumptions (lift0 1 t2) _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (tRel 0) [] true false mainApp false with
                      None => []
                    | Some a => [(tLambda dummyName t2 a)]
                    end
                    ++
                    (if generateProof then
                    match generateInductiveAssumptions (lift0 1 t2) _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (tRel 0) [] true generateProof mainApp false with
                      None => []
                    | Some a => [(tLambda dummyName t2 a)]
                    end
                     else [])
                    ++
                    (
                      if negb isInner then
                        [mkApps app appList]
                        else []
                    ))
                 )
          end
    | _ => None
      end
    | tProd na α inner => (* normal ArgumentChain *)
      fun generateInductiveAssumptions =>
      if generateProof then
        let appList2 := map (lift0 1) appList ++ [tRel 0] ++
        match (if generateInduction then generateInductiveAssumptions (lift0 1 α) _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (tRel 0) [] false generateProof false false else None) with
          None => []
        | Some fα =>
          [fα]
        end in
        innerBody <- generateInductiveAssumptions inner _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (lift0 1 app) appList2 generateDummy generateProof mainApp false;;
        Some (tLambda na α innerBody)
      else
        (
      innerBody <- generateInductiveAssumptions inner _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (lift0 1 app) ((map (lift0 1) appList)++[tRel 0]) generateDummy generateProof mainApp false ;;
      match (if generateInduction then generateInductiveAssumptions (lift0 1 α) _ paramCount nested generateInduction (S recpos) (S ppos) (S fpos) (tRel 0) [] false generateProof false false else None) with
        None => Some (tProd na α innerBody)
      | Some IHα => Some (
                    tProd na α
                    (
                      tProd (extendName "IH_" na) (IHα) (lift0 1 innerBody)
                    )
                  )
      end
      )


     | _ => fun _ => None
    end
).
  Unshelve.
  (* solve equations for recursive calls *)
  all: simpl;try rewrite termSizeLifting;(apply lt_plus_S_l + apply lt_plus_S_r).
Defined.





Require Import nested_datatypes.

Definition mkRelNum (n:nat) :=
  nat_rect (fun _ => list term) [] (fun n a => tRel n :: a) n.

Open Scope bs_scope.

(* generated the cases from the constructor list *)
Definition quantifyCases (isInductive:bool) (ctors : list constructor_body) (paramCount:nat) (ind:inductive) (univ:Instance.t) (nested: kername -> nat -> option (term×term)):=
  let ctorCount := #|ctors| in
  let type := tInd ind univ in
      (* fold over constructors for cases *)
  (* can be omitted with type inference *)
        mapi
        (fun n cb => 
          let count := cb.(cstr_arity) in  (* count=arguments of constructor case *)
          let name := cb.(cstr_name) in
          let a := cb.(cstr_type) in
          let lcount := n in (* how many cases before this *)
           vass
             ({| binder_name := nNamed ("H_" +s name); binder_relevance := Relevant |})
             (
                     let ppos := n in
                     let paramOffset := 1+ppos in
                     let recPos := paramOffset + paramCount in
                     let ctorType :=
            (
              lift0 paramOffset (* lift parameter call over other cases *)
              (remove_arity (* remove param quantification in constructor *)
                  paramCount
                  a
              ))
                         in
                     match
                       generateInductiveAssumptions paramCount nested isInductive recPos ppos 0 (tConstruct ind lcount univ) (map (lift0 (paramOffset)) (mkRelNum paramCount)) false false false false ctorType
                     with
                       None => tVar "this can't happen"
                     | Some t =>
                       subst1 type recPos t
                     end
             )
        ) ctors.

Definition update_arity (fn : nat -> nat) (cb : constructor_body) :=
  {| cstr_name := cb.(cstr_name); 
     cstr_type := cb.(cstr_type);
     cstr_indices := cb.(cstr_indices);
     cstr_args := cb.(cstr_args);
     cstr_arity := fn cb.(cstr_arity) |}.

Definition make_predicate (mib : mutual_inductive_body) (oib : one_inductive_body) 
    (paramlist : list term) univ (ty : term) : predicate term :=
  let (pctx, concl) := 
    match decompose_prod_n_assum [] #|mib.(ind_params)| ty with
    | Some a => a
    | None => ([], ty) (* impossible *)
    end
  in
  let concl := 
    match concl with
    | tProd _ b concl => concl
    | _ => concl (* impossible *)
    end
  in
  {| pparams := paramlist;
     puinst := univ;
     pcontext := pctx;
     preturn := concl |}.

Fixpoint decompose_lam_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match t with
    | tLambda na A B => decompose_lam_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_lam_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

Definition make_branch ind ind_body one_body pred term := 
  let ctx := case_predicate_context ind ind_body one_body pred in
  let body := 
    match decompose_lam_n_assum [] #|ctx| term with 
    | Some (ctx, body) => body
    | None => term
    end
  in
  {| bcontext := ctx; 
     bbody := body |}.

(*
arguments:
isInductive create induction assumptions and proofs
ind         inductive kernelname+index from tInd
univ        universe from tInd
ind_body    declaration extracted by quoteInductive
returnType  prop or type or none to infer maximal elimination
nameFun     generate new names (currently not used)
nested      function mapping inductives to assumption fuction and proof function terms
 *)
Definition createElim (isInductive:bool) (ind:inductive) (univ:Instance.t) (ind_body:mutual_inductive_body) (returnType:option term) (nameFun:name->term->name) (nested: kername -> nat -> option (term×term)) :=
  (* take params *)
    (* p *)
  (* var for cases *)
  (* f *)
  (* indices *)
  (* instance *)
  match nth_error ind_body.(ind_bodies) ind.(inductive_ind) with
  | None => None
  | Some one_body => Some(
  (* let paramCount := ind_body.(ind_npars) in *)
  let allParamCount := ind_body.(ind_npars) in
  let trueParamCount := getParamCount one_body ind_body.(ind_npars) in
  let nonUniformArgCount := ind_body.(ind_npars) - trueParamCount in

  let allParams := ind_body.(ind_params) in
  let nonUniformParams := firstn nonUniformArgCount allParams in
  let trueParams := skipn nonUniformArgCount allParams in

  let trueParamCtors := one_body.(ind_ctors) in
  let allParamCtors := map (update_arity (plus nonUniformArgCount)) one_body.(ind_ctors) in

  let type := tInd ind univ in
  let paramlist := (mapi (fun i _ => tRel (trueParamCount-i-1)) trueParams) in
  let ind_applied := (* typ applied with params *)
      mkApps type paramlist
  in
  let nuIndex_type := remove_arity trueParamCount one_body.(ind_type) in
  let trueIndex_type := remove_arity allParamCount one_body.(ind_type) in
  let allIndCount := (* count of indices and non Uniform *)
      count_prods nuIndex_type
  in
  let trueIndCount := (* count of indices *)
      count_prods trueIndex_type
  in
  let ctorCount := #|trueParamCtors| in
  let predType :=
       replaceLastProd
         (
            (* add ∀ for instance *)
            (tProd ({| binder_name := nNamed "inst"; binder_relevance := Relevant |})
                   (createAppChain (lift0 allIndCount ind_applied) allIndCount)
                 (* if prop => elim over prop *)
                 (* if type => elim over type *)
               (match returnType with None => getMaxElim one_body.(ind_kelim) | Some t => t end)
          )
         )
         (* quantify over indices but not over params *)
         nuIndex_type in
  let case_pred :=
    make_predicate ind_body one_body paramlist univ
      (lift0 (S trueIndCount)
      (replaceLastLambda'
        (mapProdToLambda
      (lift (2+ctorCount) nonUniformArgCount
                  (remove_arity nonUniformArgCount predType)
        ))
        (* apply p with indices and instace *)
        (* p is after instance, indices, f, arguments (indices and instance) and cases *)
        (* trueInd from above, nonUniformArgCount, f,  *)
        (createAppChain (tRel (1+allIndCount+1+ctorCount) (* 1+trueIndCount *)
                        ) (S allIndCount))
      ))
  in
  (* quantify over all params *)
  it_mkLambda_or_LetIn trueParams
  (tLambda
     (* predicate *)
     ({| binder_name := nNamed "p"; binder_relevance := Relevant |})
     (* the type of p is a transformation of the type
      todo: fold indices for type of p or use the type in index construction below
      for consistency*)
     predType
     (
       it_mkLambda_or_LetIn (rev (quantifyCases isInductive allParamCtors trueParamCount ind univ nested))
        (*
          theoretically recursive fix after cases
         *)
         (
              tFix
            [{|
             dname := {| binder_name := nNamed "f"; binder_relevance := Relevant |};
             dtype := (* could be omitted using type inference *)
               (* lift over cases for constructor and p *)
               replaceLastProd'
               (lift0 (S ctorCount) predType)
               (createAppChain (tRel (allIndCount + S ctorCount)) (S allIndCount))
              (* return p of instace *)
              (* p is after indices and cases *)
              ;
              dbody := (* take all indicies *)
              (* lift over cases for constructor and p and f? *)
                replaceLastLambda'
                  (mapProdToLambda (lift0 (2+ctorCount) predType))
                  (
                    (* match on instance *)
                    (* use change match return type, case application and access to non uniform *)
                        (tCase {| ci_ind := ind; ci_npar := allParamCount; 
                          ci_relevance := one_body.(ind_relevance) |}
                            (* return type of match *)
                            case_pred
                           (* on instance *)
                            (tRel 0)
                            (* map case for each constructor *)

    (mapi
      (fun i cb =>
        let count := cb.(cstr_arity) in (* count for arguments of constructor *)
        let a := cb.(cstr_type) in 
        make_branch ind ind_body one_body case_pred 
           (let fpos := 1+allIndCount in
            let Hstart := fpos in
            let Hpos := Hstart+(ctorCount -i) in

            let ppos := 1+Hstart+ctorCount in
            let paramOffset := 1+ppos in
            let recPos := paramOffset + trueParamCount in

            let ctorType :=
                        (
                          (lift0 (S trueIndCount)
                          (lift (2+ctorCount) nonUniformArgCount
                                (remove_arity allParamCount a)
                          )
                          )
                        )
            in
            match
              generateInductiveAssumptions trueParamCount nested isInductive recPos 
                ppos fpos (tRel Hpos) (map (lift0 (1+trueIndCount)) 
                (mkRelNum nonUniformArgCount)) false true true false ctorType
            with
              None => tVar "this can't happen (proof)"
            | Some t =>
              subst1 type recPos t
            end
            )) trueParamCtors))) ;
             (* recursion over instance (last argument) *)
             rarg := allIndCount |}] 0)
    )) 
  , one_body.(ind_name) +s (if isInductive then "_ind_MC" else "_case_MC") ) end.



Require Import helperGen.

(* Set Universe Polymorphism. *)

Class betterInd {X} (ty:X) :=
{
  principleType: Type;
  principle: principleType
}.

Print tmDefinitionRed.


(* POLYMORPHIC *)
Definition runElim {A:Type} (indTm : A) (isInductive:bool) (create:bool) (nameOpt:option ident) (returnType:option Ast.term)
  : TemplateMonad unit
  := p <- tmQuoteRec indTm;;
     let (env,tm) := (p:Ast.Env.program) in
     let tenv := TemplateToPCUIC.trans_global_env env in
     match tm with
     | Ast.tInd ind0 univ =>
       decl <- tmQuoteInductive (inductive_mind ind0) ;;
       nestedFunc <- extractFunction tenv (TemplateToPCUIC.trans_minductive_body tenv decl) (inductive_ind ind0);;
            let namingFun (na:name) (t:term) : name :=
                BasicAst.nNamed (fresh_name (empty_ext tenv.(TemplateToPCUIC.trans_env_env)) [] na (Some t))
            in
            let lemma : option (term×string) := createElim isInductive ind0 univ (TemplateToPCUIC.trans_minductive_body tenv decl) (option_map (trans tenv) returnType) namingFun nestedFunc in
            evaluated <- tmEval lazy lemma;;
            if create then
              match evaluated with
                None => tmFail "invalid inductive"
              | Some (x,name') =>
                let name := match nameOpt with None => name' | Some s => s end
                in
                        tmMsg ("created " +s name);;
                         y <- tmUnquote (PCUICToTemplate.trans x);;
                         z <- tmEval lazy (y.(my_projT2));;
                        oldName <- tmEval all name;;
                        newName <- tmFreshName oldName;;
                        obj <- tmDefinitionRed newName (Some lazy) z;;(* simplified type *)
                        tmReturn tt

                        (* registering better induction principles *)
                        (* let instName' := newName +s "_inst" in
                        oldName' <- tmEval all instName';;
                        instName <- tmFreshName oldName';;
                        (* tmPrint obj;; *)
                        reg <- tmEval cbv (
                          {|
                              principle := @obj
                          |} : betterInd indTm
                        );;
                        tmPrint reg;;
                        tmDefinitionRed instName (Some cbv) reg;;
                        (* (1* tmDefinition instName ( *1) *)
                        (* (1*   {| *1) *)
                        (* (1*       principle := @obj *1) *)
                        (* (1*   |} : betterInd indTm *1) *)
                        (* (1* );; *1) *)
                        (* tmExistingInstance instName;; *)

                        tmReturn tt *)
              end
            else
              match evaluated with
                None => tmPrint "failed"
                | Some (x,_) =>
                  tmPrint x;;
                  bruijn_print x;;
                  tmMsg "";;
                  tmMsg (print_term (empty_ext (TemplateToPCUIC.trans_env_env tenv)) true [] true false x)
              end
     | _ => tmPrint tm ;; tmFail " is not an inductive"%bs
     end.

(* Print Universes. *)


Definition create {A:Type} (tm:A) (isInductive:bool) (create:bool) :=
  runElim tm isInductive create None None.


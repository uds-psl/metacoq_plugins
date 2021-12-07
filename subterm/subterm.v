From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst.
From MetaCoq.PCUIC Require TemplateToPCUIC PCUICToTemplate.

From MetaCoq.Template Require Import config monad_utils utils TemplateMonad Universes.
From MetaCoq.Template Require Ast.
Import MCMonadNotation.

Require Import List String Relation_Operators.
Import ListNotations.

From Local Require Import non_uniform.

Definition clift0 (n : nat) (t : context_decl) : context_decl :=
  {| decl_name := t.(decl_name);
     decl_body := match t.(decl_body) with
                   | Some q => Some (lift0 n q)
                   | None => None
                  end;
     decl_type := lift0 n t.(decl_type)
  |}.

Definition subterms_for_constructor
           (refi : inductive)
           (ref   : term) (* we need the term for exactly this inductive just for the substition *)
           (ntypes : nat) (* number of types in the mutual inductive *)
           (npars : nat) (* number of parameters in the type *)
           (nind : nat) (* number of proper indeces in the type *)
           (ct    : term) (* type of the constructor *)
           (ncons : nat) (* index of the constructor in the inductive *)
           (nargs : nat) (* number of arguments in this constructor *)
                  : list (nat * term * nat)
  := let indrel := (ntypes - inductive_ind refi - 1) in
    let '(ctx, ap) := decompose_prod_assum [] ct in
    (*    ^ now ctx is a reversed list of assumptions and definitions *)
    let len := List.length ctx in
    let params := List.skipn (len - npars) (ctx) in
    let inds := List.skipn npars (snd (decompose_app ap)) in
    (* d is a list of occurences of subterms in arguments to the constructor *)
    let d :=List.concat (
           (* so this i represents distance from return object to `t` *)
              mapi (fun i t =>
                      let '(ctx, ar) := decompose_prod_assum [] (decl_type t)
                      in let p := (indrel + (len - i - 1) + List.length (ctx))
                      in let (f, s) := decompose_app ar
                      in match f with
                         | tRel j => if Nat.eqb p j
                                    then [inl (i, ctx, s)]
                                    else []
                         | tInd list [] => 
                         end) ctx) in
    let '(ctx_sbst, _) := decompose_prod_assum [] (subst1 ref indrel ct) in
    let construct_cons :=
        fun (* index of a subterm in this constructor *)
          (i: nat)
          (* these are arguments for the function
             that is a parameter of the constructor
             and if applied fully returns something of the needed type *)
          (ctx': context)
          (* these are arguments of the type of the subterm *)
          (args' : list term) =>
          let len' := List.length ctx' in
          let ctxl' := (map (clift0 (2 + i)) ctx') in
          it_mkProd_or_LetIn
             (ctxl' ++ ctx_sbst)
             (mkApps (tRel (len + len'))
                   ((map (lift0 (len' + len - npars))
                         (to_extended_list params)) ++
                    (map (lift (1 + i + len') len') (List.skipn npars args')) ++
                    (map (lift0 len') inds) ++
                    [mkApps (tRel (i + len'))
                          (to_extended_list ctxl');
                     mkApps (tConstruct refi ncons [])
                         (map (lift0 len') (to_extended_list ctx_sbst))])) in
    mapi (fun i '(n, c, a) => (i, construct_cons n c a, len + List.length c)) d.

Definition nAnon := mkBindAnn nAnon Relevant.

Definition subterm_for_ind
           (refi : inductive)
           (ref   : term)
           (allparams : nat)
           (ntypes : nat) (* number of types in the mutual inductive *)
           (ind   : one_inductive_body)
                  : one_inductive_body
  := let (pai, _) := decompose_prod_assum [] ind.(ind_type) in
    let sort := (tSort (Universe.of_levels (inl PropLevel.lProp))) in
    let npars := getParamCount ind allparams in
    let pars := List.skipn (List.length pai - npars) pai in
    let inds := List.firstn (List.length pai - npars) pai in
    let ninds := List.length inds in
    let aptype1 :=
        mkApps ref ((map (lift0 (2 * ninds)) (to_extended_list pars)) ++
                    (map (lift0 ninds) (to_extended_list inds))) in
    let aptype2 :=
        mkApps ref ((map (lift0 (1 + 2 * ninds)) (to_extended_list pars)) ++
                    (map (lift0 1) (to_extended_list inds))) in
    let renamer name i := (name ++ "_subterm" ++ (string_of_nat i))%string in
    {| ind_name := (ind.(ind_name) ++ "_direct_subterm")%string;
       ind_type  := it_mkProd_or_LetIn
                      pars
                   (it_mkProd_or_LetIn
                      (inds)
                   (it_mkProd_or_LetIn
                      (map (clift0 (ninds)) inds)
                   (it_mkProd_or_LetIn
                       [mkdecl nAnon None aptype2; mkdecl nAnon None aptype1]
                       sort)));
       ind_kelim := IntoPropSProp;
       ind_ctors :=List.concat
                     (mapi (fun n '(id', ct, k) => (
                       map (fun '(si, st, sk) => (renamer id' si, st, sk))
                       (subterms_for_constructor refi ref ntypes npars ninds ct n k)))
                       ind.(ind_ctors));
      ind_projs := [];
    ind_relevance := Relevant |}.


Definition direct_subterm_for_mutual_ind
            (mind : mutual_inductive_body)
            (ind0 : inductive) (* internal metacoq representation of inductive, part of tInd *)
            (ref  : term) (* reference term for the inductive type, like (tInd {| inductive_mind := "Coq.Init.Datatypes.nat"; inductive_ind := 0 |} []) *)
                  : option mutual_inductive_body
  := let i0 := inductive_ind ind0 in
    let ntypes := List.length (ind_bodies mind) in
    b <- List.nth_error mind.(ind_bodies) i0 ;;
    ret {|
        ind_finite := BasicAst.Finite;
        ind_npars := 0;
        ind_universes := tInfer ;
        ind_params := [];
        ind_bodies := [subterm_for_ind ind0 ref mind.(ind_npars) ntypes b];
        ind_variance := None
      |}.

Definition subterm (t : Ast.term)
  : TemplateMonad unit
  := match t with
    | Ast.tInd ind0 _ =>
      decl <- tmQuoteInductive (inductive_mind ind0);;
      tmPrint decl;;
      match (subterm.direct_subterm_for_mutual_ind
               (TemplateToPCUIC.trans_minductive_body decl)
               ind0
               (TemplateToPCUIC.trans t)) with
      | None =>
        tmPrint t;;
        @tmFail unit "Coulnd't construct a subterm"
      | Some d =>
        v <- tmEval lazy (PCUICToTemplate.trans_minductive_body d);;
        tmPrint v;;
        tmMkInductive' v
      end
    | _ =>
      tmPrint t;;
      @tmFail unit " is not an inductive"
    end.

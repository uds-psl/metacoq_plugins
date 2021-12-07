From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst.
From MetaCoq.PCUIC Require TemplateToPCUIC PCUICToTemplate.

From MetaCoq.Template Require Import config monad_utils utils TemplateMonad Loader.
From MetaCoq.Template Require Ast.
Import MCMonadNotation.
Require Import List String.
Import ListNotations.

Definition ex := tInd
  {|
  inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "ex");
  inductive_ind := 0 |} [].

(* Definition sigma := tInd *)
(*   {| *)
(*   inductive_mind := (MPfile ["Specif"; "Init"; "Coq"], "sigT"); *)
(*     inductive_ind := 0 |} []. *)

Definition sigma := match <% @Init.sigma %> with Ast.tInd i l => tInd i l | _ => tVar "no" end.
Print sigma.

Definition acc := tInd
  {| inductive_mind := (MPfile ["Wf"; "Init"; "Coq"], "Acc"); inductive_ind := 0 |}
  [].

Definition sigmaize (u : context_decl) (v : term) :=
  match (decl_body u) with
  | Some body => tLetIn (decl_name u) body (decl_type u) v
  | None => mkApps sigma [(decl_type u) ;
                      tLambda (decl_name u) (decl_type u) (tApp v (tRel 0))]
  end.

Fixpoint sigma_pack_go (n: nat) (c : context) (t : list term -> term) :=
  match c with
  | [] => t
  | ch :: ct =>
    match (decl_body ch) with
    | Some body =>
      sigma_pack_go (n - 1) ct (fun l => tLetIn (decl_name ch) body (decl_type ch) (t l))
    | None =>
      sigma_pack_go (n - 1) ct (fun l =>
      mkApps sigma [(decl_type ch);
               tLambda (decl_name ch) (decl_type ch) (t (tRel n :: l))])
    end
  end.

Definition sigma_pack_arity (t : term) : term
  := let (pai, c) := decompose_prod_assum [] t in
    (sigma_pack_go (List.length pai - 1) pai (fun l => mkApps t l) []).

Definition sigma_pack_inductive
           (i : inductive)
           (m : mutual_inductive_body)
              : option term :=
  (*let params := (ind_params m) in*)
  match (List.nth_error (ind_bodies m) (inductive_ind i)) with
  | None => None
  | Some ind =>
      let (inds, _) := decompose_prod_assum [] (ind_type ind) in
      let params := firstn (ind_npars m) (rev inds) in
      let inds := rev (skipn (ind_npars m) (rev inds)) in
      Some (
          it_mkLambda_or_LetIn params (
          sigma_pack_go (List.length inds - 1) inds (fun l => mkApps (tInd i []) (map tRel (rev (seq (List.length inds) (ind_npars m))) ++ l)) []))
  end.

Definition pack_inductive (t : Ast.term) : TemplateMonad (Ast.term) :=
    match t with
    | Ast.tInd ind0 _ =>
      decl <- tmQuoteInductive (inductive_mind ind0);;
      match (sigma_pack_inductive
               ind0
               (TemplateToPCUIC.trans_minductive_body decl)) with
      | None =>
        tmPrint t;;
        @tmFail (Ast.term) "Coulnd't pack inductive"
      | Some d =>
        v <- tmEval lazy (PCUICToTemplate.trans d);;
        @tmReturn (Ast.term) v
      end
    | _ =>
      tmPrint t;;
      @tmFail (Ast.term) " is not an inductive"
    end.



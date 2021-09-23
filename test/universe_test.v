Require Import MetaCoq.Template.All.
Import MonadNotation.
Require Import String.


Definition getKername {A:Type} (indTm : A) : TemplateMonad kername
  := p <- tmQuoteRec indTm;;
     let (env,tm) := (p:Ast.program) in
     match tm with
     | Ast.tInd ind0 univ =>
       (* decl <- tmQuoteInductive (inductive_mind ind0) ;; *)
       tmReturn (inductive_mind ind0)
     | _ => tmPrint tm ;; tmFail " is not an inductive"
     end.

Definition printType {A:Type} (ind:A) : TemplateMonad unit := 
    kname <- getKername ind;;
    tmQuoteInductive kname >>= tmPrint.

Definition splitter :string := "===================================================================".


Inductive rose := leaf | node (xs:list rose).

Inductive listᵗ (A : Type) (Aᵗ : A -> Type) : list A -> Type :=
	nilᵗ : listᵗ A Aᵗ nil
  | consᵗ : forall H : A,
            Aᵗ H -> forall H0 : list A, listᵗ A Aᵗ H0 -> listᵗ A Aᵗ (H :: H0).
Inductive listrose (X:Type) : Type := leaf3 (x:X) | node3 (xs:list (listrose X)).
Inductive listroseᵗ (X : Type) (Xᵗ : X -> Type) : listrose X -> Type :=
	node3ᵗ : forall h : list (listrose X),
              listᵗ (listrose X) (listroseᵗ X Xᵗ) h -> 
              listroseᵗ X Xᵗ (node3 X h).

MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType list).
MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType listᵗ).
MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType listrose).
MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType listroseᵗ).
MetaCoq Run (tmMsg splitter).


Print mutual_inductive_body. (* univ_decl *) (* generated *)
Print mutual_inductive_entry. (* univ_entry *) 
About mutual_inductive_body.
About mutual_inductive_entry.
Print universes_decl.
Print universes_entry.


MetaCoq Run (
    tmQuote nat >>= tmPrint
).

MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType nat).
MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType list).
MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType rose).
MetaCoq Run (tmMsg splitter).

Check ind_universes.
Check Monomorphic_ctx.
Check ConstraintSet.empty.
Check ConstraintSet.add.
Check UnivConstraint.make.
Check Level.Level.
Print universes_decl.
Print ContextSet.t.
Print Level.t_.
Print ConstraintSet.t_.
Print UnivConstraint.t.
Print ConstraintSet.

Search universes_decl.
Search ContextSet.t.
Search ConstraintSet.t.

(* union of ConstraintSet.t over all in quoteRec => not new types *)
(* test without constraint *)

Definition cod a b := a -> b.
Definition fin (n:nat) := nat.
Inductive folterm (n_term : nat) : Type :=
  | var_folterm : fin n_term -> folterm n_term
  | Func : forall f : nat, cod (fin f) (folterm n_term) -> folterm n_term.

(* MetaCoq Run (tmQuoteRec folterm >>= tmPrint). *)

(* MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType cod).
MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType fin). *)
MetaCoq Run (tmMsg splitter).
MetaCoq Run (printType folterm).
MetaCoq Run (tmMsg splitter).

Compute (<% Type %>).

Unset Strict Unquote Universe Mode.
Definition ta := Type.
Polymorphic Definition tb := Type.

MetaCoq Quote Definition tqa := Type.
(* MetaCoq Quote Polymorphic Definition tqb := Type. *)

MetaCoq Run (tmMsg splitter).
MetaCoq Run (tmQuoteRec ta >>= tmPrint).
MetaCoq Run (tmMsg splitter).
MetaCoq Run (tmQuoteRec tb >>= tmPrint).
MetaCoq Run (tmMsg splitter).

Unset Strict Unquote Universe Mode.
(* Definition type := <% Type %>. *)


Definition folterm2_quoted := 
{|
ind_finite := Finite;
ind_npars := 1;
ind_params := [{|
	           decl_name := nNamed "n_term"%string;
               decl_body := None;
               decl_type := tInd
                              {|
                              inductive_mind := (MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                "nat"%string);
                              inductive_ind := 0 |} [] |}]%list;
ind_bodies := [{|
               ind_name := "folterm2"%string;
               ind_type := tProd (nNamed "n_term"%string)
                             (tInd
                                {|
                                inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string]%list,
                                                 "nat"%string);
                                inductive_ind := 0 |} []%list)
                                (* (type) *)
                                (* (<% Type %>) *)
                                (tqa)
                                ;
                             (* (tSort
                                (Universe.from_kernel_repr
                                   (Level.lSet, false)
                                   [(Level.Level "universe_test.486", false);
                                   (Level.Level "universe_test.487", false)])); *)
               ind_kelim := InType;
               ind_ctors := [("var_folterm2"%string,
                             tProd (nNamed "n_term"%string)
                               (tInd
                                  {|
                                  inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string]%list,
                                                 "nat"%string);
                                  inductive_ind := 0 |} []%list)
                               (tProd nAnon
                                  (tApp
                                     (tConst
                                        (MPfile ["universe_test"%string]%list,
                                        "fin"%string) []%list) [
                                     tRel 0]) (tApp (tRel 2) [tRel 1])), 1);
                            ("Func2"%string,
                            tProd (nNamed "n_term"%string)
                              (tInd
                                 {|
                                 inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string]%list,
                                                 "nat"%string);
                                 inductive_ind := 0 |} []%list)
                              (tProd (nNamed "f"%string)
                                 (tInd
                                    {|
                                    inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string]%list,
                                                 "nat"%string);
                                    inductive_ind := 0 |} []%list)
                                 (tProd nAnon
                                    (tApp
                                       (tConst
                                          (MPfile
                                             ["universe_test"%string]%list,
                                          "cod"%string) []%list)
                                       [tApp
                                          (tConst
                                             (MPfile
                                                ["universe_test"%string]%list,
                                             "fin"%string) []%list) [
                                          tRel 0]; 
                                       tApp (tRel 2) [tRel 1]])
                                    (tApp (tRel 3) [tRel 2]))), 2)];
               ind_projs := [] |}];
ind_universes := 
(* Polymorphic_ctx ([]%list,ConstraintSet.empty); *)
 Monomorphic_ctx
                   (LevelSetProp.of_list [], ConstraintSet.empty);
(* Monomorphic_ctx
                   (LevelSetProp.of_list [],
                   ConstraintSet.add
                     (UnivConstraint.make (Level.Level "universe_test.486")
                        ConstraintType.Le (Level.Level "universe_test.487"))
                     (ConstraintSet.add
                        (UnivConstraint.make Level.lSet ConstraintType.Le
                           (Level.Level "universe_test.487"))
                        (ConstraintSet.add
                           (UnivConstraint.make Level.lSet ConstraintType.Le
                              (Level.Level "universe_test.486"))
                           ConstraintSet.empty))); *)
ind_variance := None |}.

(* Search UContext.t. *)
(* Search global_env. *)
(* Search (_ -> global_env).
Check tmQuoteRec.
Print program.

Search (_ -> ConstraintSet.t). *)
(* UContext.constraints: UContext.t -> ConstraintSet.t
TemplateLookup.global_ext_constraints:
  TemplateEnvironment.global_env_ext -> ConstraintSet.t
TemplateLookup.global_constraints:
  TemplateEnvironment.global_env -> ConstraintSet.t
TemplateLookup.monomorphic_constraints_decl:
  TemplateEnvironment.global_decl -> ConstraintSet.t *)


(* Check folterm2_quoted.
Search mutual_inductive_body mutual_inductive_entry.
Print TemplateMonad. *)

Definition env : global_env :=
[(MPfile ["universe_test"%string], "folterm"%string,
  InductiveDecl
	{|
    ind_finite := Finite;
    ind_npars := 1;
    ind_params := [{|
                   decl_name := nNamed "n_term"%string;
                   decl_body := None;
                   decl_type := tInd
                                  {|
                                  inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                  inductive_ind := 0 |} [] |}];
    ind_bodies := [{|
                   ind_name := "folterm"%string;
                   ind_type := tProd (nNamed "n_term"%string)
                                 (tInd
                                    {|
                                    inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                    inductive_ind := 0 |} [])
                                 (tSort
                                    (Universe.from_kernel_repr
                                       (Level.lSet, false)
                                       [(Level.Level "universe_test.486",
                                        false);
                                       (Level.Level "universe_test.487",
                                       false)]));
                   ind_kelim := InType;
                   ind_ctors := [("var_folterm"%string,
                                 tProd (nNamed "n_term"%string)
                                   (tInd
                                      {|
                                      inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                      inductive_ind := 0 |} [])
                                   (tProd nAnon
                                      (tApp
                                         (tConst
                                            (MPfile ["universe_test"%string],
                                            "fin"%string) []) [
                                         tRel 0]) 
                                      (tApp (tRel 2) [tRel 1])), 1);
                                ("Func"%string,
                                tProd (nNamed "n_term"%string)
                                  (tInd
                                     {|
                                     inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                     inductive_ind := 0 |} [])
                                  (tProd (nNamed "f"%string)
                                     (tInd
                                        {|
                                        inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                        inductive_ind := 0 |} [])
                                     (tProd nAnon
                                        (tApp
                                           (tConst
                                              (MPfile
                                                 ["universe_test"%string],
                                              "cod"%string) [])
                                           [tApp
                                              (tConst
                                                 (
                                                 MPfile
                                                 ["universe_test"%string],
                                                 "fin"%string) []) [
                                              tRel 0];
                                           tApp (tRel 2) [tRel 1]])
                                        (tApp (tRel 3) [tRel 2]))), 2)];
                   ind_projs := [] |}];
    ind_universes := Monomorphic_ctx
                       (LevelSetProp.of_list [],
                       ConstraintSet.add
                         (UnivConstraint.make
                            (Level.Level "universe_test.486")
                            ConstraintType.Le
                            (Level.Level "universe_test.487"))
                         (ConstraintSet.add
                            (UnivConstraint.make Level.lSet ConstraintType.Le
                               (Level.Level "universe_test.487"))
                            (ConstraintSet.add
                               (UnivConstraint.make Level.lSet
                                  ConstraintType.Le
                                  (Level.Level "universe_test.486"))
                               ConstraintSet.empty)));
    ind_variance := None |});
 (MPfile ["universe_test"%string], "cod"%string,
 ConstantDecl
   {|
   cst_type := tProd (nNamed "a"%string)
                 (tSort
                    (Universe.from_kernel_repr
                       (Level.Level "universe_test.486", false) []))
                 (tProd (nNamed "b"%string)
                    (tSort
                       (Universe.from_kernel_repr
                          (Level.Level "universe_test.487", false) []))
                    (tSort
                       (Universe.from_kernel_repr
                          (Level.Level "universe_test.486", false)
                          [(Level.Level "universe_test.487", false)])));
   cst_body := Some
                 (tLambda (nNamed "a"%string)
                    (tSort
                       (Universe.from_kernel_repr
                          (Level.Level "universe_test.486", false) []))
                    (tLambda (nNamed "b"%string)
                       (tSort
                          (Universe.from_kernel_repr
                             (Level.Level "universe_test.487", false) []))
                       (tProd nAnon (tRel 1) (tRel 1))));
   cst_universes := Monomorphic_ctx
                      (LevelSetProp.of_list
                         [Level.Level "universe_test.487";
                         Level.Level "universe_test.486"],
                      ConstraintSet.empty) |});
 (MPfile ["universe_test"%string], "fin"%string,
 ConstantDecl
   {|
   cst_type := tProd (nNamed "n"%string)
                 (tInd
                    {|
                    inductive_mind := (MPfile
                                         ["Datatypes"%string; "Init"%string;
                                         "Coq"%string], "nat"%string);
                    inductive_ind := 0 |} [])
                 (tSort (Universe.from_kernel_repr (Level.lSet, false) []));
   cst_body := Some
                 (tLambda (nNamed "n"%string)
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["Datatypes"%string;
                                            "Init"%string; "Coq"%string],
                                         "nat"%string);
                       inductive_ind := 0 |} [])
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["Datatypes"%string;
                                            "Init"%string; "Coq"%string],
                                         "nat"%string);
                       inductive_ind := 0 |} []));
   cst_universes := Monomorphic_ctx
                      (LevelSetProp.of_list [], ConstraintSet.empty) |});
 (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string,
 InductiveDecl
   {|
   ind_finite := Finite;
   ind_npars := 0;
   ind_params := [];
   ind_bodies := [{|
                  ind_name := "nat"%string;
                  ind_type := tSort
                                (Universe.from_kernel_repr
                                   (Level.lSet, false) []);
                  ind_kelim := InType;
                  ind_ctors := [("O"%string, tRel 0, 0);
                               ("S"%string, tProd nAnon (tRel 0) (tRel 1), 1)];
                  ind_projs := [] |}];
   ind_universes := Monomorphic_ctx
                      (LevelSetProp.of_list [], ConstraintSet.empty);
   ind_variance := None |})]%list.

Compute (global_constraints env).




MetaCoq Run (
    tmMkInductive (mind_body_to_entry folterm2_quoted)
).

Print folterm2.




(* ([(MPfile ["universe_test"%string], "folterm"%string,
  InductiveDecl
	{|
    ind_finite := Finite;
    ind_npars := 1;
    ind_params := [{|
                   decl_name := nNamed "n_term"%string;
                   decl_body := None;
                   decl_type := tInd
                                  {|
                                  inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                  inductive_ind := 0 |} [] |}];
    ind_bodies := [{|
                   ind_name := "folterm"%string;
                   ind_type := tProd (nNamed "n_term"%string)
                                 (tInd
                                    {|
                                    inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                    inductive_ind := 0 |} [])
                                 (tSort
                                    (Universe.from_kernel_repr
                                       (Level.lSet, false)
                                       [(Level.Level "universe_test.486",
                                        false);
                                       (Level.Level "universe_test.487",
                                       false)]));
                   ind_kelim := InType;
                   ind_ctors := [("var_folterm"%string,
                                 tProd (nNamed "n_term"%string)
                                   (tInd
                                      {|
                                      inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                      inductive_ind := 0 |} [])
                                   (tProd nAnon
                                      (tApp
                                         (tConst
                                            (MPfile ["universe_test"%string],
                                            "fin"%string) []) [
                                         tRel 0]) 
                                      (tApp (tRel 2) [tRel 1])), 1);
                                ("Func"%string,
                                tProd (nNamed "n_term"%string)
                                  (tInd
                                     {|
                                     inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                     inductive_ind := 0 |} [])
                                  (tProd (nNamed "f"%string)
                                     (tInd
                                        {|
                                        inductive_mind := (
                                                 MPfile
                                                 ["Datatypes"%string;
                                                 "Init"%string; "Coq"%string],
                                                 "nat"%string);
                                        inductive_ind := 0 |} [])
                                     (tProd nAnon
                                        (tApp
                                           (tConst
                                              (MPfile
                                                 ["universe_test"%string],
                                              "cod"%string) [])
                                           [tApp
                                              (tConst
                                                 (
                                                 MPfile
                                                 ["universe_test"%string],
                                                 "fin"%string) []) [
                                              tRel 0];
                                           tApp (tRel 2) [tRel 1]])
                                        (tApp (tRel 3) [tRel 2]))), 2)];
                   ind_projs := [] |}];
    ind_universes := Monomorphic_ctx
                       (LevelSetProp.of_list [],
                       ConstraintSet.add
                         (UnivConstraint.make
                            (Level.Level "universe_test.486")
                            ConstraintType.Le
                            (Level.Level "universe_test.487"))
                         (ConstraintSet.add
                            (UnivConstraint.make Level.lSet ConstraintType.Le
                               (Level.Level "universe_test.487"))
                            (ConstraintSet.add
                               (UnivConstraint.make Level.lSet
                                  ConstraintType.Le
                                  (Level.Level "universe_test.486"))
                               ConstraintSet.empty)));
    ind_variance := None |});
 (MPfile ["universe_test"%string], "cod"%string,
 ConstantDecl
   {|
   cst_type := tProd (nNamed "a"%string)
                 (tSort
                    (Universe.from_kernel_repr
                       (Level.Level "universe_test.486", false) []))
                 (tProd (nNamed "b"%string)
                    (tSort
                       (Universe.from_kernel_repr
                          (Level.Level "universe_test.487", false) []))
                    (tSort
                       (Universe.from_kernel_repr
                          (Level.Level "universe_test.486", false)
                          [(Level.Level "universe_test.487", false)])));
   cst_body := Some
                 (tLambda (nNamed "a"%string)
                    (tSort
                       (Universe.from_kernel_repr
                          (Level.Level "universe_test.486", false) []))
                    (tLambda (nNamed "b"%string)
                       (tSort
                          (Universe.from_kernel_repr
                             (Level.Level "universe_test.487", false) []))
                       (tProd nAnon (tRel 1) (tRel 1))));
   cst_universes := Monomorphic_ctx
                      (LevelSetProp.of_list
                         [Level.Level "universe_test.487";
                         Level.Level "universe_test.486"],
                      ConstraintSet.empty) |});
 (MPfile ["universe_test"%string], "fin"%string,
 ConstantDecl
   {|
   cst_type := tProd (nNamed "n"%string)
                 (tInd
                    {|
                    inductive_mind := (MPfile
                                         ["Datatypes"%string; "Init"%string;
                                         "Coq"%string], "nat"%string);
                    inductive_ind := 0 |} [])
                 (tSort (Universe.from_kernel_repr (Level.lSet, false) []));
   cst_body := Some
                 (tLambda (nNamed "n"%string)
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["Datatypes"%string;
                                            "Init"%string; "Coq"%string],
                                         "nat"%string);
                       inductive_ind := 0 |} [])
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["Datatypes"%string;
                                            "Init"%string; "Coq"%string],
                                         "nat"%string);
                       inductive_ind := 0 |} []));
   cst_universes := Monomorphic_ctx
                      (LevelSetProp.of_list [], ConstraintSet.empty) |});
 (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string,
 InductiveDecl
   {|
   ind_finite := Finite;
   ind_npars := 0;
   ind_params := [];
   ind_bodies := [{|
                  ind_name := "nat"%string;
                  ind_type := tSort
                                (Universe.from_kernel_repr
                                   (Level.lSet, false) []);
                  ind_kelim := InType;
                  ind_ctors := [("O"%string, tRel 0, 0);
                               ("S"%string, tProd nAnon (tRel 0) (tRel 1), 1)];
                  ind_projs := [] |}];
   ind_universes := Monomorphic_ctx
                      (LevelSetProp.of_list [], ConstraintSet.empty);
   ind_variance := None |})]%list,
tInd
  {|
  inductive_mind := (MPfile ["universe_test"%string]%list, "folterm"%string);
  inductive_ind := 0 |} []%list) *)

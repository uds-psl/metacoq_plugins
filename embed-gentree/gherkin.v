(** 
 * 
 *        _               _    _       
 *      | |             | |  (_)      
 *  __ _| |__   ___ _ __| | ___ _ __  
 * / _` | '_ \ / _ \ '__| |/ / | '_ \ 
 *| (_| | | | |  __/ |  |   <| | | | |
 * \__, |_| |_|\___|_|  |_|\_\_|_| |_|
 *  __/ |                             
 * |___/                              
 *
 * A PLUGIN TO PICKLE / UNPICKLE (INDICE-FREE) INDUCTIVE TYPES 
 *  
 *)
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst.
From MetaCoq.PCUIC Require TemplateToPCUIC PCUICToTemplate.

From MetaCoq.Template Require Import config monad_utils utils TemplateMonad.
From MetaCoq.Template Require Ast.
Require Import MetaCoq.Template.All.

Require Import PeanoNat.
Require Import Coq.Arith.Compare_dec. 
Require Import String.
Require Import List.
Import Nat MCMonadNotation. 

Import ListNotations.
Notation TM := TemplateMonad.
Delimit Scope template_scope with template.
Open Scope template_scope.
Lemma nat_eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intro n; induction n as [|n IHn]; intro m; destruct m as [|m].
  - now left.
  - now right.
  - now right.
  - destruct (IHn m); [left|right]; auto.
Defined.

(*** PICKLE / UNPICKLE **)

(* 
 * First we define Pickle / Unpickle as types
 *)
Require Import gentree. 
Definition Pickle (A: Type) := A -> Ntree.
Definition Unpickle (A: Type) := Ntree -> (option A). 
Definition pcancel {A: Type} (f: Pickle A) (g: Unpickle A) := forall (a: A), (g (f a)) = Some a.

(** 
 * Table for storing results 
 * The translation table will be used to store a pickle / unpickle function for an inductive.
 *)
Require Import gentree. 
Definition tsl_table := list(prod global_reference term).

Fixpoint lookupTable (gr: global_reference) (T: tsl_table) : option term :=
  match T with
    nil => None
  | ((x, y)::tr) => if gref_eq_dec x gr then Some y else lookupTable gr tr
  end.

(** We define some auxilary function doing interesting stuff on terms 
    Some are taken from Marcel's work
**)

(** 
 * We need to be able to count the # of uniform / non-uniform parameters of a given inductive type. The code is by @Marcel.
 *)
Module countUniform.
  Open Scope nat_scope.
  Require Import List String.
  Require Import PeanoNat.
  Import Nat MCMonadNotation. 
Require Import MetaCoq.Template.All.
 From MetaCoq.PCUIC Require Import PCUICAst (* PCUICAst PCUICAstUtils PCUICInduction *) PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration. 

  Fixpoint getMinChain k t cl max : option nat :=
  match t with
  | tRel n => if   n =?  k then
               Some 0
             else
               None
  | tApp t1 t2 =>
    m <- getMinChain k t1 (S cl) max;;
      match t2 with
      | tRel n =>
        if n =? k+cl-max then
          Some (S m)
        else
          Some m
      | _ => Some m
      end
  | _ => None
  end.

(* check correctness *)
Fixpoint countOfCtor (k:nat) (max:nat) (c:term) {struct c} : nat :=
  match c with
    tRel _ => max
  | tProd _ t1 t2 => min (countOfCtor k max t1) (countOfCtor (S k) max t2)
  | tApp t1 t2 =>
    min (
    match getMinChain k c 0 max with
      None => countOfCtor k max t1
    | Some x => x
    end)
          (countOfCtor k max t2)
  | _ => max
  end.

Fixpoint collect_prods (t:term) : list (context_decl) :=
  match t with
  | tProd n t1 t2 => (vass n t1)::collect_prods t2
  | _ => []
  end.
Definition count_prods (t : term) : nat := #|collect_prods t|.

Definition getParamCount (ind:one_inductive_body) (n0:nat) : nat :=
  fold_right (fun c m => min m (countOfCtor 0 (count_prods (ind.(ind_type))) (snd(fst c)))) n0 ind.(ind_ctors).
End countUniform. 
(** End of code for counting parameters **)

(* Extract the types from a context_decl *)
Fixpoint typeList (l: list context_decl) : list term :=
  match l with
   x::xr => (decl_type x)::(typeList xr)
  | nil => nil end. 

(* 
   Takes a chain of terms (e.g. T1 ; T2 ; T3 ; t4 ] and a term (representing types) and creates 
   T1 -> (pickle T1) -> ... -> term
 *)

Definition nAnon := mkBindAnn nAnon Relevant.
Definition nNamed name := mkBindAnn (nNamed name) Relevant.

Fixpoint GeneralChain
         (l: list term) (*  *)
         (appterm: term) (* *)
         (t: term) : term := 
  match l with
    nil => t
  | (x::xr) => (tProd nAnon x (tProd nAnon (tApp appterm [(tRel 0)]) (GeneralChain xr appterm t)))
  end.

Definition pickleChain (l: list term) (t: term) : term := 
  GeneralChain l <% Pickle %> t
.

Fixpoint collect_prods (t:term) : list (context_decl) :=
  match t with
  | tProd n t1 t2 => (vass n t1)::collect_prods t2
  | _ => []
  end.
Definition count_prods (t : term) : nat := #|collect_prods t|.

(* 
   Takes a chain of terms (e.g. T1 ; T2 ; T3 ; t4 ] and a term (representing types) and creates 
   fun A: T1 (fun Ap: (pickle T1) -> ... -> term
 *)

Fixpoint pickleChainLambda (l: list term) (t: term) : term := 
  match l with
    nil => t
  | (x::xr) => (tLambda nAnon x
                      (tLambda nAnon
                               (tApp <% @Pickle %> [(tRel 0)])
                               (pickleChainLambda xr t)
                      )
             )
  end.

(*
  Helper function to annotate a list with element indices (used for generating unique indices for pickle / unpickle
 *)
Fixpoint annoteListWithIndices {A: Type} (l: list A) (start : nat) : list (nat * A) :=
  match l with
    x::xr => (start, x)::(annoteListWithIndices xr (S start))
  | nil => nil 
  end.

(** Helper function to quote a constant natural number **)
Fixpoint quoteNumber (n: nat) := match n with
                                 0 => <% 0 %>
                               | (S n) => (mkApp <% S %> (quoteNumber n))
                               end.

(**
We need a sequence function with an adjustable step size 
(Since we add pickle T_i arguments)
 **)
Fixpoint seq' (start : nat) (step: nat) (len: nat) :=
  match len with
  | 0 => nil
  | (S n) => start :: (seq' (start + step) step n)
  end.                 
(** 
 *  Zips over 2 Lists 
 *  (We use it for generating calls to pickle / unpickle a type with parameters since there we 
 *  interleave the parameters and their respective pickle types) 
 *)
Fixpoint zip {A: Type} (l1 l2: list A)  :=
  match (l1, l2) with
    (x::xr, y::yr) => x::y::(zip xr yr)
  | _ => nil end. 
(** Converts a list of option A -> list A by deleting all None Elements **)
Fixpoint DeleteNone {A: Type} (l: list (option A)) :=
  match l with
    (None) :: lr => DeleteNone lr
  | (Some x) :: xr => x::(DeleteNone xr)
  | nil => nil end.                    
(** 
 *  Since move from type A -> B -> C -> X (A, B, C, D are parameters of the inductive type T)
 * to A -> (pickle A) -> B -> ... fix ... (pickle B) -> C -> (pickle C) -> (pickle X)
 * the types are not where they used to be, when the type was constructed. 
 * Depending on wether the parameter is uniform or not we can calulate where it is now.
 * Correspindingly, the matching pickle function can be found at index  
 * a+1+ (n-i)*2
 * This shifts, when non-uniform parameters come into play
 *)
Definition whereIsPickle (a: nat) (c: nat) (nunip: nat) (i: nat) : nat := 
  if lt_dec i nunip then  a+(c-i)*2-1 +1 else  a+(c-i)*2-1 .
(* The type is one above the pickle *)
Definition whereIsType (a: nat) (c: nat) (nunip: nat) (i: nat) :=  (whereIsPickle a c nunip i)+1.
(**
   myLift recursively lifts  terms (used for lifting in translate for inductives etc).
 **)
Fixpoint myLift (a: nat) (c: nat) (nuni: nat)  (t: term) : term :=
  match t with
    tApp t1 t2 => tApp (myLift a c nuni t1) (List.map (myLift a c nuni) t2)
  | tProd tn t1 t2 => tProd tn (myLift a c nuni t2) (myLift a c nuni t2)
  | tRel n => tRel (whereIsType a c nuni n)
  | x => x end.                       

(** 
 * This function generates the pickle term for a term t. The term t represents the type (with parameters applied)
 * (E.g. it generates a function which can  be applied to the element of type t)
 * The cases are 
 * - tRel => it is a parameter -> lift it 
 * - tInd => lookup the translation in the translation table, if it is None we will return None 
 * - tApp => If we encouter a call (f a:T1 b:T2 c:T3 d:T4) we shall call (pickle_f T1 pickle_T1 T2 pickle T2 ... pickle T4. Do do this we recursively translate to get the pickle functions and recursively lift (using myLift) to get where the types are now.
     
When translating the inductive we are currently pickeling, the uniform parameters can not be applied in the recursive call. The current is kind of hacky.
 *)

Fixpoint translate
         (ind: inductive) (* The inductive we are transalting *)
         (table: tsl_table)
         (a: nat) (* How many lambdas deep is the constructor buried *)
         (npars: nat)
         (nonunipars: nat)
         (t: term) : option term :=
  match t with
  | tInd ind u => (lookupTable (IndRef ind) table)
 
  | tRel n => Some (tRel (whereIsPickle a npars (npars-nonunipars) (n)))
  | tApp f alist =>
    (* We explicitely check wether we apply some terms to the type we are currently generating for. We assume the paramters to be in the same order.  *)
    let tfO := (translate ind table a npars nonunipars f) in
    let translatedApplications := DeleteNone (List.map (translate ind table a npars nonunipars) alist) in 
    match tfO with None => None |
                  Some tf =>
                                 (match f with
                                   (tInd x _) =>
                                   if eq_inductive x ind then
                                     Some (tApp tf (zip  (List.map (myLift (a) npars (npars-nonunipars)) (skipn (npars-nonunipars) alist)) (skipn (npars-nonunipars) translatedApplications))) else
                                     Some (tApp tf (zip  (List.map (myLift (a) npars (npars-nonunipars)) alist) translatedApplications))    
              | _ =>   Some (tApp tf (zip  (List.map (myLift (a) npars (npars-nonunipars)) alist) translatedApplications))    end  ) end                
  | _ => None 
  end.
(** 
 * To translate a field, we call translate with the correct arguments.
 *)
Definition  pickleField
            (ind: inductive) (* The inductive we are pickeling *)
            (field: context_decl)
            (n: nat) (* # of field we are pickeling *)
            (a: nat) (* How many lambdas deep is this constrcutor buried? *)
            (npars: nat) (* How many parameters does the type have *)
            (nonunipars : nat)
            (tab: tsl_table)
        : option term :=
      match field with
      | {| decl_type := t0;
           decl_name := dnn             
        |}  => 
         
   (translate ind tab a npars nonunipars t0) end. 
(** Pickeling a list of fields works by recursively pickeling every field.  **)           
Fixpoint generateFieldPickles
         (ind: inductive) (* The inductive we are pickeling *)
         (pfields : context) (* This constructors fields *)
         (cnum : nat) (* The number of this constructor *)
         (a : nat)    
         (npars: nat)
         (nonunipars: nat)
         (table: tsl_table) (* Translation table with stored stuff *)

  : list (term) :=
  match pfields with
  | nil => nil
  |  fld::xr =>
     match pickleField ind fld cnum a npars nonunipars  table with
     | (Some t) =>
       (tApp
          (t)
          [(tRel (a-cnum - 1))])
         ::(generateFieldPickles ind xr (S cnum) a npars nonunipars table)
       | _        =>   generateFieldPickles ind xr (S cnum) a npars nonunipars table
     end                                      
   end. 

(** This function can be used to pickle constant lists of type ty  **)
Fixpoint q_list_of_list_q (ty : term) (ts : list term) : term :=
  match ts with
  | [] => mkApp <%@nil%> ty
  | t :: ts => mkApps <%@cons%> [ty ; t ; q_list_of_list_q ty ts]
  end. 

Fixpoint lrep {A: Type} (l: A) (n: nat) :=
  match n with 0 => nil | (S n) => l::(lrep l n) end.

(** 
    The n-th field in the context is lifted down by n arguments. 
    This is useful for contexts obtained from dealing with constructors.
**)
Fixpoint maplift (l: context) (n: nat) :=
  match l with
    ({|
        decl_type := t0;
        decl_name := dnn;
        decl_body := db
      |}::xr) => {| decl_type :=  subst0 (((lrep (tRel 0) n))) t0;
                  decl_name := dnn;
                  decl_body := db
              |}::(maplift (xr) (S n)) | nil => nil end.
From MetaCoq.PCUIC Require Import TemplateToPCUIC.
Print TemplateToPCUIC. 
Definition generateMatch
           (tyDef : mutual_inductive_body)
           (refi: inductive)
           (refib: one_inductive_body)
           (matchee: term) (* Matchee *)
           (motive: term) (* Motive , type of the matchee *)
           (ti : term) (* Inductive term *)
                      (paramList: list nat)
           (table: tsl_table)
  :  term :=
    
    let ctors := (refib).(ind_ctors) in  
    let ctors' := annoteListWithIndices ctors 0 in
    let params := (rev'  (seq' 2 2 (ind_npars tyDef)))  in
    let npars  := (ind_npars tyDef) in
    let nunipars := (countUniform.getParamCount (TemplateToPCUIC.trans_one_ind_body refib) npars) in
    (* Count uniform and non-uniform parameters *)
    let nnonunipars := npars - nunipars in
    
    (** Generates the pickle for a constructor case **)                             
    let mkBranch :=
             (* i - number of ctor,
              * a - number of arguemnts to the ctor 
              * t - ctor term 
              *)
        (fun '(i, (name, t, a)) =>
           (**
            t' correctly replaces with the new parameters indices (which have changed since we have inserted pickle functions 
            **)
           let t'  := subst0 (rev' (ti :: (List.map tRel paramList))) (remove_arity (ind_npars tyDef) t) in
           (* t''' replaces the parameters with 0 ... npars, this makes generating the pickle functions easier, however we can't use the extracted context for generating the lambda  *)
           let t'' := subst0 (rev' (ti :: (List.map tRel (seq 0 npars)))) (remove_arity (ind_npars tyDef) t) in
           (* We only care about the contexts, since we need them to generate the terms *)
           let '(ctx, _) := decompose_prod_assum [] t' in
           let '(ctxp, _) := decompose_prod_assum [] t'' in
           (* What matters: ctx' is a list of the constructors fields such that the tRels are 
              the same for each element in the context (e.g. A -> A -> A => [tRel 0; tRel 0; tRel 0] *)
           let ctx' := maplift (rev ctxp) 0 in 
           let pfields :=  (generateFieldPickles refi  (ctx') 0 (a) (npars) nnonunipars (((IndRef refi,
                                                                         (tRel (2*nnonunipars + a + 1))
                                                                       ))::table)) in
           let u := it_mkLambda_or_LetIn ctx  (tApp
                                                     <% (NBranch) %>
                                                     [(quoteNumber i);  q_list_of_list_q <% Ntree %>  (rev' pfields) ] ) 
           in
               (a, u )
        ) in
    (tCase ((refi, 0), Relevant)  motive matchee  (List.map mkBranch ctors')) .

(**
 * Generates a list of indexes uniform / nonunform parameters positions   
 * Skips one index between uniform and nonuniform (since the fix is between them) 
 **)
Definition generateParamList (uniform: nat) (nonuni: nat) :=
 rev' ((seq' 1 2 nonuni) ++ (seq' ((2*nonuni)+2) 2 uniform)).

Definition addList (l: list nat) (n: nat) :=
  List.map (Nat.add n) l. 

Definition pickle_for_single_ind
           (mind: mutual_inductive_body)
           (refi : inductive)
           (ref   : term)
           (allparams : nat)
           (ind   : one_inductive_body)
           (table: tsl_table)
  : term :=
  (* Generate the function type *)
  let params := collect_prods ind.(ind_type) in
  let matchTerm := generateMatch in
  (* Count parameters *)
  let npars  := (ind_npars mind) in
  let nunipars := (countUniform.getParamCount (TemplateToPCUIC.trans_one_ind_body ind) npars) in 
  let nnonunipars := npars - nunipars in

  let uniparams := firstn nunipars params in
  let nuniparams := skipn nunipars params in


  (* Generate a list for the position of each parameter *)
  let paramList := generateParamList nunipars nnonunipars in

  (* Generate the new header *) 
               let  y := (generateMatch mind refi
                                                                        ind
                                                                        (tRel 0)
                                                                        (tLambda
                                                                           nAnon 
                                                                           (tApp
                                                                              ref
                                                                              (List.map (fun x => tRel (x+1)) paramList 
                                                                              )
                                                                           )
                                                                           <% Ntree %>
                                                                        )
                                                                        ref
                                                                        (List.map S paramList)
                                                                        table 
                     ) in 
                 let
                   x :=
                   
                  (tFix [mkdef _ (nNamed "pickle") (pickleChain (typeList nuniparams)
                                                                 (tProd nAnon
                                                                        (tApp ref (map (fun x => (tRel (x))) (rev (seq' 1 2 npars))))
                                                                        (<% Ntree %>)))
                                (pickleChainLambda (typeList nuniparams)
                                                   (tLambda nAnon
                                                            (tApp ref (map (fun x => (tRel (x))) paramList))

                                                            y
                                                   )
                                )                                
                                            
                                (2*nnonunipars) (* Recursion is on the last argument*)
                         ] 0)        
                 in
                   let x' :=  (pickleChainLambda (typeList uniparams)
                                                 x) in
                   (*npars <- tmEval cbv nunipars;;
                   tmPrint ("Uniform: ", npars);;
                   tmEval cbn ("plist: ", uniparams, nuniparams) >>= tmPrint;;
                   tmEval cbn ("plist: ", paramList ) >>= tmPrint;; *)

                    x'.
(*
  Extract the singlie inductive body, and derive pickle for it.
  Expects that the translation table is already filled
 *)

Definition pickle_for_ind
           (mind: mutual_inductive_body)
           (ind0: inductive)
           (ref: term)
           (table: tsl_table)
  : TemplateMonad term :=
   match nth_error mind.(ind_bodies) 0 with
    None => tmFail "err" 
   | Some b =>
     let i0 := inductive_ind ind0 in
     let ntypes := List.length (ind_bodies mind) in
     let x := pickle_for_single_ind mind ind0 ref mind.(ind_npars) b table in 
     tmReturn x
  end.
(** Pickle *)
(* Get the [one_inductive_body] from a [mutual_inductive_body].
   Fails if there is more than one. *)
Definition get_ind_body (tyDef : mutual_inductive_body)
  : TemplateMonad one_inductive_body :=
  match ind_bodies tyDef with
  | [body] => tmReturn body
  | _ => tmFail "Unimplemented (mutually recursive types)"
  end.
Require Import String.

Definition mk_instance_name := fun (s: string) => concat ""  ["Pickle_"; s].
Definition augmentTable (ind0: inductive) (t: term) (tab : tsl_table) :=
  let z :=  ((IndRef ind0, t)::tab) in 
  tmReturn z.
Definition when (b : bool) (u : TM unit) : TM unit :=
  if b then u else tmReturn tt.

Print one_inductive_body.
Print List.fold_left. 
Definition unify {A: Type} (l: list (list A)) :=
  List.fold_left  (fun a b => a++b) l [].
Print tProd.
(** Extract the inductives from a term *)
Fixpoint getInductives
           (t: term)
  : list inductive :=
  match t with
  | tInd ind u => [ind]  
  | tEvar ev args => unify (List.map getInductives args)
  | tApp f args => unify ((getInductives f)::List.map getInductives args)
  | tProd name t1 t2 => (getInductives t1) ++ (getInductives t2)
  | tSort  t1 => []                     
  | _ => []                  
  end.
Fixpoint in_dec {A: Type} (decA: A -> A -> bool) (a: A) (l: list A) :=
match l with
  nil => false
| x::xr => if decA x a then true else in_dec decA a xr end. 
Fixpoint nodup {A: Type} (decA: A -> A -> bool) (l : list A)  : list A :=
    match l with
      | [] => []
      | x::xs => if in_dec decA x xs then nodup decA xs else x::(nodup decA xs)
    end.


(** 
 *  Guesses the inductives which will need to be pickled / unpickled before ind0 can be pickled.
 *  Currently guesing only works one level deep -> if multiple levels are needed 
 *  the translation table has to be provided manually.
 *)
Definition guessInductives
           (mind: mutual_inductive_body)
           (ind0: inductive)
           (ref: term)
  : TM (list inductive) :=
   match nth_error mind.(ind_bodies) 0 with
    None => tmFail "err" 
   | Some b =>
     let ctors := (ind_ctors b) in
     let inductives := nodup eq_inductive (List.filter (fun a => negb (eq_inductive a ind0)) (unify (List.map (fun '(i, t, n) => getInductives t) ctors))) in
     tmReturn inductives
   end.

(** Helper to 'map' with template monad functions. Taken from coq-ceres *)
Definition tmTraverse {A B} (f : A -> TM B)
  : list A -> TM (list B) :=
  fix _traverse xs :=
    match xs with
    | [] => tmReturn []
    | x :: xs =>
      y <- f x ;;
      ys <- _traverse xs ;;
      tmReturn (y :: ys)
    end.
(** 
 * Pickles a single inductive, assuming the translation table is already filled.
 *)
Definition pickleSingle
           (t : Ast.term)
           (table: tsl_table) :=
  match t with
  | Ast.tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0);;
      tyOne <- get_ind_body decl ;;
      bodyDef <-   (pickle_for_ind (decl) ind0 (t) table) ;; 
      tmReturn bodyDef
  | _ => tmFail "not inductive" end.               


Definition pickle
           (t : Ast.term) (* Term to generate pickle for, must be a quoted inductive *)
           (define: bool) (* Flag: Shall we define the function or just ignore this for now *)
           (guessy: bool) (* Flag: Shall we try to guess and pickle other indcutives first *)
           (table: tsl_table) (* Translation Table *)
  : TemplateMonad (tsl_table)
  :=
    (* Recursively pickle the inductives for the translation table *)
    let  pickleMultiple := fix pmm (t: list (inductive)) (tab: tsl_table) : TM tsl_table :=
                             match t with 
                               nil => tmReturn tab
                             | (t::tr) =>
                               bodyDef <- pickleSingle (Ast.tInd t []) tab ;;
                               tab' <- (augmentTable t bodyDef tab);;
                               tab'' <- pmm tr tab';;
                               tmReturn tab''
                             end
    in
    let genTable (guessy: bool) (gi: list inductive) (tab: tsl_table) : TM tsl_table :=
        if guessy then
          table <- pickleMultiple gi tab;;
          tmReturn table
        else
          tmReturn tab
    in                
    match t with
    | Ast.tInd ind0 _ =>
      decl <- tmQuoteInductive (inductive_mind ind0);;
      tyOne <- get_ind_body decl ;;
      inductives <- guessInductives (decl) ind0 (t);;
      table <- genTable guessy inductives table;; 
      bodyDef <-   (pickleSingle (t) table) ;; 
      if define then (
          body <- tmUnquote bodyDef ;;
      res' <- tmEval cbn (my_projT2 body) ;;
      y <- (get_ind_body decl);;
      name <- tmEval all (mk_instance_name (ind_name y));;
       tmPrint "Sucess";;
       z <- (augmentTable ind0 bodyDef table) ;;
        tmDefinitionRed name (Some cbv) res';;    
        tmReturn z)     else (
          print_nf bodyDef;;
          body <- tmUnquote bodyDef ;;
      res' <- tmEval cbn (my_projT2 body) ;;
      y <- (get_ind_body decl);;
      name <- tmEval all (mk_instance_name (ind_name y));;
       tmPrint "Sucess";;
       z <- (augmentTable ind0 bodyDef table) ;;
          tmReturn z)
        
     | _ =>
      tmFail "Not an inductive"
     
    end.
(**
   Pickle' does not try to infer which inductives need to be pickled first.
 **)
Definition pickle'
           (t : Ast.term) (* Term to generate pickle for, must be a quoted inductive *)
           (define: bool) (* Flag: Shall we define the function or just ignore this for now *)
           (subtypes: list term) (* List of types to pickle before pickling the rest, will be pickled in List Order *)
           (define: bool)
           (tab: tsl_table)
  :=
        let  genTab := fix pmm (t: list (term)) (tab: tsl_table) : TM tsl_table :=
                             match t with 
                               nil => tmReturn tab
                             | ((Ast.tInd t _)::tr) =>
                               bodyDef <- pickleSingle (Ast.tInd t []) tab ;;
                               tab' <- (augmentTable t bodyDef tab);;
                               tab'' <- pmm tr tab';;
                               tmReturn tab''
                             | _ => tmFail "Not inductive"           
                             end
        in
        tab <- genTab subtypes tab;; 
        tab' <- pickle t define false tab;;
        tmReturn tab'. 

Notation "'Derive' 'Pickle' 'for' T" := (pickle <% T %> true true []) (at level 0).
(* Define a notation for manually supplying which inudctives should be pickled first *)
Notation "'Derive' 'pickle' 'for' T 'with' z" :=
  (pickle' <% T %> true z true [])  (at level 0).
(* Vectors do not work with this scheme *)
 Fail MetaCoq Run (t1 <- pickle <% nat %> false [];;pickle <% Vector %> true t1).


(** 
 *  Generating unpickle functions 
 *
 *)

(* Define chain functions, (similiar to PickleChain) *) 
Fixpoint unpickleChain (l: list term) (t: term) : term := 
  match l with
    nil => t
  | (x::xr) => (tProd nAnon x (tProd nAnon (tApp <% @Unpickle %> [(tRel 0)]) (unpickleChain xr t)))
  end.
Fixpoint unpickleChainLambda (l: list term) (t: term) : term := 
  match l with
    nil => t
  | (x::xr) => (tLambda nAnon x
                      (tLambda nAnon
                               (tApp <% @Unpickle %> [(tRel 0)])
                               (unpickleChainLambda xr t)
                      )
             )
  end.

Definition generateParamListUP (uniform: nat) (nonuni: nat) :=
 rev' ((seq' 1 2 nonuni) ++ (seq' (2*(nonuni-1)+2) 2 uniform)).

Fixpoint myLiftUnpickle (a: nat) (c: nat) (nuni: nat)  (t: term) : term :=
  match t with
    tApp t1 t2 => tApp (myLift a c nuni t1) (List.map (myLiftUnpickle a c nuni) t2)
  | tProd tn t1 t2 => tProd tn (myLift a c nuni t2) (myLiftUnpickle a c nuni t2)
  | tRel n => tRel (whereIsType a c nuni n)
  | x => x end.                       

(** 
 * The procedure is similiar to translatePickle, however we need to take 
 * an additional parameter d - how many lambdas deep we are into account
 *)

Fixpoint translateUnpickle
         (ind: inductive) (* The inductive we are transalting *)
         (table: tsl_table)
         (a: nat)
         (npars: nat)
         (nonunipars: nat)
         (d: nat)
         (t: term) : option term :=
  match t with
  | tInd ind u => (match (lookupTable (IndRef ind) table) with
                    (Some y) => (Some (lift0 d y))
                  | None => None end )
  | tRel n => Some (tRel (whereIsPickle a npars (npars-nonunipars) (n)))
  | tApp f alist =>
    (* We explicitely check wether we apply some terms to the type we are currently generating for. We assume the paramters to be in the same order.  *)
    let tfO := (translateUnpickle ind table a npars nonunipars (d) f) in
    let translatedApplications := DeleteNone (List.map (translateUnpickle ind table a npars nonunipars d) alist) in 
    match tfO with None => None |
                  Some tf =>
                                 (match f with
                                   (tInd x _) =>
                                   if eq_inductive x ind then
                                     Some (tApp tf (zip  (List.map (myLiftUnpickle (a) npars (npars-nonunipars)) (skipn (npars-nonunipars) alist)) (skipn (npars-nonunipars) translatedApplications))) else
                                     Some (tApp
                                             tf
                                             (zip
                                                (List.map
                                                   (myLiftUnpickle
                                                      (a)
                                                      npars
                                                      (npars-nonunipars)
                                                   )
                                                   alist)

                                                translatedApplications)
                                          )    
              | _ =>   Some (tApp tf (zip  (List.map (myLift (a) npars (npars-nonunipars)) alist) translatedApplications))    end  ) end                
  | _ => None

  end.

Definition  unpickleField
            (ind: inductive) (* The inductive we are pickeling *)
            (field: context_decl)
            (n: nat) (* # of field we are pickeling *)
            (a: nat) (* How many lambdas deep is this constrcutor buried? + offset from matching on the list *)
            (npars: nat) (* How many parameters does the type have *)
            (nonunipars : nat)
            (tab: tsl_table)
            (d: nat)
        : option term :=
      match field with
      | {| decl_type := t0
        |}  => 
         
   (translateUnpickle ind tab a npars nonunipars d t0) end. 

Fixpoint generateFieldUnpickles
         (paramList: list nat) (* List of parameters to pass *)
         (ind: inductive) (* The inductive we are pickeling *)
         (indTerm: term) (* The type we shall return *)
         (cTerm: term) (* Constructor gen with paramaters already set *)
         (pfields : context) (* This constructors fields *)
         (default: term)
         (cnum : nat) (* The number of this constructor *)
         (a : nat)    
         (npars: nat)
         (nonunipars: nat)
         (nargs: nat) (* Number of arguments this constructor takes *)
         (i: nat) (* Number of current argument *)
         (table: tsl_table) (* Translation table with stored stuff *)

  :  (term) :=
    let optionInd := ((mkInd ((MPfile ["Datatypes"; "Init"; "Coq"],
                        "option")) 0)) in 

  match pfields with
  | nil =>
      (* All arguments have been unpickled successfully => [tRel nargs; ... ; tRel 0] is the list of arguments we can pass to 
         to the constructor *) 
      
      (mkApps
         <% @Some %>
         [(lift0 (i) indTerm) (* We are c lambdas below the call *) ;
         (mkApps
            (mkApps
               (tConstruct  ind cnum [])
               (List.map (fun x => (tRel (x+2+a))) paramList))
            (List.map tRel (rev' (seq 0 (nargs)))) )
         ]) 
         
             
  |  fld::xr => 
     match unpickleField ind fld cnum  (S a) npars nonunipars  table i with
     | (Some t) => 
       (tCase (* We match on the unpickeled field => if it is Some x we can proceed, else we return the default *)
          ((optionInd, 1), Relevant)
          (tLambda nAnon
                  (mkApp <% option %>
                         (myLiftUnpickle
                             (a+1)
                             npars
                             (npars-nonunipars)
                             (decl_type fld)
                          ) 
                   ) 
               (tApp <% option %>  [(lift0 (i+1) indTerm)])         
        )
      (tApp
          t
          [(tRel (1+2*i+(i)))]) 
       [
       (1,
         (tLambda nAnon  (myLiftUnpickle
                             (a+1)
                             npars
                             (npars-nonunipars)
                             (decl_type fld)
                        )
                  
          (generateFieldUnpickles paramList ind indTerm cTerm xr default cnum (a+1) npars nonunipars nargs (S i) table) 
         )        
       );
       (0,  (lift0 i default))
       ]) 
         
       | _ => (tRel 0) (* Shouldn't happen *)   
     end
  end.

(** 
 *   For a fixed n, generates a match which only matches with lists of length n
 *   Lists of a different length => default is returned.
 *   The matchterm is not lifted (else the list elements could not be used) but default is 
 *   (Is used for matching on lists of pickeled constructor fields)
 *) 
Fixpoint  matchListNWith
           (n: nat)  (* How many elements ** must ** this list have *)
           (matchee: term) (* Which list to match on *)
           (type: term) (* The element type of the list (e.g. list of A -> A *)
           (rettype : term) (* Return type *)
           (default: term) (* Term to output in the branches which do not correspond to the list having exactly n elements *)
           (matchTerm : term)
           (depth: nat)
           {struct n}
  : term :=
  let listInd := ((mkInd ((MPfile ["Datatypes"; "Init"; "Coq"],
                        "list")) 0)) in 
  match n with
    0 => (* Output the term *)
     (tCase
        ((listInd, 0), Relevant)
        (tLambda nAnon
                 (mkApp <% list %> type)
                 (lift0 (depth+1) rettype)        
        )          
       (tRel 0)
       [(0,  matchTerm); (* The matchterm is ** not ** lifted *)
       (2,
         (tLambda nAnon type
                 (tLambda nAnon (mkApp <% list %> type)
                          (lift0 (depth+2) default)
                 )
         )        
       )
      ])
    
  | S n =>
    (tCase
       ((listInd, 0), Relevant)
       (tLambda nAnon
                 (mkApp <% list %> type)
                 (lift0 (depth+1) rettype)
                 
        )  
       matchee
       [(0,  (lift0 depth default) );
       (2,
        (tLambda nAnon type
                 (tLambda nAnon (mkApp <% list %> type)
                       (matchListNWith n   (tRel 0) type rettype default matchTerm (depth+2)) 
                 )         
       ))
      ]) end. 

Definition generateUnpickleBranches
           (tyDef : mutual_inductive_body)
           (refi: inductive)
           (refib: one_inductive_body)
           (ti : term) (* Inductive term *)
           (paramList: list nat)
           (table: tsl_table)
  :  (list (nat * term)) :=
    
    let ctors := (refib).(ind_ctors) in  (* A list of the constructors *)
    let ctors' := annoteListWithIndices ctors 0 in (* Store the number for each constructor *)
    let npars  := (ind_npars tyDef) in (* Count the number of parameters  *)
    (* Count uniform and non-uniform parameters
       to pass them along to the function whcih generates the pickle for the fields
     *)
    let nunipars := (countUniform.getParamCount (TemplateToPCUIC.trans_one_ind_body refib) npars) in (* Number of uniform paramaters *)
    let nnonunipars := npars - nunipars in
    
     (* Generates a single branch given an element of ctors' (i.e. a pair of metacoq constructor  *)
     let mkBranch :=
         (fun '(i, (name, t, a)) =>
           let t'' := subst0 (rev' (ti :: (List.map tRel paramList))) (remove_arity (ind_npars tyDef) t) in 
           let t''' := subst0 (rev' (ti :: (List.map tRel (seq 0 npars)))) (remove_arity (ind_npars tyDef) t) in
           let '(ctx, t') := decompose_prod_assum [] t'' in
           let '(ctxp, t') := decompose_prod_assum [] t''' in 
           let ctx' := maplift (rev ctxp) 0 in
           (* Count the number fo fields *)
           let depth := (List.length ctx')  in
           let pfields :=  (generateFieldUnpickles
                                                   paramList
                                                   refi
                                                   (lift0 (2*depth) (mkApps ti (List.map (lift0 0) (List.map (fun x => (tRel (x+3))) paramList))))
                                                    (mkApps (tConstruct  refi i [])   (List.map (fun x => (tRel (x+3+2*depth))) paramList))
                                                   (ctx')
                                                   (lift0 (2*depth) (mkApp
                                                      <% @None %>
                                                      (mkApps ti (List.map (lift0 0) (List.map (fun x => (tRel (x+3))) paramList)))))
                                                   i
                                                   (2*(depth)+1)
                                                   (npars)
                                                   nnonunipars
                                                   depth
                                                   0
                                                   (((IndRef refi,
                                                                         (tRel (2*nnonunipars + 2*(depth)+3 ))
                                                    ))::table)
                           ) 
           
           in 
               (i, 
                          (matchListNWith
                             depth
                             (tRel 0)
                             <% Ntree %>
                             (mkApp
                                <% option %>
                                (mkApps ti (List.map (lift0 0) (List.map (fun x => (tRel (x+3))) paramList))))
                             (mkApp
                                <% @None %>
                                (mkApps ti (List.map (lift0 0) (List.map (fun x => (tRel (x+3))) paramList))))
                               pfields
                             0  
                            )
                        )
        ) in
    (* tmPrint "Branches";;
     tmEval cbv branches >>= tmPrint;; *)
     List.map mkBranch ctors' . 
(**
   Takes a list [(t1, term1); ... ; (tn, termn)] and generates 
   if compare = t1 then term1 else  ... if compare = tn then termn else default 
 **)
Fixpoint generateNatCases
           (cases:list (nat * term))
           (default: term) (* For else branch *)
           (type: term)
           (compare: term)
  :=
    let boolInd := ((mkInd ((MPfile ["Datatypes"; "Init"; "Coq"],
                        "bool")) 0)) in 
    match cases with nil => default
                |   ((x, t) ::xr) => (tCase
                                      ((boolInd, 0), Relevant)
                                      (tLambda nAnon
                                               <% bool %>
                                               (lift0 1 type)
                                      )         
                                      (tApp <% Nat.eqb %> [(quoteNumber x); compare])
                                      [(0, t); (0,  (generateNatCases xr default type compare) ) ])
    end.
                                             

Definition unpickle_for_single_ind
           (mind: mutual_inductive_body)
           (refi : inductive)
           (ref   : term)
           (allparams : nat)
           (ind   : one_inductive_body)
           (table: tsl_table)
  :  term :=
  (* Generate the function type *)
  let params := collect_prods ind.(ind_type) in
  let matchTerm := generateMatch in
   
  let npars  := (ind_npars mind) in
  let nunipars := (countUniform.getParamCount (TemplateToPCUIC.trans_one_ind_body ind) npars) in 
  let nnonunipars := npars - nunipars in

  let uniparams := firstn nunipars params in
  let nuniparams := skipn nunipars params in

  (* Generate a list for the position of each parameter *)
  let paramList := generateParamList   nunipars nnonunipars in

  (* Inductive for gentree nat *)
  let gInd := ((mkInd ((MPfile ["gentree"; "gherkin"],
                        "Ntree")) 0)) in
  let appli :=                                           (tApp
                                                                                           <% @None %>
                                                                                           [(mkApps ref
                                                                                                    (List.map (fun x => tRel (x+3)) paramList))]
                                                         ) in

  let branches := generateUnpickleBranches mind refi ind ref paramList table in 
  
  let x :=  (tFix [mkdef _ (nNamed "unpickle") (unpickleChain (typeList nuniparams)
                                                            (tProd nAnon
                                                                   (<% Ntree %>)
                                                                   (tApp <% @option %>
                                                                        [(tApp ref (map (fun x => (tRel (x))) (rev (seq' 2 2 npars))))]
                                                                       )))
                         (unpickleChainLambda (typeList nuniparams)
                                                   (* Match on the gentree argument *)
                                                   (tLambda nAnon <% Ntree %>
                                                            (tCase
                                                               ((gInd, 1), Relevant)
                                                               (tLambda nAnon <% Ntree %>                                                                                                                      (tApp
                                                                                                                                                                                                            <% @option %>
                                                                                                                                                                                                            [(mkApps ref (List.map (fun x => tRel (x+2)) paramList))]
                                                                                                                                                                                                         )
                                                               )
                                                                 (tRel 0)       

                                                                   [
                                                                     (* If it is a Leaf ignore it (we only pickle into Branch *)
                                                                     (1, 
                                                                      (tLambda nAnon <% nat %>
                                                                               (tApp <% @None %>  [(mkApps ref (List.map (fun x => tRel (x+2)) paramList))])
                                                                       ));

                                                                     (* If its a branch, we can try to unpcikle (-> nat. eq_dec on branch number ,etc  *)
                                                                     (2,
                                                                      (tLambda nAnon <% nat %>
                                                                               (tLambda nAnon <% list (Ntree) %>
                                                                                        (generateNatCases
                                                                                           branches 
                                                                                           appli
                                                                                             (tApp
                                                                                           <% @option %>
                                                                                           [(mkApps ref
                                                                                                    (List.map (fun x => tRel (x+3)) paramList))]
                                                                                           

                                                                                             )
                                                                                             (tRel 1)
                                                                                             
                                                                      ))
                                                                     ))]   
       
                                                            
                                                   ) 
                               ))                                
                                            
                                (2*nnonunipars) (* Recursion is on the last argument*)
                         ] 0)        
                 in
                   let x' :=  (unpickleChainLambda (typeList uniparams)
                                                 x) in x'. 

Definition unpickle_for_ind
           (mind: mutual_inductive_body)
           (ind0: inductive)
           (ref: term)
           (table: tsl_table)
  : TemplateMonad term :=
   match nth_error mind.(ind_bodies) 0 with
    None => tmFail "err" 
   | Some b =>
     let i0 := inductive_ind ind0 in
     let ntypes := List.length (ind_bodies mind) in
     let x := unpickle_for_single_ind mind ind0 ref mind.(ind_npars) b table in 
     tmReturn x
  end.

Definition mk_up_name := fun (s: string) => concat ""  ["Unpickle_"; s].
About tmDefinitionRed.

Definition unpickleSingle
           (t : Ast.term)
           (table: tsl_table) :=
  match t with
  | Ast.tInd ind0 _ =>
       decl <- tmQuoteInductive (inductive_mind ind0);;
      tyOne <- get_ind_body decl ;;
      bodyDef <-   (unpickle_for_ind (decl) ind0 (t) table) ;; 
      tmReturn bodyDef
  | _ => tmFail "not inductive" end.               

Definition unpickle (t : Ast.term) (define: bool) (guessInductivesP: bool)  (table: tsl_table)
  : TemplateMonad (tsl_table)
  :=
let  unpickleMultiple := fix pmm (t: list (inductive)) (tab: tsl_table) : TM tsl_table :=
                             match t with 
                               nil => tmReturn tab
                             | (t::tr) =>
                               bodyDef <- unpickleSingle (Ast.tInd t []) tab ;;
                               tab' <- (augmentTable t bodyDef tab);;
                               tab'' <- pmm tr tab';;
                               tmReturn tab''
                             end
    in
    let genTable (guessy: bool) (gi: list inductive) (tab: tsl_table) : TM tsl_table :=
        if guessy then
          table <- unpickleMultiple gi tab;;
          tmReturn table
        else
          tmReturn tab
    in                
      
    match t with
     | Ast.tInd ind0 _ =>
      tmPrint "Is inductive";; 
      decl <- tmQuoteInductive (inductive_mind ind0);;
      tyOne <- get_ind_body decl ;;
      inductives <- guessInductives (decl) ind0 (t);;
      table <- genTable guessInductivesP inductives table;;  
      bodyDef <-   (unpickle_for_ind (decl) ind0 (t) table) ;;
      print_nf bodyDef;;
        if define then (body <- tmUnquote bodyDef ;;
      res' <- tmEval cbn (my_projT2 body) ;;
      y <- (get_ind_body decl);;
      name <- tmEval all (mk_up_name (ind_name y));;
       tmPrint "Sucess";;
       z <- (augmentTable ind0 bodyDef table) ;;
             tmDefinitionRed name (Some cbv) res';;    
             tmReturn z )    else (
body <- tmUnquote bodyDef ;;
      res' <- tmEval cbn (my_projT2 body) ;;
      y <- (get_ind_body decl);;
       z <- (augmentTable ind0 bodyDef table) ;;
      tmReturn z )
          
        
     | _ =>
      tmFail "Not an inductive"
     
     end.

Definition unpickle'
           (t : Ast.term) (* Term to generate pickle for, must be a quoted inductive *)
           (define: bool) (* Flag: Shall we define the function or just ignore this for now *)
           (subtypes: list term) (* List of types to pickle before pickling the rest, will be pickled in List Order *)
           (define: bool)
           (tab: tsl_table)
  :=
        let  genTab := fix pmm (t: list (term)) (tab: tsl_table) : TM tsl_table :=
                             match t with 
                               nil => tmReturn tab
                             | ((Ast.tInd t _)::tr) =>
                               bodyDef <- unpickleSingle (Ast.tInd t []) tab ;;
                               tab' <- (augmentTable t bodyDef tab);;
                               tab'' <- pmm tr tab';;
                               tmReturn tab''
                             | _ => tmFail "Not inductive"           
                             end
        in
        tab <- genTab subtypes tab;; 
        tab' <- unpickle t define false tab;;
        tmReturn tab'. 



Notation "'Derive' 'Unpickle' 'for' T" := (unpickle <% T %> true true []) (at level 0).
Notation "'Derive' 'unpickle' 'for' T 'with' z" :=
  (unpickle' <% T %> true z true [])  (at level 0).




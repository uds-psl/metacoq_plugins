(** implementation of a flag system in MetaCoq **)

Require Import MetaCoq.Template.All.
Import MCMonadNotation.
Open Scope bs.
Class mode (s:string) := { state: bool }.
Import String (append).

Print tmExistingInstance.
Print tmFreshName.
Print global_reference.

Definition changeMode (m:string) (value:bool) : TemplateMonad unit :=
  ename <- tmEval all m;;
  name <- tmFreshName ename;;
  tmDefinition name ({| state := value |}:mode m);;
  tmExistingInstance (VarRef name);;
  tmMsg (append (append "The mode " m) (append " was " (if value then "set" else "unset"))).

Definition getMode (m:string) : TemplateMonad bool :=
  v <- tmInferInstance None (mode m);;
  val <- tmEval all (
    match v with
      my_None => false
    | my_Some v' => @state _ v'
    end
  );;
  tmReturn val.

Definition getName (x : nat -> nat) :=
  x <- tmEval cbv x;;
  t <- tmQuote x;;
  match t with 
  | Ast.tLambda ({| binder_name := nNamed na |}) _ _ => tmReturn na
  | _ => tmReturn ""%bs
  end.


Notation "'Set' n" := (
  name <- getName (fun n:nat => n);;
  changeMode name true
  )(at level 8).
Notation "'Unset' n" := (
  name <- getName (fun n:nat => n);;
  changeMode name false
  )(at level 8).



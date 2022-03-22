(**  **)

(*** de_bruijn_print: Pretty print for terms with bruijn indices ***)

(**

For a complete pretty print with names
unquote and use Coqs Print Command

It is useful as debugging if a term does not type

There is the pure pretty print function but
this function uses too little parenthesis 
and does not print tRels and tInd in a useful way
 **)

Require Import MetaCoq.Template.All.
Open Scope bs.
Require Import List.
Require Import Program Arith Lia PeanoNat.
Import ListNotations MCMonadNotation Nat.

(** could use string_of_nat **)
Definition natToString := string_of_nat.
Infix ":s" := String.String (at level 73).
(** normally ^ **)
Infix "+s" := String.append (at level 72).
Definition linebreak := nl.

Definition join := String.concat "".
Definition append := String.append.

(** needed for mutual inductive types **)
Definition getInductiveName (ind:kername) (indIndex:nat) :TemplateMonad string :=
  ind <- tmQuoteInductive ind;;
  tmEval lazy match nth_error (ind).(ind_bodies) indIndex with
           | None => ""
           | Some b => b.(ind_name)
              end.

Definition getConstructName (ind:kername) (indIndex:nat) (consIndex:nat) :TemplateMonad string :=
  ind <- tmQuoteInductive ind;;
  tmEval lazy match nth_error (ind).(ind_bodies) indIndex with
           | None => ""
           | Some b => match nth_error b.(ind_ctors) consIndex with
                        None => ""
                      | Some cb => cb.(cstr_name)
                      end
           end.

Definition nameToString (s:name) : string :=
  match s with
    nAnon => "_"
  | nNamed s => s
  end.

Definition concatString (xs:list string) : string :=
  fold_left (fun a b => a +s b) xs "".

(** auxiliary function to generate the tring **)
Fixpoint bruijn_print_aux (t:term) : TemplateMonad string :=
  match t with
  | tRel n => tmReturn("R" :s (natToString n))
  | tVar ident => tmReturn(ident)
  | tEvar n xs => tmReturn "TODO:EVAR"
  | tSort univ => 
    tmReturn "tSort ?"
  | tProd n t t2 => match n.(binder_name) with
                   | nAnon => s1 <- bruijn_print_aux t;;
                             s2 <- bruijn_print_aux t2;;
                             tmReturn("(":s append s1 (append ") -> " s2))
                   | nNamed s => s1 <- bruijn_print_aux t;;
                                s2 <- bruijn_print_aux t2;;
                                tmReturn("∀ (" +s s +s (" : "+s s1) +s "), " +s s2)
                   end
  | tLambda s t t2 => s1 <- bruijn_print_aux t;;
                    s2 <- bruijn_print_aux t2;;
                    tmReturn("λ ("+s match s.(binder_name) with
                        nAnon => "_"
                      | nNamed s => s
                      end
                     +s " : "+s s1+s"). "+s s2)
  | tLetIn name t1 t2 t3 =>
    s1 <- bruijn_print_aux t1;;
    s2 <- bruijn_print_aux t2;;
    s3 <- bruijn_print_aux t3;;
    tmReturn("let "+s (nameToString name.(binder_name)) +s " := "+s s1 +s " : " +s s2 +s " in "+s linebreak +s s3)
  | tApp t1 t2 =>
    s1 <- bruijn_print_aux t1;;
    s2 <- monad_fold_left (fun s t => s2 <- bruijn_print_aux t;;tmReturn (s +s s2 +s ";")) t2 "";;
    tmReturn("((" +s s1 +s ") [" +s s2 +s "])")
  | tConst kn ui => let (_,name) := kn in tmReturn name
  | tInd ind ui => getInductiveName ind.(inductive_mind) ind.(inductive_ind)
  | tConstruct ind n ui => getConstructName ind.(inductive_mind) ind.(inductive_ind) n
  | tCase ci p c brs =>
    let ind := ci.(ci_ind) in
    let n := ci.(ci_npar) in
    let rel := ci.(ci_relevance) in
    sc <- bruijn_print_aux c;;
    sp <- bruijn_print_aux p.(preturn) ;;
    sb <- fold_left (fun sa x => match x with {| bcontext := n; bbody := t |} => st <- bruijn_print_aux t;;sb <- sa;;tmReturn (sb +s " | ("+s(natToString (List.length n))+s") " +s st +s linebreak) end) 
      brs (tmReturn "");;
    tmReturn(linebreak +s "match (P:" +s (natToString n) +s ") "+s sc +s " return " +s sp +s " with" +s linebreak +s
            sb +s
             "end")
  | tProj p t => tmReturn "TODO:Proj"
  | tFix mf n =>
    (fix f xs := match xs with
                  nil => tmReturn ""
                | mfb::xs =>
                  sr <- f xs;;
          stype <- bruijn_print_aux (mfb.(dtype));;
          sbody <- bruijn_print_aux (mfb.(dbody));;
          tmReturn (linebreak +s "(fix "+s (nameToString mfb.(dname).(binder_name)) +s " : " +s stype +s " := " +s linebreak +s sbody +s ") "+s sr)
                end
    ) mf
  | _ => tmReturn "TODO"
  end.

(** evalute and print, it is important to use lazy evaluation **)
Definition bruijn_print (t:term) : TemplateMonad unit :=
  s <- bruijn_print_aux t;;
  val <- tmEval lazy s;;
  tmMsg val.

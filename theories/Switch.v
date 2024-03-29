Require Import Coq.Lists.List.
Require Import MetaCoq.Template.All.

Import ListNotations.
Import MCMonadNotation.

Open Scope bs_scope.

Definition rname (s:string) := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Fixpoint mkSwitchCases
         (type_name: kername)
         (A_t: term)
         (P_t: term)
         (choices_t: list term)
         (n: nat) : term :=
  let ind_0 n := {| inductive_mind := n; inductive_ind := 0 |} in
  let T_i := ind_0 type_name in

  let bool_i := ind_0 (MPfile ["Datatypes"; "Init" ; "Coq"], "bool") in
  let opt_i := ind_0 (MPfile ["Datatypes"; "Init"; "Coq"], "option") in
  match choices_t with
  | [] => tApp (tConstruct opt_i 1 []) [tInd T_i []]
  | (x::xs) => tCase
               (* # of parameters *)
               (mk_case_info bool_i 0 Relevant)

               (* type info *)
               (mk_predicate [] [] [mkBindAnn nAnon Relevant] (tApp (tInd opt_i []) [tInd T_i []]))

               (* discriminee *)
               (tApp P_t [tRel 0; x])

               (* branches *)
               [
                 mk_branch [] (tApp (tConstruct opt_i 0 []) [tInd T_i []; tConstruct T_i n []]);
                 mk_branch [] (mkSwitchCases type_name A_t P_t xs (S n))
               ]
  end.

Definition mkSwitch
           (A: Type)
           (P: A -> A -> bool)
           (choices: list (A*String.string))
           (type_name: String.string)
           (def_name: String.string): TemplateMonad unit
  :=
  let choices' := map (fun '(a, s) => (a, String.of_string s)) choices in
  let type_name' := String.of_string type_name in
  let def_name' := String.of_string def_name in
    let one_i : one_inductive_entry :=
        {|
          mind_entry_typename := type_name' ;
          mind_entry_arity := tSort Universe.type0 ;
          mind_entry_consnames := map snd choices' ;
          mind_entry_lc := map (fun _ => tRel 0) choices';
        |} in
    let ind:mutual_inductive_entry := {|
          mind_entry_record    := None ;
          mind_entry_finite    := Finite ;
          mind_entry_params    := [] ;
          mind_entry_inds      := [one_i] ;
          mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
          mind_entry_template := false ;
          mind_entry_variance := None ;
          mind_entry_private   := None (* or (Some false)? *)
        |} in
    mp <- tmCurrentModPath tt ;;
    ind_t <- tmMkInductive false ind ;;
    T <- tmUnquoteTyped Type (tInd {| inductive_mind := (mp, type_name'); inductive_ind := 0 |} []) ;;
    A_t <- tmQuote A ;;
    P_t <- tmQuote P ;;
    choices_t <- monad_map (fun x => tmQuote (fst x)) choices' ;;
    let body_t := tLambda (rname "x") A_t (mkSwitchCases (mp, type_name') A_t P_t choices_t 0) in
    body <- tmUnquoteTyped (A -> option T) body_t ;;
    def_t <- tmDefinition def_name' body ;;
    tmReturn tt.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import MetaCoq.Template.All.

Import MonadNotation.
Import ListNotations.

Open Scope string_scope.

Fixpoint mkSwitchCases
         (type_name: kername)
         (A_t: term)
         (P_t: term)
         (choices_t: list term)
         (n: nat) : term :=
  let ind_0 n := {| inductive_mind := n; inductive_ind := 0 |} in
  let T_i := ind_0 type_name in

  let bool_i := ind_0 (MPfile ["Datatypes"; "Init"; "Coq"], "bool") in
  let opt_i := ind_0 (MPfile ["Datatypes"; "Init"; "Coq"], "option") in
  match choices_t with
  | [] => tApp (tConstruct opt_i 1 []) [tInd T_i []]
  | (x::xs) => tCase
               (* # of parameters *)
               (bool_i, 0)

               (* type info *)
               (tLambda (nNamed "b") (tInd bool_i []) (tApp (tInd opt_i []) [tInd T_i []]))

               (* discriminee *)
               (tApp P_t [tRel 0; x])

               (* branches *)
               [
                 (0, tApp (tConstruct opt_i 0 []) [tInd T_i []; tConstruct T_i n []]) ;
               (0, mkSwitchCases type_name A_t P_t xs (S n))
               ]
  end.


Definition mkSwitch
           (A: Type)
           (P: A -> A -> bool)
           (choices: list (A*string))
           (type_name: string)
           (def_name: string): TemplateMonad unit
  :=
    let one_i : one_inductive_entry :=
        {|
          mind_entry_typename := type_name ;
          mind_entry_arity := tSort Universe.type0 ;
          mind_entry_consnames := map snd choices ;
          mind_entry_lc := map (fun _ => tRel 0) choices;
        |} in
    let ind:mutual_inductive_entry := {|
          mind_entry_record    := None ;
          mind_entry_finite    := Finite ;
          mind_entry_params    := [] ;
          mind_entry_inds      := [one_i] ;
          mind_entry_universes := Monomorphic_entry (LevelSet.empty, ConstraintSet.empty);
          mind_entry_template := false ;
          mind_entry_cumulative  := false ;
          mind_entry_private   := None (* or (Some false)? *)
        |} in
    mp <- tmCurrentModPath tt ;;
    ind_t <- tmMkInductive ind ;;
    T <- tmUnquoteTyped Type (tInd {| inductive_mind := (mp, type_name); inductive_ind := 0 |} []) ;;
    A_t <- tmQuote A ;;
    P_t <- tmQuote P ;;
    choices_t <- monad_map (fun x => tmQuote (fst x)) choices ;;
    let body_t := tLambda (nNamed "x") A_t (mkSwitchCases (mp, type_name) A_t P_t choices_t 0) in
    body <- tmUnquoteTyped (A -> option T) body_t ;;
    def_t <- tmDefinition def_name body ;;
    tmReturn tt.

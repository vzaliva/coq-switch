Require Import Switch.Switch.

Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Template.All.

Import ListNotations.

Section NatExample.

  Run TemplateProgram
      (mkSwitch nat
                beq_nat
                [(0,"Love") ; (10,"Ten") ; (20, "twenty")]
                "Ex1_Choices" "ex1_select"
      ).

  Print Ex1_Choices.
  Print ex1_select.


  Definition Ex1 (n:nat): nat :=
    match ex1_select n with
    | Some Love => 100
    | Some Ten => 110
    | Some Twenty => 120
    | None => 0
    end.

End NatExample.


Section StringExample.

  Definition string_beq a b :=
    if string_dec a b then true else false.

  Run TemplateProgram
      (mkSwitch string
                string_beq
                [("love","SLove") ; ("ten","STen") ; ("twenty","STwenty")]
                "Ex2_Choices" "ex2_select"
      ).

  Print Ex2_Choices.
  Print ex2_select.


  Definition Ex2 (s:string) : nat :=
    match ex2_select s with
    | Some SLove => 100
    | Some STen => 110
    | Some STwenty => 120
    | None => 0
    end.

End StringExample.

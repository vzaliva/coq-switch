Require Import Switch.Switch.

Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import MetaCoq.Template.All.

Import ListNotations.

Section NatExample.

  (* This example uses standard list notation for choices *)

MetaCoq Run
      (mkSwitch nat
                Nat.eqb
                [(0,"Love"%bs) ; (10,"Ten"%bs) ; (20, "twenty"%bs)]
                "Ex1_Choices"%bs "ex1_select"%bs
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

  Compute Ex1 10.

End NatExample.

Definition string_beq a b :=
  if string_dec a b then true else false.

Section StringExample.

  (* This example custom -> notation for choices *)
  Infix "->" := pair.

  MetaCoq Run
      (mkSwitch String.string string_beq [
                  "love"%string   -> "SLove"%bs ;
                  "ten"%string    -> "STen"%bs  ;
                  "twenty"%string -> "STwenty"%bs
                ] "Ex2_Choices"%bs "ex2_select"%bs
      ).

  Print Ex2_Choices.
  Print ex2_select.


  Definition Ex2 (s:String.string) : nat :=
    match ex2_select s with
    | Some SLove => 100
    | Some STen => 110
    | Some STwenty => 120
    | None => 0
    end.

  Compute Ex2 "ten".
  Compute Ex2 "xxx".

End StringExample.

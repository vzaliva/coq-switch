# coq-switch #

`coq-switch` plugin for Coq

## Introduction ##

Sometimes you need to dispatch on several constant values which have a
decidable type. Unfortunately Coq, does not have `swtich` statement,
so common approach is to map these matches to an inductive type on
which `match` could be performed later. This leads to code like this
(taken from real-life projects):

```
Definition BER_bits2radix (b : Z) : radix :=
  if (b =? 0)%Z
  then radix2
  else if (b =? 1)%Z
       then radix4
       else if (b =? 2)%Z
            then radix8
            else if (b =? 4)%Z
                 then radix16
                 else radix2.
```

or like this:

```
Definition parse_SHCOL_Op_Name (s:string): SHCOL_Op_Names :=
  if string_dec s "eUnion" then n_eUnion
  else if string_dec s "eT" then n_eT
    else if string_dec s "SHPointwise" then n_SHPointwise
       else if string_dec s "SHBinOp" then n_SHBinOp
          else if string_dec s "SHInductor" then n_SHInductor
            else if string_dec s "IUnion" then n_IUnion
              else if string_dec s "ISumUnion" then n_ISumUnion
                else if string_dec s "IReduction" then n_IReduction
                  else if string_dec s "SHCompose" then n_SHCompose
                    else if string_dec s "SafeCast" then n_SafeCast
                      else if string_dec s "UnSafeCast" then n_UnSafeCast
                        else if string_dec s "HTSUMUnion" then n_HTSUMUnion
                          else n_Unsupported s.
```

Writing manually such biolerplate code is tiresome and
error-prone. This plugin allows to automate such tasks.


## Installation ##

* [Coq 8.8.1](https://coq.inria.fr/) 
* [Template Coq](https://template-coq.github.io/template-coq/)

To install all required dependenceis:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install --jobs=4 coq coq-template-coq
    
    
## Usage ##

This plugin is written using TemplateCoq. After importing you run
template program `mkSwitch` providing the following parameters:

    * type (`A`)
    * boolean equality predicate on this type (`P: A->A->bool`)
    * list of choices `(A * string)` where each element is a tuple of
      a constant of type `A` and name of a constructor (as a string).
    * name of a new inductive type
    * name of selection function
      
For example, running:

```
 Run TemplateProgram
     (mkSwitch nat
               beq_nat
               [(0,"Love") ; (10,"Ten") ; (20, "twenty")]
               "Ex1_Choices" "ex1_select"
     ).
```

Will define a new type and a function:

```
Print Ex1_Choices.

  Inductive Ex1_Choices : Set :=
    | Love   : Ex1_Choices 
    | Ten    : Ex1_Choices 
    | twenty : Ex1_Choices

Print ex1_select.

  ex1_select = 
  fun x : nat =>
  if Nat.eqb x (fst (0, "Love"))
  then Some Love
  else
   if Nat.eqb x (fst (10, "Ten"))
   then Some Ten
    else if Nat.eqb x (fst (20, "twenty")) then Some twenty else None
      : nat -> option Ex1_Choices
```

Now, using these could be used for easy matching:

```
Definition Ex1 (n:nat) : T :=
  match ex1_select n with
  | Some Love => ...
  | Some Ten => ...
  | Some Twenty => ...
  | None => ...
  end.
```

# Contact #

    * Repository: https://github.com/vzaliva/coq-switch
    * Questions: [Vadim Zaliva](mailto:vzaliva@cmu.edu)

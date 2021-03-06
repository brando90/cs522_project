(* *)

Check Some.
(*
Some
     : ?A -> option ?A
where
?A : [ |- Type]
*)

Print Some.
(*
Inductive option (A : Type) : Type :=  Some : A -> option A | None : option A

For Some: Arguments are renamed to A, a
For Some: Argument A is implicit and maximally inserted
For None: Argument A is implicit and maximally inserted
For option: Argument scope is [type_scope]
For Some: Argument scopes are [type_scope _]
For None: Argument scope is [type_scope]
*)

(* Q: how do you pass something of type 2
Compute option 2. 
*)

Inductive my_nat : Type :=
  | O_ : my_nat
  | S_ : my_nat -> my_nat.

Check O.
Check my_nat.
Check option my_nat.

Compute Some my_nat.

Definition myPred (n:nat) : option nat := match n with
  | S p => Some p
  | O => None
end.

Compute myPred 3.
Compute myPred 0.
Compute None.

Compute Some 3.
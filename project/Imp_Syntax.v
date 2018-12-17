Require Import Coq.Strings.String.

Inductive AExp : Type :=
  | ANum : nat -> AExp
  | APlus : AExp -> AExp -> AExp
  | ADiv : AExp -> AExp -> AExp
  | AId : string -> AExp.

Inductive BExp : Type :=
  | BVal : bool -> BExp
  | BLe : AExp -> AExp -> BExp
  | BNot : BExp -> BExp
  | BAnd : BExp -> BExp -> BExp.

Compute BVal true.
Example test_BVal: (BVal true) = BVal true.
Proof. simpl. reflexivity. Qed.

Inductive Block : Type :=
  | EmptyBlk : Block
  | Blk : Statement -> Block
with Statement : Type :=
  | Assignment : string -> AExp -> Statement
  | Seq : Statement -> Statement -> Statement
  | IfElse : BExp -> Block -> Block -> Statement
  | While : BExp -> Block -> Statement.

Inductive Program : Type :=
  | Pgm : list string -> Statement -> Program.

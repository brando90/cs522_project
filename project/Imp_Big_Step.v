Require Import Imp_Syntax.
Require Import Coq.Strings.String.

Definition State := string -> (option nat).

Inductive BigConfig : Type := 
  | B_AExpConf : AExp -> State -> BigConfig
  | B_NatConf : nat -> BigConfig
  | B_BExpConf : BExp -> State -> BigConfig
  | B_BoolConf : bool -> BigConfig
  | B_StmtConf : Statement -> State -> BigConfig
  | B_BlkConf : Block -> State -> BigConfig
  | B_StateConf : State -> BigConfig
  | B_PgmConf : Program -> BigConfig.


Inductive BigStepR : BigConfig -> BigConfig -> Prop :=
  | Block : forall (S : Statement) (Sigma Sigma' : State),
      BigStepR (B_StmtConf S Sigma) (B_StateConf Sigma') ->
      BigStepR (B_BlkConf (Blk S) Sigma) (B_StateConf Sigma').

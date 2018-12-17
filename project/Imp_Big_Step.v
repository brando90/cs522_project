Add LoadPath "/Users/brandomiranda/home_simulation_research/cs522_project/project".
Require Import Imp_Syntax.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

Definition State := string -> (option nat).

Inductive BigConfig : Type := 
  | B_AExpConf : AExp -> State -> BigConfig
  | B_BExpConf : BExp -> State -> BigConfig
  | B_StmtConf : Statement -> State -> BigConfig
  | B_BlkConf : Block -> State -> BigConfig
  | B_StateConf : State -> BigConfig
  | B_PgmConf : Program -> BigConfig.

Inductive BigStepR : BigConfig -> BigConfig -> Prop :=
  | Block : forall (S : Statement) (Sigma Sigma' : State),
      BigStepR (B_StmtConf S Sigma) (B_StateConf Sigma') ->
      BigStepR (B_BlkConf (Blk S) Sigma) (B_StateConf Sigma')
(*  crl < A1 + A2 , Sigma > => < I1 +Int I2 > if < A1,Sigma > => < I1 > /\ < A2,Sigma > => < I2 > . *)
  | BigStep_Add : forall (A1 A2 I1 I2 : AExp ) (Sigma : State ),
    (BigStepR (B_AExpConf A1 Sigma) (B_AExpConf I1 Sigma) ) ->
    (BigStepR (B_AExpConf A2 Sigma) (B_AExpConf I2 Sigma) ) ->
    (BigStepR (B_AExpConf (APlus A1 A2) Sigma) (B_AExpConf (APlus I1 I2) Sigma)).

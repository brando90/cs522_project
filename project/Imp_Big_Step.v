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
  (* TODO: do we need this? rl < I,Sigma > => < I > . *)
  (* TODO: do we need this? crl < X,Sigma > => < Sigma(X) > if Sigma(X) =/=Bool undefined . *)
  (*  crl < A1 + A2 , Sigma > => < I1 +Int I2 > if < A1,Sigma > => < I1 > /\ < A2,Sigma > => < I2 > . TODO: how do we deal with the division by zero? *)
  | BigStep_Add : forall (A1 A2 I1 I2 : AExp ) (Sigma : State ),
    (BigStepR (B_AExpConf A1 Sigma) (B_AExpConf I1 Sigma) ) ->
    (BigStepR (B_AExpConf A2 Sigma) (B_AExpConf I2 Sigma) ) ->
    (BigStepR (B_AExpConf (APlus A1 A2) Sigma) (B_AExpConf (APlus I1 I2) Sigma))
  (* crl < A1 / A2,Sigma > => < I1 /Int I2 > if < A1,Sigma > => < I1 > /\ < A2,Sigma > => < I2 > /\ I2 =/=Bool 0 . *)
  | BigStep_Divide: forall (A1 A2 I1 I2 : AExp ) (Sigma : State ),
    (BigStepR (B_AExpConf A1 Sigma) (B_AExpConf I1 Sigma) ) ->
    (BigStepR (B_AExpConf A2 Sigma) (B_AExpConf I2 Sigma) ) ->
    (* TODO (not (I2 = 0) ) -> *)
    (BigStepR (B_AExpConf (APlus A1 A2) Sigma) (B_AExpConf (ADiv I1 I2) Sigma))
  (* TODO: do we need this? rl < T,Sigma > => < T > . *)
  (* crl < A1 <= A2,Sigma > => < I1 <=Int I2 > if < A1,Sigma > => < I1 > /\ < A2,Sigma > => < I2 > .*)
  | BigStep_Leq : forall (A1 A2 I1 I2 : AExp) (Sigma : State),
     (BigStepR (B_AExpConf A1 Sigma) (B_AExpConf I1 Sigma) ) ->
     (BigStepR (B_AExpConf A2 Sigma) (B_AExpConf I2 Sigma) ) ->
     (BigStepR (B_BExpConf (BLe A1 A2) Sigma) (B_BExpConf (BLe I1 I2) Sigma) )
  (*  crl < ! B,Sigma > => < false > if < B,Sigma > => < true > . *)
  | BigStep_Not : forall (A B : BExp) (Sigma : State),
     (BigStepR (B_BExpConf A Sigma) (B_BExpConf B Sigma) ) ->
     (BigStepR (B_BExpConf (BNot A) Sigma) (B_BExpConf (BNot B) Sigma) ).  

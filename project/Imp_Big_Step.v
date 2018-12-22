Add LoadPath "C:\\Users\\ument\\School\\cs522\\cs522_project\\project".
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
Definition t_update (m : State) (x : string) (v : nat) :=
  fun x' => if string_dec x x' then Some v else m x'.

Inductive BigConfig : Type :=
  | B_AExpConf : AExp -> State -> BigConfig
  | B_BExpConf : BExp -> State -> BigConfig
  | B_StmtConf : Statement -> State -> BigConfig
  | B_BlkConf : Block -> State -> BigConfig
  | B_StateConf : State -> BigConfig
  | B_PgmConf : Program -> BigConfig.

Inductive BigStepR : BigConfig -> BigConfig -> Prop :=
  (* TODO: do we need this? rl < I,Sigma > => < I > . *)
  (* TODO: do we need this? crl < X,Sigma > => < Sigma(X) > if Sigma(X) =/=Bool undefined . *)
  | IdVal : forall (id : string) (X : nat) (Sigma : State),
      ((Sigma id) = (Some X)) ->
      BigStepR (B_AExpConf (AId id) Sigma) (B_AExpConf (ANum X) Sigma)
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
      (BigStepR (B_BExpConf (BNot A) Sigma) (B_BExpConf (BNot B) Sigma) )
  (* crl < B1 && B2,Sigma > => < false > if < B1,Sigma > => < false > . *)
  | BigStep_And_F : forall (B1 B2 : BExp ) (Sigma : State),
      (BigStepR (B_BExpConf B1 Sigma) (B_BExpConf (BVal false) Sigma) ) ->
      (BigStepR (B_BExpConf (BAnd B1 B2) Sigma) (B_BExpConf (BVal false) Sigma) )
  (* crl < B1 && B2,Sigma > => < T > if < B1,Sigma > => < true > /\ < B2,Sigma > => < T > . *)
  | BigStep_And_T : forall (B1 B2 : BExp ) (Sigma : State),
      (BigStepR (B_BExpConf B1 Sigma) (B_BExpConf (BVal true) Sigma) ) ->
      (BigStepR (B_BExpConf B2 Sigma) (B_BExpConf (BVal true) Sigma) ) ->
      (BigStepR (B_BExpConf (BAnd B1 B2) Sigma) (B_BExpConf (BVal true) Sigma) )
  (* TODO: rl < {},Sigma > => < Sigma > . *)
  (*  crl < {S},Sigma > => < Sigma' > if < S,Sigma > => < Sigma' > .  *)
  | BigStep_Block : forall (S : Statement) (Sigma Sigma' : State),
      BigStepR (B_StmtConf S Sigma) (B_StateConf Sigma') ->
      BigStepR (B_BlkConf (Blk S) Sigma) (B_StateConf Sigma')
  (*  crl < X = A ;,Sigma > => < Sigma[I / X] > if < A,Sigma > => < I > /\ Sigma(X) =/=Bool undefined . *)
  | BigStep_Assign : forall (X : nat) (A : AExp) (id : string) (Sigma Sigma': State),
      (BigStepR (B_AExpConf A Sigma) (B_AExpConf (ANum X) Sigma)) ->
      ((t_update Sigma id X) = Sigma') ->
      BigStepR (B_StmtConf (Assignment id A) Sigma) (B_StateConf Sigma')
  (*  crl < S1 S2,Sigma > => < Sigma2 > if < S1,Sigma > => < Sigma1 > /\ < S2,Sigma1 > => < Sigma2 > . *)
  | BigStep_Seq: forall (S1 S2 : Statement) (Sigma Sigma1 Sigma2 : State),
      BigStepR (B_StmtConf S1 Sigma) (B_StateConf Sigma1) ->
      BigStepR (B_StmtConf S2 Sigma1) (B_StateConf Sigma2) ->
      BigStepR (B_StmtConf (Seq S1 S2) Sigma) (B_StateConf Sigma2)
  (* crl < if (B) S1 else S2,Sigma > => < Sigma1 > if < B,Sigma > => < true > /\ < S1,Sigma > => < Sigma1 > . *)
  | BigStep_If_True: forall (B : BExp) (B1 B2 : Block) (Sigma Sigma1 : State),
      BigStepR (B_BExpConf B Sigma) (B_BExpConf (BVal true) Sigma) ->
      BigStepR (B_BlkConf B1 Sigma) (B_StateConf Sigma1) ->
      BigStepR (B_StmtConf (IfElse B B1 B2) Sigma) (B_StateConf Sigma1)
  (* crl < if (B) S1 else S2,Sigma > => < Sigma2 > if < B,Sigma > => < false > /\ < S2,Sigma > => < Sigma2 > . *)
  | BigStep_If_False: forall (B : BExp) (B1 B2 : Block) (S1 S2 : Statement) (Sigma Sigma2 : State),
    BigStepR (B_BExpConf B Sigma) (B_BExpConf (BVal false) Sigma) ->
    BigStepR (B_BlkConf B2 Sigma) (B_StateConf Sigma2) ->
    BigStepR (B_StmtConf (IfElse B B1 B2) Sigma) (B_StateConf Sigma2)
  (* crl < while (B) S,Sigma > => < Sigma > if < B,Sigma > => < false > . *)
  | BigStep_While_False: forall (Bl : BExp) (Bck : Block) (S1 S2 : Statement) (Sigma : State),
    BigStepR (B_BExpConf Bl Sigma) (B_BExpConf (BVal false) Sigma) ->
    BigStepR (B_StmtConf (While Bl Bck) Sigma) (B_StateConf Sigma)
  (* crl < while (B) S,Sigma > => < Sigma' > if < B,Sigma > => < true > /\ < S while (B) S,Sigma > => < Sigma' > . *)
  | BigStep_While_True: forall (Bl : BExp) (Bck : Block) (S1 S2 : Statement) (Sigma Sigma' : State),
    BigStepR (B_BExpConf Bl Sigma) (B_BExpConf (BVal true) Sigma) ->
    BigStepR (B_StmtConf (While Bl Bck) Sigma) (B_StateConf Sigma') ->
    BigStepR (B_StmtConf (While Bl Bck) Sigma) (B_StateConf Sigma')
  (* TODO: crl < int Xl ; S > => < Sigma > if < S,(Xl |-> 0) > => < Sigma > . *)
  | BigStep_Pgm : forall (S : Statement) (Ids : list string) (Sigma : State),
    BigStepR (B_StmtConf S (fun x =>
      if (bool_in x Ids) then Some 0 else None
    )) (B_StateConf Sigma) ->
    BigStepR (B_PgmConf (Pgm Ids S)) (B_StateConf Sigma)
.

Theorem BigStep_AEval : forall (Sigma : State) (A : AExp) (n : nat),
  (((aeval Sigma A) = Some n) <-> (BigStepR (B_AExpConf A Sigma) (B_AExpConf (ANum n) Sigma))).
  Proof.
  Admitted.

Theorem BigStep_BEval : forall (Sigma : State) (B : BExp) (b : bool),
  (((beval Sigma B) = Some b) <-> (BigStepR (B_BExpConf B Sigma) (B_BExpConf (BVal b) Sigma))).
  Proof.
  Admitted.

(*
Theorem AEvalR : forall (Sigma : State) (A : AExp) (n : nat),
  (((aeval Sigma A) = Some n) <-> (ConfigEquivR (B_AExpConf A Sigma) (B_AExpConf (ANum n) Sigma))).
  Proof.
  Admitted.*)

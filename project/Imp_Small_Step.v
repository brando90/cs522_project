Require Import Imp_Syntax.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Import ListNotations.

Definition State := string -> (option nat).
Definition t_update (m : State) (x : string) (v : nat) :=
  fun x' => if string_dec x x' then Some v else m x'.

Inductive SmallConfig : Type := 
  | S_AExpConf : AExp -> State -> SmallConfig
  | S_BExpConf : BExp -> State -> SmallConfig
  | S_StmtConf : Statement -> State -> SmallConfig
  | S_BlkConf : Block -> State -> SmallConfig
  | S_PgmConf : Program -> SmallConfig.


Inductive SmallStepR : SmallConfig -> SmallConfig -> Prop :=
  | Block : forall (S : Statement) (Sigma : State),
      SmallStepR (S_BlkConf (Blk S) Sigma) (S_StmtConf S Sigma)
  | PlusANums : forall (X Y Z : nat) (Sigma : State),
      ((X + Y) = Z) ->
      SmallStepR (S_AExpConf (APlus (ANum X) (ANum Y)) Sigma) (S_AExpConf (ANum Z) Sigma)
  | DivANums : forall (X Y Z : nat) (Sigma : State),
      ((mult Y Z) = X) ->
      SmallStepR (S_AExpConf (ADiv (ANum X) (ANum Y)) Sigma) (S_AExpConf (ANum Z) Sigma)
  | LEqANums : forall (X Y : nat) (Z : bool) (Sigma : State),
      ((leb X Y) = Z) ->
      SmallStepR (S_BExpConf (BLe (ANum X) (ANum Y)) Sigma) (S_BExpConf (BVal Z) Sigma)
  | IdVal : forall (id : string) (X : nat) (Sigma : State),
      ((Sigma id) = (Some X)) ->
      SmallStepR (S_AExpConf (AId id) Sigma) (S_AExpConf (ANum X) Sigma)
  | PlusLeft : forall (A B C : AExp) (Sigma : State),
      (SmallStepR (S_AExpConf A Sigma) (S_AExpConf C Sigma)) ->
      SmallStepR (S_AExpConf (APlus A B) Sigma) (S_AExpConf (APlus C B) Sigma)
  | PlusRight : forall (A B C : AExp) (Sigma : State),
      (SmallStepR (S_AExpConf B Sigma) (S_AExpConf C Sigma)) ->
      SmallStepR (S_AExpConf (APlus A B) Sigma) (S_AExpConf (APlus A C) Sigma)
  | DivLeft : forall (A B C : AExp) (Sigma : State),
      (SmallStepR (S_AExpConf A Sigma) (S_AExpConf C Sigma)) ->
      SmallStepR (S_AExpConf (ADiv A B) Sigma) (S_AExpConf (ADiv C B) Sigma)
  | DivRight : forall (A B C : AExp) (Sigma : State),
      (SmallStepR (S_AExpConf B Sigma) (S_AExpConf C Sigma)) ->
      SmallStepR (S_AExpConf (ADiv A B) Sigma) (S_AExpConf (ADiv A C) Sigma)
  | LEqLeft : forall (A B C : AExp) (Sigma : State),
      (SmallStepR (S_AExpConf A Sigma) (S_AExpConf C Sigma)) ->
      SmallStepR (S_BExpConf (BLe A B) Sigma) (S_BExpConf (BLe C B) Sigma)
  | LEqRight : forall (A B C : AExp) (Sigma : State),
      (SmallStepR (S_AExpConf B Sigma) (S_AExpConf C Sigma)) ->
      SmallStepR (S_BExpConf (BLe A B) Sigma) (S_BExpConf (BLe A C) Sigma)
  | NotStep : forall (A B : BExp) (Sigma : State),
      (SmallStepR (S_BExpConf A Sigma) (S_BExpConf B Sigma)) ->
      SmallStepR (S_BExpConf (BNot A) Sigma) (S_BExpConf (BNot B) Sigma)
  | NotTrue : forall (Sigma : State),
      SmallStepR (S_BExpConf (BNot (BVal true)) Sigma) (S_BExpConf (BVal false) Sigma)
  | NotFalse : forall (Sigma : State),
      SmallStepR (S_BExpConf (BNot (BVal false)) Sigma) (S_BExpConf (BVal true) Sigma)
  | AndLeft : forall (A B C : BExp) (Sigma : State),
      (SmallStepR (S_BExpConf A Sigma) (S_BExpConf C Sigma)) ->
      SmallStepR (S_BExpConf (BAnd A B) Sigma) (S_BExpConf (BAnd C B) Sigma)
  | AndFalse : forall (A : BExp) (Sigma : State),
      SmallStepR (S_BExpConf (BAnd (BVal false) A) Sigma) (S_BExpConf (BVal false) Sigma)
  | AndTrue : forall (A : BExp) (Sigma : State),
      SmallStepR (S_BExpConf (BAnd (BVal true) A) Sigma) (S_BExpConf A Sigma)
  | AsgnStep : forall (A B : AExp) (id : string) (Sigma : State),
      (SmallStepR (S_AExpConf A Sigma) (S_AExpConf B Sigma)) ->
      SmallStepR (S_StmtConf (Assignment id A) Sigma) (S_StmtConf (Assignment id B) Sigma)
  | Assign : forall (X : nat) (id : string) (Sigma Sigma': State),
      ((t_update Sigma id X) = Sigma') ->
      SmallStepR (S_StmtConf (Assignment id (ANum X)) Sigma) (S_BlkConf EmptyBlk Sigma')
.

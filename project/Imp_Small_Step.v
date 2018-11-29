Require Import Imp_Syntax.
Require Import Coq.Strings.String.

Definition State := string -> (option nat).

Inductive SmallConfig : Type := 
  | S_AExpConf : AExp -> State -> SmallConfig
  | S_BExpConf : BExp -> State -> SmallConfig
  | S_StmtConf : Statement -> State -> SmallConfig
  | S_BlkConf : Block -> State -> SmallConfig
  | S_PgmConf : Program -> SmallConfig.


Inductive SmallStepR : SmallConfig -> SmallConfig -> Prop :=
  | Block : forall (S : Statement) (Sigma : State),
      SmallStepR (S_BlkConf (Blk S) Sigma) (S_StmtConf S Sigma).

Require Import Imp_Syntax.
Require Import Coq.Strings.String.

Definition State := string -> (option nat).

Inductive SmallConfig : Type := 
  | AExpConf : AExp -> State -> SmallConfig
  | BExpConf : BExp -> State -> SmallConfig
  | StmtConf : Statement -> State -> SmallConfig
  | BlkConf : Block -> State -> SmallConfig
  | PgmConf : Program -> SmallConfig.


Inductive SmallStepR : SmallConfig -> SmallConfig -> Prop :=
  | Block : forall (S : Statement) (Sigma : State),
      SmallStepR (BlkConf (Blk S) Sigma) (StmtConf S Sigma).

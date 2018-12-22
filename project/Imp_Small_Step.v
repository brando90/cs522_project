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
  | IfStep : forall (X Y : BExp) (B1 B2 : Block) (Sigma : State),
      (SmallStepR (S_BExpConf X Sigma) (S_BExpConf Y Sigma)) ->
      SmallStepR (S_StmtConf (IfElse X B1 B2) Sigma) (S_StmtConf (IfElse Y B1 B2) Sigma)
  | IfTrue : forall (B1 B2 : Block) (Sigma : State),
      SmallStepR (S_StmtConf (IfElse (BVal true) B1 B2) Sigma) (S_BlkConf B1 Sigma)
  | IfFalse : forall (B1 B2 : Block) (Sigma : State),
      SmallStepR (S_StmtConf (IfElse (BVal false) B1 B2) Sigma) (S_BlkConf B2 Sigma)
  | SeqStep : forall (S1 S2 S3 : Statement) (Sigma1 Sigma2 : State),
      SmallStepR (S_StmtConf S1 Sigma1) (S_StmtConf S2 Sigma2) ->
      SmallStepR (S_StmtConf (Seq S1 S3) Sigma1) (S_StmtConf (Seq S2 S3) Sigma2)
  | SeqDone : forall (S1 S2 : Statement) (Sigma1 Sigma2 : State),
      SmallStepR (S_StmtConf S1 Sigma1) (S_BlkConf EmptyBlk Sigma2) ->
      (* TODO this is a little messy, not strictly small step but seems it must be
      done this way due to not having blocks be subsorts of statements. would be
      possible to fix this but would require many changes elsewhere *)
      SmallStepR (S_StmtConf (Seq S1 S2) Sigma1) (S_StmtConf S2 Sigma2)
  | While : forall (X : BExp) (B : Block) (Sigma : State),
      SmallStepR (S_StmtConf (While X B) Sigma) (S_StmtConf (IfElse X (Blk (While X B)) EmptyBlk) Sigma)
  | Program_intro : forall (S : Statement) (Ids : list string) (Sigma : State),
    SmallStepR (S_PgmConf (Pgm Ids S)) (S_StmtConf S (fun x =>
      if (bool_in x Ids) then Some 0 else None)
    )
.

Inductive NSmallSteps : nat -> SmallConfig -> SmallConfig -> Prop :=
  | Zero : forall (C : SmallConfig), NSmallSteps 0 C C
  | Succ : forall (C1 C2 C3 : SmallConfig) (N M : nat),
      (NSmallSteps N C2 C3) -> (SmallStepR C1 C2) -> (M = (S N))-> (NSmallSteps M C1 C3)
  | Skip : forall (C1 C2 : SmallConfig) (N : nat), NSmallSteps N C1 C2 -> NSmallSteps (S N) C1 C2
.

(* these lemmas all seem fairly intuitive but are hard to prove so we use them
   without proof *)

Definition ConfigEquivR (C1 C2 : SmallConfig) :=
  exists N : nat, NSmallSteps N C1 C2.

Theorem asgn_success_iff : forall (s : string) (a : AExp) (S1 S2 : State),
  (ConfigEquivR (S_StmtConf (Assignment s a) S1) (S_BlkConf EmptyBlk S2)) <->
  (exists y : nat, ConfigEquivR (S_StmtConf (Assignment s a) S1) (S_StmtConf (Assignment s (ANum y)) S1)).
  Admitted.

Theorem asgn_aexp_steps : forall (y : nat) (s : string) (a : AExp) (S1 : State),
  ConfigEquivR (S_StmtConf (Assignment s a) S1) (S_StmtConf (Assignment s (ANum y)) S1) <->
  ConfigEquivR (S_AExpConf a S1) (S_AExpConf (ANum y) S1).
  Admitted.

Theorem seq_success_first : forall (S1 S2 : Statement) (Sigma1 Sigma2 : State),
  (ConfigEquivR (S_StmtConf (Seq S1 S2) Sigma1) (S_StmtConf S2 Sigma2)) <->
  (ConfigEquivR (S_StmtConf S1 Sigma1) (S_BlkConf EmptyBlk Sigma2)).
  Admitted.

Theorem seq_success_total : forall (S1 S2 : Statement) (Sigma1 Sigma2 : State),
  (exists Sigma3 : State,
    ((ConfigEquivR (S_StmtConf S1 Sigma1) (S_BlkConf EmptyBlk Sigma3)) /\
    (ConfigEquivR (S_StmtConf S2 Sigma3) (S_BlkConf EmptyBlk Sigma2)))) <->
  (ConfigEquivR (S_StmtConf (Seq S1 S2) Sigma1) (S_BlkConf EmptyBlk Sigma2)).
  Admitted.

Theorem AEvalR : forall (Sigma : State) (A : AExp) (n : nat),
  (((aeval Sigma A) = Some n) <-> (ConfigEquivR (S_AExpConf A Sigma) (S_AExpConf (ANum n) Sigma))).
  Proof.
  Admitted.

Theorem BEvalR : forall (Sigma : State) (B : BExp) (b : bool),
  (((beval Sigma B) = Some b) <-> (SmallStepR (S_BExpConf B Sigma) (S_BExpConf (BVal b) Sigma))).
  Proof.
  Admitted.

Theorem Confluence : forall (A B C : SmallConfig),
  (SmallStepR A B) -> (SmallStepR A C) -> exists D : SmallConfig, ((SmallStepR B D) /\ (SmallStepR C D)).
Proof.
Admitted.

Theorem ConfluenceVariant : forall (C1 C2 C3 : SmallConfig), ConfigEquivR C1 C3 -> ConfigEquivR C1 C2 -> ConfigEquivR C2 C3.
Proof.
Admitted.

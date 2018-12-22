Add LoadPath "C:\\Users\\ument\\School\\cs522\\cs522_project\\project".
Add LoadPath "/Users/brandomiranda/home_simulation_research/cs522_project/project".
Require Import Imp_Syntax.
Require Import Imp_Big_Step.
Require Import Imp_Small_Step.
Require Import Coq.Strings.String.

Definition State := string -> (option nat).
Definition ConfigEquivR (C1 C2 : SmallConfig) :=
  exists N : nat, NSmallSteps N C1 C2.

Theorem Big_Small_Equiv_Stmt : forall (S' : Statement) (S1 S2 : State),
  (BigStepR (B_StmtConf S' S1) (B_StateConf S2)) <-> (ConfigEquivR (S_StmtConf S' S1) (S_BlkConf EmptyBlk S2)).
  split.
  (* big step -> small step *)
  admit.


  (* small step -> big step *)
  generalize dependent S1.
  generalize dependent S2.
  induction S' ; intros.

  (* Assign *)
  cut (exists y : nat, (aeval S1 a) = Some y).
  intros.
  destruct H0.
  apply BigStep_Assign with (X := x).
  apply BigStep_AEval.
  exact H0.

  admit. (* not sure how to tackle this one *)
  apply asgn_success_iff in H.
  destruct H.
  refine (ex_intro _ x _ ).
  rewrite AEvalR.
  rewrite <- asgn_aexp_steps.
  exact H.


  (* sequence *)
  cut (exists Sigma1 : State, ConfigEquivR (S_StmtConf S'1 S1) (S_BlkConf EmptyBlk Sigma1)).
  intros.
  unfold ConfigEquivR.
  unfold Imp_Small_Step.ConfigEquivR in H0.
  destruct H0.
  apply BigStep_Seq with (Sigma1 := x).
  refine (IHS'1 x S1 H0).
  refine (IHS'2 S2 x _).
  (*rewrite <- (seq_success_iff S'1 S'2 x S1).*)
  apply ConfluenceVariant with (C1 := (S_StmtConf (Seq S'1 S'2) S1)).
  exact H.
  rewrite seq_success_first.
  exact H0.
  apply seq_success_total in H.
  destruct H.
  refine (ex_intro _ x _ ).
  destruct H.
  exact H.

  (* if/else *)
  cut (exists y : bool, beval S1 b = Some y).
  intros.
  destruct H0.
  apply BigStep_BEval in H0.
  destruct x.
  apply BigStep_If_True.
  exact H0.
  admit.
  admit.
  admit.

  (* while *)
  admit.
Admitted.

Theorem Big_Small_Equiv : forall (P : Program) (S' : State),

(* big step -> small step *)
  (BigStepR (B_PgmConf P) (B_StateConf S')) <-> (ConfigEquivR (S_PgmConf P) (S_BlkConf EmptyBlk S')).
  intros.
  split.
  induction P.
  intros.
  unfold ConfigEquivR. refine (ex_intro _ _ _) .
  admit.

(* small step -> big step *)
  case P.
  intros.
  apply BigStep_Pgm.
  rewrite Big_Small_Equiv_Stmt.
  apply ConfluenceVariant with (C1 := (S_PgmConf (Pgm l s))).
  exact H.
  unfold ConfigEquivR.
  refine (ex_intro _ (S 0) _).
  apply Succ with (C2 := (S_StmtConf s (fun x : string => if bool_in x l then Some 0 else None))) (N := 0).
  apply Zero.
  apply Program_intro.
  auto.
  auto.
Admitted.

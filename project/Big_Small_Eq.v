Add LoadPath "C:\\Users\\ument\\School\\cs522\\cs522_project\\project".
Add LoadPath "/Users/brandomiranda/home_simulation_research/cs522_project/project".
Require Import Imp_Syntax.
Require Import Imp_Big_Step.
Require Import Imp_Small_Step.
Require Import Coq.Strings.String.

Definition State := string -> (option nat).
Definition ConfigEquivR (C1 C2 : SmallConfig) :=
  exists N : nat, NSmallSteps N C1 C2.
  

Theorem Big_Small_Equiv_Stmt : forall (S : Statement) (S1 S2 : State),
  (BigStepR (B_StmtConf S S1) (B_StateConf S2)) <-> (ConfigEquivR (S_StmtConf S S1) (S_BlkConf EmptyBlk S2)).
Admitted.

Theorem Big_Small_Equiv : forall (P : Program) (S' : State),
  (BigStepR (B_PgmConf P) (B_StateConf S')) <-> (ConfigEquivR (S_PgmConf P) (S_BlkConf EmptyBlk S')).
  intros.
  split.
  induction P.
  intros.
  unfold ConfigEquivR. refine (ex_intro _ _ _) .
  admit.

(* small step -> big step direction *)
  case P.
  intros.
  apply BigStep_Pgm.
  rewrite Big_Small_Equiv_Stmt.
  unfold ConfigEquivR.
  unfold ConfigEquivR in H.
  cut (exists N : nat, NSmallSteps (S N) (S_PgmConf (Pgm l s)) (S_BlkConf EmptyBlk S')).
  intros.
  destruct H0.
  refine (ex_intro _ x _).
  apply Succ with (C2 := (S_PgmConf (Pgm l s))) (N := x) .
  exact H0.
  rewrite <- Succ with (C1 := (S_StmtConf s (fun x : string => if bool_in x l then Some 0 else None))) (C2 := (S_PgmConf (Pgm l s))) (C3 := (S_BlkConf EmptyBlk S')).
  generalize dependent S.
  induction s ; intros.


(* assign *)
  cut (exists y : nat, (aeval (fun x : string => if bool_in x l then Some 0 else None) a) = Some y).
  intros.
  destruct H0.
  apply BigStep_Assign with (X := x).
  apply BigStep_AEval.
  exact H0. (* assignment, apply Assign defers proof of state and cut defers proof of value *)

  unfold ConfigEquivR in H.
  destruct H.
  apply AEvalR in H0.
  admit. (* proof of state *)
  admit. (* proof of value *)

(* sequence *)

  cut (exists Sigma1 : State, BigStepR (B_StmtConf s1 (fun x : string => if bool_in x l then Some 0 else None)) (B_StateConf Sigma1)).
  intros.
  destruct H0.
  apply BigStep_Seq with (Sigma1 := x).
  exact H0.

  admit.

(* if/else *)


  admit.

(* while *)

  admit.
(*  intros.
  cut (exists Sigma1 : State, BigStepR (B_PgmConf (Pgm l s1)) (B_StateConf Sigma1)).
  intros.
  destruct H0.
  apply BigStep_Seq with (Sigma1 := x).
  refine (IHs1 x _).
  unfold ConfigEquivR.
  refine (ex_intro _ _ _).
  admit.
  refine (TMP _).
  admit.
  unfold ConfigEquivR in H.
  destruct H.
  cut (BigStepR (B_PgmConf (Pgm l s2)) (B_StateConf S)).
  intros.
.*)
Admitted.
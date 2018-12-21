Add LoadPath "C:\\Users\\ument\\School\\cs522\\cs522_project\\project".
Add LoadPath "/Users/brandomiranda/home_simulation_research/cs522_project/project".
Require Import Imp_Syntax.
Require Import Imp_Big_Step.
Require Import Imp_Small_Step.
Require Import Coq.Strings.String.

Definition State := string -> (option nat).
Definition ConfigEquivR (C1 C2 : SmallConfig) :=
  exists N : nat, NSmallSteps N C1 C2.
  
Theorem Big_Small_Equiv : forall (P : Program) (S : State),
  (BigStepR (B_PgmConf P) (B_StateConf S)) <-> (ConfigEquivR (S_PgmConf P) (S_BlkConf EmptyBlk S)).
  intros.
  split.
  induction P.
  intros.
  unfold ConfigEquivR. refine (ex_intro _ _ _) . admit. (*
  refine (Succ _ _ _ _) .
  intros.
  generalize dependent s.
  induction s ; intros ; unfold ConfigEquivR . *)
  generalize dependent P.
  induction P .
  intros.
  apply BigStep_Pgm.
  unfold ConfigEquivR in H.
  induction s.
  refine (BigStep_Assign _ _ _ _).
Admitted.
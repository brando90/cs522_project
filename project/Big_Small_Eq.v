Add LoadPath "C:\\Users\\ument\\School\\cs522\\cs522_project\\project".
Require Import Imp_Syntax.
Require Import Imp_Big_Step.
Require Import Imp_Small_Step.
Require Import Coq.Strings.String.

Definition State := string -> (option nat).

Theorem Big_Small_Equiv : forall (P : Program) (S : State),
  (BigStepR (B_PgmConf P) (B_StateConf S)) <-> (SmallStepR (S_PgmConf P) (S_BlkConf EmptyBlk S)).
Admitted.
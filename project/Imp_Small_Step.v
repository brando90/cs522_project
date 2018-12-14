Add LoadPath "C:\\Users\\ument\\School\\cs522\\cs522_project\\project".
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
.

Inductive NSmallSteps : nat -> SmallConfig -> SmallConfig -> Prop :=
  | Zero : forall (C : SmallConfig), NSmallSteps 0 C C
  | Succ : forall (C1 C2 : SmallConfig), 
.

Inductive ConfigEquivR : SmallConfig -> SmallConfig -> Prop :=
  | Trans : forall (C1 C2 C3 : SmallConfig),
      ConfigEquivR C1 C2 -> ConfigEquivR C2 C3 -> ConfigEquivR C1 C3
  | Symmetry : forall (C1 C2 : SmallConfig),
      ConfigEquivR C1 C2 -> ConfigEquivR C2 C1
  | Reflex : forall (C : SmallConfig), ConfigEquivR C C
  | SmallStep : forall (C1 C2 : SmallConfig),
      SmallStepR C1 C2 -> ConfigEquivR C1 C2
.

Definition relation (X: Type) := X -> X -> Prop.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Theorem SmallStepEquiv : equivalence ConfigEquivR.
Proof.
  constructor ; constructor ; try(constructor).
  apply SmallStep.
  apply Reflex.
  exact H.
  constructor.
  generalize H0.
  generalize H.
  apply Trans.
Qed.

Theorem ImplEqual : forall (C1 C2 : SmallConfig),
  ConfigEquivR C1 C2 -> (C1 = C2).
Proof.
  intros.
  inversion H ; subst.
Qed.

Fixpoint aeval (st : State) (a : AExp) : option nat :=
  match a with
  | ANum n => Some n
  | AId x => st x
  | APlus a1 a2 => match (aeval st a1) with
    | Some n => match (aeval st a2) with
      | Some n0 => Some (n + n0)
      | None => None
      end
    | None => None
    end
  | ADiv a1 a2 => match (aeval st a2) with
    | Some 0 => None
    | Some (S n) => match (aeval st a1) with
      | Some n0 => Some (div n0 (S n))
      | None => None
      end
    | None => None
    end
  end.

Fixpoint beval (st : State) (b : BExp) : option bool :=
  match b with
  | BVal v => Some v
  | BLe a1 a2 => match (aeval st a1) with
    | Some v => match (aeval st a2) with
      | Some v0 => Some (leb v v0)
      | None => None
      end
    | None => None
    end
  | BNot b1 => match (beval st b1) with
    | Some v => Some (negb v)
    | None => None
    end
  | BAnd b1 b2  => match (beval st b1) with
    | Some v => match (beval st b2) with
      | Some v0 => Some (andb v v0)
      | None => None
      end
    | None => None
    end
  end.

Theorem AEvalR : forall (Sigma : State) (A : AExp) (n : nat),
  (((aeval Sigma A) = Some n) <-> (ConfigEquivR (S_AExpConf A Sigma) (S_AExpConf (ANum n) Sigma))).
  Proof.
  intros.
  split.
  generalize dependent n.
  induction A.
  intros.
  inversion H.
  apply SmallStep.
  apply Reflex.
  intros.
  admit.
  admit.
  admit.
  intros.
  generalize dependent n.
  induction A.
  intros.
  simpl.
  cut (n = n0).
  intros.
  subst.
  reflexivity.
  cut (forall (X Y : SmallConfig), (ConfigEquivR X Y )).
  inversion H ; subst.
  
  
  Admitted.

Theorem BEvalR : forall (Sigma : State) (B : BExp) (b : bool),
  (((beval Sigma B) = Some b) <-> (SmallStepR (S_BExpConf B Sigma) (S_BExpConf (BVal b) Sigma))).
  Proof.
  Admitted.

Theorem Confluence : forall (A B C : SmallConfig),
  (SmallStepR A B) -> (SmallStepR A C) -> exists D : SmallConfig, ((SmallStepR B D) /\ (SmallStepR C D)).
Proof.
  induction A ; intros.
  - induction a.
  admit.
  destruct a1 ; destruct a2 ; try rewrite PlusANums in H.
  destruct B.
  intros.
  refine (ex_intro _ _ _).
  refine (conj _ _).
  induction B.
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  

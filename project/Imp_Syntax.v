Require Import Coq.Strings.String.
Require Export ZArith_base.
Require Import Coq.Init.Nat.

Inductive AExp : Type :=
  | ANum : nat -> AExp
  | APlus : AExp -> AExp -> AExp
  | ADiv : AExp -> AExp -> AExp
  | AId : string -> AExp.

Inductive BExp : Type :=
  | BVal : bool -> BExp
  | BLe : AExp -> AExp -> BExp
  | BNot : BExp -> BExp
  | BAnd : BExp -> BExp -> BExp.

Compute BVal true.
Example test_BVal: (BVal true) = BVal true.
Proof. simpl. reflexivity. Qed.

Inductive Block : Type :=
  | EmptyBlk : Block
  | Blk : Statement -> Block
with Statement : Type :=
  | Assignment : string -> AExp -> Statement
  | Seq : Statement -> Statement -> Statement
  | IfElse : BExp -> Block -> Block -> Statement
  | While : BExp -> Block -> Statement.

Inductive Program : Type :=
  | Pgm : list string -> Statement -> Program.

Definition State := string -> (option nat).
Definition t_update (m : State) (x : string) (v : nat) :=
  fun x' => if string_dec x x' then Some v else m x'.
  
Fixpoint aeval (st : State) (a : AExp) : option nat :=
  match a with
  | ANum n => Some n
  | AId x => st x
  | APlus a1 a2 => 
    match (aeval st a1) with 
    | Some n => 
      match (aeval st a2) with
        | Some n0 => Some (n + n0)
        | None => None
      end
    | None => None
    end
  | ADiv a1 a2 => 
    match (aeval st a2) with
      | Some 0 => None
      | Some (S n) => 
        match (aeval st a1) with
          | Some n0 => Some ( div n0 (S n))
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

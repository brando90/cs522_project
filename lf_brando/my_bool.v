Inductive bool : Type :=
  |true : bool
  |false : bool.

Definition negb (b:bool) : bool :=
  match b with
  |true => false
  |false => true
end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  |true => b2
  |false => b1
end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  |true => b1
  |false => b2
end.

Definition xrb (b1:bool) (b2:bool) : bool :=
  match b1 with
  |false => b2
  |true => negb b2
end.

Compute (xrb false false).
Compute (xrb true true).

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_xrb1: (xrb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_xrb2: (xrb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_xrb3: (xrb true false) = true.
Proof. simpl. reflexivity. Qed.
Example text_xrb4: (xrb true true) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
Example test_arb: true && true && false = false.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  (negb (andb b1 b2)).

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3 .

Compute andb true true.
Compute andb3 true true true.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.
Example test_andb35: (andb3 false false true) = false.
Proof. reflexivity. Qed.
Example test_andb36: (andb3 false true false) = false.
Proof. reflexivity. Qed.
Example test_and37: (andb3 true false false) = false.
Proof. reflexivity. Qed.
Example test_and38: (andb3 false false false) = false.
Proof. reflexivity. Qed.

Check true.
Check negb true.
Check negb.
Check andb.

(* Colors *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Module color_lib.

Definition monochrome (c : color) : bool :=
(* Monochrome means black and white *)
  match c with
  | black => true
  | white => true
  | primary p => false (* for any color that isn't black white, then its not monochrome!*)
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

End color_lib.

Compute red.
Compute black.
Compute primary _.
Compute primary red.
Check primary .
Check primary _.
Compute color_lib.monochrome (primary _).
Compute color_lib.monochrome black.
Compute color_lib.isred (primary red).

(* *)

Module NatPlayground.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Compute 0.
Compute O.
Compute 1.
Compute S O.
Compute S (S O).

(* End NatPlayground. *)

Check (S (S (S (S O)))).
Check S (S O) .
Compute pred O .
Compute pred ( S (S O) ) .

End NatPlayground.

Check S O .
Check (S (S O) ) .

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4) .

Definition minusthree (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S ( S O ) => O
    | S ( S ( S n' ) ) => n'
  end.

Compute (minusthree 0) .
Compute (minusthree 1) .
Compute (minusthree 2) .
Compute (minusthree 3) .
Compute (minusthree 4) .
Compute (minusthree 7) .

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n' (* unpeal the pair of successors! *)
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.
Example test_even1: evenb 0 = true.
Proof. simpl. reflexivity. Qed.
Example test_even2: evenb 11 = false.
Proof. simpl. reflexivity. Qed.
Example test_even3: evenb 33 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m) (* unpleas the # of succesors from both until they are all piled up on one function *)
  end.

Compute (plus 3 2).

(*  plus (S (S (S O))) (S (S O))
==> S (plus (S (S O)) (S (S O)))
      by the second clause of the match
==> S (S (plus (S O) (S (S O))))
      by the second clause of the match
==> S (S (S (plus O (S (S O)))))
      by the second clause of the match
==> S (S (S (S (S O))))
      by the first clause of the match
*)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O (* any subtraction to the negatives goes to zero *)
  | S _ , O => n (* if n is any number greater than 1 return the original number *)
  | S n', S m' => minus n' m' (* peal off the difference *)
  end.

Compute ( minus 3 2 ) .
Compute ( minus 2 3 ) .

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p) (* 2^n = 2x2^(n-1) *)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 4) = 24.
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).
Compute ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Compute andb true true .

Definition blt_nat (n m : nat) : bool :=
  ( andb (leb n m) (negb (beq_nat n m))  ).
  
Compute blt_nat 2 3.
Compute blt_nat 3 2.

Example test_lt_nat00: (blt_nat 2 3) = true.
Proof. simpl. reflexivity. Qed.
Example test_lt_nat0: (blt_nat 3 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* proof by simplification *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: with name H *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  (* rewrite -> H. (* n + n = m + m ==> m + m = m + m *) *)
  rewrite <- H. (* n + n = m + m ==> n + n = n + n *)
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n. (* 0 + n = n *)
  reflexivity. 
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  simpl.
  rewrite <- H.
  reflexivity.
Qed.


(* proof by cases *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. 
  destruct n as [| n'].
    - rewrite -> plus_O_n. 
      simpl. reflexivity.
    - simpl. reflexivity. 
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity. 
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    reflexivity.
    reflexivity. }
  { destruct c.
    reflexivity.
    reflexivity. }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. 
Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* intros x y. destruct y as [|y]. === intros [|y] *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b as [].
  - simpl. intros H. rewrite H. reflexivity.
  - { destruct c as [].
    + simpl. intros H. reflexivity.
    + simpl. intros H. rewrite H. reflexivity.
  }
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [].
  -rewrite->plus_O_n. simpl. reflexivity.
  -simpl. reflexivity.
Qed.

(* Math 570 show forall x ( x<2-> x=0 OR x=1 *)

(*
Theorem x_less_ssO : forall x : nat,
  blt_nat x (S (S O) ) = true -> 
  ( (orb (beq_nat x 0) (beq_nat x (S O))) = true ).
Proof.
  intros x.
  induction x as [| x' IHx'].
  (* intuition: by cases, we have x < 2, so consider 0, 1. Then the claim is true. 
  For the other case for n, n > 2 so the assumption is false, so the implication is true
  Done. How to express this in Coq. Or is there a different proof the prof had in mind?*)
  (* Or use axiom N8, now how do we encode that axiom?*)
  - intros H. simpl. reflexivity.
  - intros H. simpl. simpl. 
Qed.
*)

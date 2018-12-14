
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n' (* unpeal the pair of successors! *)
  end.

Example eveb_test1: evenb 0 = true.
Proof. simpl. reflexivity.
Qed.
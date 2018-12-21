(* Tactics:
  - The tactics implement backward reasoning.
  - backwards reasoning: \u201cto prove this I have to prove this and this\u201d
  - We say that the conclusion is the goal to prove and premises are the subgoals (to be proved).
*)

(* reflexivity *)

Lemma everything_is_itself:
  forall x: Set, x = x.
Proof.
  intro.
  reflexivity.
Qed.

(* assumption: 
Use it when: your goal is already in your "context" of terms you already know.
*)

Lemma everything_implies_itself:
  forall p: Prop, p -> p.
Proof.
  intros.
  assumption.
Qed.

(* discriminate:
If you have an equality in your context that isn't true, you can prove anything using discriminate.
This tactic proves any goal from an assumption stating that two structurally different terms of an inductive set are equal. 
For example, from (S (S O))=(S O) we can derive by absurdity any proposition.
*)

Inductive bool: Set :=
  | true
  | false.

Lemma incorrect_equality_implies_anything:
  forall a, false = true -> a.
Proof.
  intros.
  discriminate.
Qed.

(* constructor: when you want to prove that a term has some type and you a constructor to do
  just that, then use constructor tactic!

*)

Inductive even : nat -> Prop:=
 | even_O: even O
 | even_S: forall n, even n -> even (S(S n)).

Lemma two_is_even:
  even (S (S O)).
Proof.
  constructor.
  constructor.
Qed.

(* apply: 
    - If we have a hypothesis that says that x implies y, 
      we know that to prove y all we really have to do is prove x.
    - The tactic apply attempts to use the function/lemma/etc. to prove the current goal.
    - The tactic apply tries to match the current goal against the conclusion of the type of term. 
      If it succeeds, then the tactic returns as many subgoals as the number of non-dependent premises
      of the type of term.

    - Use it when: you have a hypothesis where the conclusion (on the right of the arrow) is the same as your goal.
    - Advanced usage: If we know that x implies y and we know that x is true, we can transform x into y in our context using apply. 
*)

Theorem four_4_is_even : even 4.
Proof.  (* goal: ev 4*)
  apply even_S.
  apply even_S.
  apply even_O.
Qed.

Lemma modus_ponens:
  forall p q : Prop, (p -> q) -> p -> q.
Proof.
  intros.
  apply H. 
  (* transforms the goal q by matching the conclusion of p->q, seeing they match
  and thus transform the goal q to proving the premise p.*)
  assumption. (* note the premise is in the current context of things that are true so we are done *)
Qed.

Lemma modus_ponens_again:
  forall p q : Prop, (p -> q) -> p -> q.
Proof.
  intros.
  apply H in H0. (* applies hypothesis H in H0 to change the context! *)
  (* in particular since H:p->q and H0:p using MP we can transform H0 to q *)
  assumption. (* due to using MP on the context, we changed p to q and now we can tell coq our goal is in the cotext already *)
Qed.

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

(* 
  subst: 
    - substitute/transforms an identifier/name appearing in your goal
      from an identifier appearing in your context/assumptions.

    - Use it when: you want to transform an identifier into an equivalent term.
*)


Lemma equality_commutes:
  forall (a: bool) (b: bool), a = b -> b = a.
  (* Goal: forall (a: bool) (b: bool), a = b -> b = a. *)
Proof.
  intros. 
  (* 
  | Context: a,b : bool, H: a=b 
  | Goal: b=a 
  *)
  subst. (* since a is b, we can replace a for b in goal *)
  reflexivity. (* proof ends because we have b=b *)
Qed.

Lemma xyz_subst:
  forall (f: bool->bool) x y z,
    x=y -> y=z -> f x=f z.
Proof.
  intros.
  subst. (* TODO *)
  reflexivity.
Qed.

(* 
  rewrite: 
    -If we know two terms are equal we can transform one term into the other using rewrite.

    - An identity is just a name like x, while a term can be more complex, 
      like a function application: (f x).

    - Use it when: you know two terms are equivalent and you want to transform one into the other
    - Advanced usage: you can also apply rewrite backwards, and to terms in your context.
    TODO: difference with substitute, might just need to know the difference of identifier and terms.
*)

Lemma equality_of_functions_commutes:
  forall (f: bool->bool) x y,
    (f x) = (f y) -> (f y) = (f x).
  (* 
    Goal: forall (f : bool -> bool) (x y : bool), 
          f x = f y -> f y = f x 
  *)
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma equality_of_functions_commutes_BACKWARDS:
  forall (f: bool->bool) x y,
    (f x) = (f y) -> (f y) = (f x).
  (* 
    Goal: forall (f : bool -> bool) (x y : bool), 
          f x = f y -> f y = f x 
  *)
Proof.
  intros.
  rewrite <- H.
  reflexivity.
Qed.

Lemma equality_of_functions_transits:
  forall (f: bool->bool) x y z,
    (f x) = (f y) ->
    (f y) = (f z) ->
    (f x) = (f z).
Proof.
  intros.
  rewrite H0 in H. (* or rewrite <- H0 *)
  assumption.
Qed.

Lemma xyz_rewrite:
  forall (f: bool->bool) x y z,
    x=y -> y=z -> f x=f z.
Proof.
  intros.
  rewrite H0 in H.
  rewrite -> H.
  reflexivity.
Qed.

(* 
  simpl:
    - When we have a complex term we can use simpl to crunch it down.
*)

Fixpoint add (a: nat) (b: nat) : nat :=
  match a with
    | O => b
    | S x => S (add x b) (* note this just tacks on Successors to b, exactly a of them *)
  end.

Compute add 1 0.
Compute add 3 0.

Lemma zero_plus_n_equals_n:
  forall n, (add O n) = n.
Proof.
  intros. (* Context: n:nat, Goal: add 0 n = n *)
  simpl. (* runs the add function on the Goal *)
  reflexivity.
Qed.

(*
  cut:
    - insert a new assumptions. Prove the original goal with the new assumption. Now prove
    the new assumption.
    -Sometimes to prove a goal you need an extra hypothesis. In this case, you can add the 
    hypothesis using cut.
    This allows you to first prove your goal using the new hypothesis, and then prove that 
    the new hypothesis is also true.

    - Use it when: you want to add an intermediate hypothesis to your proof 
      that will make the proof easier.
*)

Lemma xyz:
  forall (f: bool->bool) x y z,
    x=y -> y=z -> f x=f z.
Proof.
  intros.
  cut (x = z).
  (* prove original goal with new assumption *)
  - intro. subst. reflexivity.
  (* prove new assumption *)
  - subst. reflexivity.
Qed.

(*
  unfold:
  
    - Use it when: you want to replace a definition with its body.
*)

Definition inc (n : nat) : nat := n + 1.

Lemma foo_defn : 
  forall n, 
  inc n = S n.
Proof.
  intros n.
  (* This doesn't work because rewrite can't "see through" the definition: *)
  Fail rewrite <- plus_n_Sm.
  unfold inc.
  (* Now it works! *)
  rewrite <- plus_n_Sm. (* TODO check this *)
  rewrite <- plus_n_O.
  reflexivity.
Qed.

(*
  destruct: 
    -performs case analysis on a term.
*)

Definition not (b: bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Lemma not_not_x_equals_x:
  forall b, not (not b) = b.
Proof.
  intro.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* 
  inversion:
    -Sometimes you have a hypothesis that can't be true unless other things are also true. 
     We can use inversion to discover other necessary conditions for a hypothesis to be true.
    -Introduce new information to context based on hypotheses.
     it "reverse engineers" a known hypothesis to **discover** new stuff and put it in the context
     so that it can be used in the proof.
*)

Lemma successors_equal_implies_equal:
  forall a b, 
  S a = S b -> a = b.
  (* Goal: S a = S b -> a = b. *) 
Proof.
  intros.
  (*
  | Context: H: S a = S b
  | Goal: a = b
  *)
  inversion H. (* discovers that H: S a = S b, can only be true if a = b, and puts that knowledge in the context *)
  (* TODO: why did it also change the goal?
  | Context: H: S a = S b, H1: a = b
  | Goal: a = b
  *)  
  reflexivity.
Qed.

(* 
  induction:
    -When we use induction, Coq generates subgoals for every possible constructor of the term, 
     similar to destruct.
    -However, for inductive constructors (like S x for nats), you also get an inductive hypothesis 
     to help you prove your goal.
*)

(*
Fixpoint add (a: nat) (b: nat) : nat :=
  match a with
    | O => b
    | S x => S (add x b)
  end.
*)

Lemma n_plus_zero_equals_n:
  forall n, 
    (add n O) = n.
Proof.
  induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
Qed.

(*
  auto:
    - auto will intro variables and hypotheses and then try applying various other tactics 
      to solve the goal. Which other tactics does it try? Who knows man.
    - The good thing is that auto can't fail. At worst it will leave your goal unchanged. So go wild!

    - Use it when: you think the goal is easy but you're feeling lazy.
      - TODO find a better heuristic for this...
*)

Lemma modus_tollens:
forall p q: Prop,
  (p->q) -> ~q -> ~p.
Proof.
  auto. (* TODO lol see what the heck this is doing *)
Qed.

(* 
  intuition:
    - better version of auto?
    - The intuition tactic also intros variables and hypotheses and applies tactics to them, including auto. Sometimes it works when auto doesn't.

    -Q: whats the difference of this and auto?
    -Use it when: auto doesn't work but you think it should be easy to prove.
*)

Lemma conjunction_elimination:
forall p q,
  p /\ q -> p.
Proof.
  intuition. (* TODO figure out what this does *)
Qed.

(*
  Omega:
    - If you are trying to prove something "mathy" you should try the omega tactic. 
      It's good at reasoning about goals involving nats and integers.
*)

Require Import ZArith.
(* or Require Import Omega. *)

Lemma odds_arent_even:
forall a b: nat,
  2*a + 1 <> 2*b.
Proof.
  intros.
  omega. (* TODO: what does this do? *)
Qed.
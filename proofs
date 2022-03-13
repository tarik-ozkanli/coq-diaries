Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.

Proof.

intros a b H.

split.

destruct H as [H1 H2].

exact H2.

intuition.

Qed.


Lemma example3 : forall A B, A \/ B -> B \/ A.

Proof.


intros A B H.

destruct H as [H1 | H1].

right; assumption.

left; assumption.

Qed.


Check le_n.

Check le_S.

Lemma example4 : 3 <= 5.

Proof.

apply le_S.

apply le_S.

apply le_n.

Qed.

Require Import Arith.

Check Nat.le_trans.

Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.

Proof.
intros x y x10 y10.

apply le_trans with (m := 10).

assumption.

assumption.

Qed.

Lemma example6 : forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.

Proof.

intros x y.

SearchRewrite (_ * (_ + _)).

rewrite Nat.mul_add_distr_l.

SearchRewrite ((_ + _) * _).

rewrite Nat.mul_add_distr_r with (p:=x).

rewrite Nat.mul_add_distr_r.

SearchRewrite (_ + (_ + _)).

rewrite Nat.add_assoc.

rewrite <- Nat.add_assoc with (n := x * x).

SearchPattern (?x * ?y = ?y * ?x).

rewrite Nat.mul_comm with (n:= y) (m:=x).

SearchRewrite (S _ * _).

rewrite <- (Nat.mul_1_l (x * y)) at 1.

rewrite <- Nat.mul_succ_l.

SearchRewrite (_ * (_ * _)).

rewrite Nat.mul_assoc.

reflexivity.

Qed.


Lemma ex_trivia : forall x:nat, x = x.

Proof.

reflexivity.

Qed.

























Set Implicit Arguments.
Require Import Omega.

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

Definition valley(f : nat -> nat)(n x : nat) := forall y, x <= y -> y <= n+x -> f y = f x.

Lemma decr_0 : forall f x, decr f -> f x = 0 -> forall y, x <= y -> f y = 0.
Proof.
  intros.
  induction y.
  inversion H1.
  rewrite H2 in H0; exact H0.
  inversion H1.
  rewrite <- H2; exact H0.
  pose (H y).
  pose (IHy H3).
  omega.
Qed.

Lemma zero_valley : forall f n x, decr f -> f x = 0 -> valley f n x.
Proof.
  intros f n x fd fx y Hxy _.
  rewrite fx.
  exact (decr_0 fd fx Hxy).
Qed.

Lemma arith_lemma : forall x y, x <= y -> x = y \/ S x <= y.
Proof.
  intros.
  omega.
Qed.

Lemma valley_or_drop : forall n f x, decr f -> valley f n x \/ exists y, f y < f x.
Proof.
  induction n; intros.
  left.
  intros y H1 H2.
  simpl in H2.
  assert (x = y).
  omega.
  rewrite H0; reflexivity.
  destruct (IHn _ (S x) H).
  pose (G := H x).
  inversion G.
  left.
  intros y Hy1 Hy2.
  destruct (arith_lemma Hy1).
  rewrite H1; reflexivity.
  rewrite <- H2.
  apply H0.
  exact H1.
  omega.
  right.
  exists (S x).
  omega.
  right.
  destruct H0 as [y Hy].
  exists y.
  pose (G := H x).
  omega.
Qed.

Lemma valley_aux : forall y f x n, f x <= y -> decr f -> exists x', valley f n x'.
Proof.
  induction y; intros.
  intros.
  exists x.
  apply zero_valley.
  exact H0.
  inversion H.
  reflexivity.
  destruct (valley_or_drop n x H0).
  exists x.
  exact H1.
  destruct H1 as [x' Hx'].
  assert (f x' <= y).
  omega.
  destruct (IHy f x' n H1 H0).
  exists x0; exact H2.
Qed.

Theorem decr_valleys : forall n f, decr f -> exists x, valley f n x.
Proof.
  intros.
  exact (valley_aux 0 n (le_refl (f 0)) H).
Qed.
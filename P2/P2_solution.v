Set Implicit Arguments.
Require Import Omega.
Require Import Coq.Arith.Max.

Definition LPO := forall f : nat -> bool, (exists x, f x = true) \/ (forall x, f x = false).

Fixpoint true_below(f : nat -> bool)(x : nat) : bool :=
  match x with
  |0   => f 0
  |S y => f x || true_below f y
  end.

Lemma true_below_correct1 : forall f x, true_below f x = true -> exists y, f y = true.
Proof.
  intros.
  induction x.
  exists 0.
  exact H.
  simpl in H.
  destruct (f (S x)) eqn:G.
  exists (S x); exact G.
  apply IHx.
  exact H.
Qed.

Lemma f_true_below : forall f x, f x = true -> true_below f x = true.
Proof.
  intros.
  destruct x.
  exact H.
  simpl.
  rewrite H; reflexivity.
Qed.

Lemma true_below_correct2 : forall f x y, true_below f x = true -> x <= y -> true_below f y = true.
Proof.
  intros f x.
  induction x.
  intros.
  induction y.
  exact H.
  simpl.
  rewrite IHy.
  destruct (f (S y)); reflexivity.
  omega.
  induction y.
  intros.
  inversion H0.
  intros.
  inversion H0.
  rewrite <- H2; exact H.
  simpl.
  rewrite IHy.
  destruct (f (S y)); reflexivity.
  exact H.
  exact H2.
Qed.

Definition to_nat(f : nat -> bool) : nat -> nat :=
  fun x => if f x then 0 else 1.

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

Lemma decr_shift : forall y f, decr f -> decr (fun x => f (x + y)).
Proof.
  induction y; simpl; intros; intro x.
  apply H.
  simpl.
  apply H.
Qed.

Lemma decr_antitone : forall f, decr f -> forall x y, x <= y -> f y <= f x.
Proof.
  intros.
  induction y.
  inversion H0.
  omega.
  inversion H0.
  omega.
  pose (IHy H2).
  pose (H y).
  omega.
Qed.

Lemma decr_0 : forall f, decr f -> f 0 = 0 -> forall x, f x = 0.
Proof.
  intros.
  induction x.
  exact H0.
  pose (G := H x).
  omega.
Qed.

Lemma to_nat_decr : forall f, decr (to_nat (true_below f)).
Proof.
  intros f x.
  unfold to_nat.
  simpl.
  destruct (f (S x)); simpl; omega.
Qed.

Definition infvalley(f : nat -> nat)(x : nat) := forall y, x <= y -> f y = f x.

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Proof.
  intros H f.
  destruct (H _ (to_nat_decr f)).
  unfold to_nat,infvalley in H0.
  destruct (true_below f x) eqn:G.
  left.
  exact (true_below_correct1 _ _ G).
  right.
  intro y.
  destruct (f y) eqn:fy.
  destruct (true_below f (max x y)) eqn:G1.
  pose (G2 := H0 _(le_max_l x y)).
  rewrite G1 in G2.
  discriminate G2.
  pose (G2 := f_true_below _ _ fy).
  rewrite (true_below_correct2 _ G2 (le_max_r x y)) in G1.
  exact G1.
  reflexivity.
Qed.

Definition Slt(f : nat -> nat) : nat -> bool :=
  fun x => match lt_dec (f (S x)) (f x) with
           |left _  => true
           |right _ => false
           end.

(*to avoid creating ill-typed terms*)
Lemma obvious : forall f x, f (S x) < f x -> Slt f x = true.
Proof.
  intros.
  unfold Slt.
  destruct (lt_dec (f (S x)) (f x)).
  reflexivity.
  contradiction.
Qed.

Lemma Slt_correct1 : forall f, decr f -> (forall x, Slt f x = false) -> forall x, f x = f 0.
Proof.
  intros.
  induction x.
  reflexivity.
  destruct (lt_dec (f (S x)) (f x)).
  pose (G := H0 x).
  rewrite (obvious _ _ l) in G.
  discriminate G.
  pose (G := H x).
  omega.
Qed.

Lemma Slt_correct2 : forall f, decr f -> forall y, Slt f y = true -> f (S y) < f 0.
Proof.
  intros.
  unfold Slt in H0.
  destruct (lt_dec (f (S y)) (f y)).
  assert (0 <= y).
  omega.
  pose (decr_antitone H H1).
  omega.
  discriminate H0.
Qed.

Lemma arith_lemma : forall x y z, x + y <= z -> exists u, z = u + y.
Proof.
  intros.
  exists (z - y).
  omega.
Qed.

Lemma infvalley_shift : forall s f x, infvalley (fun x => f (x + s)) x -> infvalley f (x + s).
Proof.
  intros s f x v y Hy.
  destruct (arith_lemma _ _ Hy) as [y' Hy'].
  rewrite Hy'.
  apply v.
  omega.
Qed.

Lemma infvalley_aux : LPO -> forall n f, f 0 <= n -> decr f -> exists x, infvalley f x.
Proof.
  intros H n; induction n.
  intros.
  assert (f 0 = 0).
  omega.
  exists 0.
  intros x _.
  rewrite H2.
  rewrite (decr_0 H1 H2).
  reflexivity.
  intros.
  destruct (H (Slt f)).
  destruct H2.
  pose (Slt_correct2 H1 _ H2).
  assert (f (S x) <= n).
  omega.
  destruct (IHn _ H3 (decr_shift _ H1)).
  exists (x0 + S x).
  apply infvalley_shift.
  exact H4.
  exists 0.
  pose (Slt_correct1 H1 H2).
  intros y _.
  apply e.
Qed.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Proof.
  intros H f fd.
  exact (infvalley_aux H (le_refl (f 0)) fd).
Qed.

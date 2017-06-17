Set Implicit Arguments.
Require Import Omega.
Require Import Coq.Arith.Max.

(* some arithmetical lemmas *)

Lemma max_lemma_l : forall x y z, x <> S (max x y + z).
Proof.
  induction x; intros.
  omega.
  destruct y.
  simpl; omega.
  simpl.
  pose (IHx y z).
  omega.
Qed.

Lemma max_lemma_r : forall x y z, y <> S (max x y + z).
Proof.
  intros; rewrite max_comm.
  apply max_lemma_l.
Qed.

Lemma incr_global : forall f, (forall x, f x <= f (S x)) -> forall x y, x <= y -> f x <= f y.
Proof.
  intros f H x.
  destruct x.
  induction y; intros.
  omega.
  assert (0 <= y).
  omega.
  pose (IHy H1).
  pose (H y).
  omega.
  intros.
  induction y.
  omega.
  inversion H0.
  omega.
  pose (IHy H2).
  pose (H y).
  omega.
Qed.

Lemma incr_global_strict : forall f, (forall x, f x < f (S x)) -> forall x y, x < y -> f x < f y.
Proof.
  intros.
  assert (forall x, f x <= f (S x)).
  intro z; pose (H z). omega.
  assert (x <= y). omega.
  pose (incr_global _ H1).
  pose (l _ _ H2).
  inversion l0.
  inversion H0.
  rewrite <- H3 in H4.
  pose (H x).
  omega.
  rewrite <- H5 in H4.
  pose (H x).
  pose (l _ _ H3).
  pose (H m).
  omega.
  omega.
Qed.

Lemma incr_inj : forall f, (forall x, f x < f (S x)) -> forall x y, x <> y -> f x <> f y.
Proof.
  intros.
  destruct (lt_dec x y).
  pose (incr_global_strict _ H l).
  omega.
  assert (y < x).
  omega.
  pose (incr_global_strict _ H H1).
  omega.
Qed.

(* streamless stuff *)

Definition streamless(X : Set) := forall f : nat -> X, 
  {i : nat & {j : nat & i <> j /\ f i = f j}}.

Definition hat(X : Set)(x0 : X)(f : nat -> unit + X) : nat -> X :=
  fun n => match f n with
           |inl _ => x0
           |inr x => x
           end.

Lemma streamless_lemma : forall X, streamless X -> forall (x0 : X)(i j : nat)(f : nat -> unit + X), 
  f i = inl tt -> f j = inr x0 -> {i0 : nat & {j0 : nat & i0 <> j0 /\ f i0 = f j0}}.
Proof.
  intros X Xstr x0 i j f fi fj.
  destruct (Xstr (fun n => hat x0 f (S (max i j + n)))) as [k [l [klneq Hkl]]].
  unfold hat in Hkl.
  destruct (f (S (max i j + k))) as [[]|xk] eqn:fk.
  exists i,(S (max i j + k)).
  split.
  apply max_lemma_l.
  rewrite fk; exact fi.
  destruct (f (S (max i j + l))) as [[]|xl] eqn:fl.
  exists i,(S (max i j + l)).
  split.
  apply max_lemma_l.
  rewrite fl;  exact fi.
  exists (S (max i j + k)),(S (max i j + l)).
  split.
  omega.
  rewrite fl; rewrite <- Hkl; exact fk.
Qed.

Lemma streamless_plus_one_inh : forall X, streamless X -> X -> streamless (unit + X).
Proof.
  intros X Xstr x0 f.
  destruct (Xstr (hat x0 f)) as [i [j [ijneq gijeq]]].
  unfold hat in gijeq.
  destruct (f i) as [[]|xi] eqn:fi.
  destruct (f j) as [[]|xj] eqn:fj.
  exists i,j.
  split.
  exact ijneq.
  rewrite fj; exact fi.
  exact (streamless_lemma Xstr _ _ _ fi fj).
  destruct (f j) as [[]|xj] eqn:fj.
  exact (streamless_lemma Xstr _ _ _ fj fi).
  exists i,j.
  split.
  exact ijneq.
  rewrite fj; rewrite <- gijeq; exact fi.
Qed.

Lemma streamless_plus_one : forall X, streamless X -> streamless (unit + X).
Proof.
  intros X Xstr f.
  destruct (f 0) as [[]|x0] eqn:f0.
  destruct (f 1) as [[]|x1] eqn:f1.
  exists 0,1; split.
  discriminate.
  rewrite f1; exact f0.
  exact (streamless_plus_one_inh Xstr x1 _).
  exact (streamless_plus_one_inh Xstr x0 _).
Qed.

Definition hat_l(X Y : Set)(f : nat -> X + Y) : nat -> unit + X :=
  fun n => match f n with
           |inl x => inr x
           |inr _ => inl tt
           end.

Definition hat_r(X Y : Set)(f : nat -> X + Y) : nat -> unit + Y :=
  fun n => match f n with
           |inl _ => inl tt
           |inr y => inr y
           end.

Lemma str_lt_wlog : forall X, streamless X -> forall f : nat -> X,
  {i : nat & {j : nat & i < j /\ f i = f j}}.
Proof.
  intros X Xstr f.
  destruct (Xstr f) as [i [j [ijneq Hij]]].
  destruct (lt_dec i j).
  exists i,j.
  split.
  exact l.
  exact Hij.
  exists j,i.
  split.
  omega.
  symmetry; exact Hij.
Qed.

Lemma str_lt : forall (X : Set)(n : nat)(f : nat -> X), streamless X -> 
  {i : nat & {j : nat & n < i /\ i < j /\ f i = f j}}.
Proof.
  intros X n f Xstr.
  destruct (str_lt_wlog Xstr (fun m => f (S (m + n)))) as [i [j [ijleq Hij]]].
  exists (S (i + n)),(S (j + n)).
  split.
  omega.
  split.
  omega.
  exact Hij.
Qed.

Fixpoint subseq(X : Set)(Xstr : streamless X)(f : nat -> X)(n : nat) : nat :=
  match n with
  |0   => projT1 (str_lt 0 f Xstr)
  |S m => projT1 (str_lt (subseq Xstr f m) f Xstr)
  end.

Lemma subseq_incr : forall (X : Set)(Xstr : streamless X)(f : nat -> X)(n : nat),
  subseq Xstr f n < subseq Xstr f (S n).
Proof.
  intros.
  simpl.
  destruct (str_lt (subseq Xstr f n) f Xstr) as [i [j [H1 [H2 H3]]]].
  simpl.
  omega.
Qed.

Theorem streamless_sum : forall X Y, streamless X -> streamless Y -> streamless (X + Y).
Proof.
  intros X Y Xstr Ystr f.
  pose (is := subseq (streamless_plus_one Xstr) (hat_l f)).
  destruct (streamless_plus_one Ystr (fun x => hat_r f (is x))) as [k [l [klneq fkl]]].
  unfold hat_r in fkl.
  destruct (f (is k)) as [xk|yk] eqn:fi.
  unfold is in fi.
  destruct k.
  simpl in fi.
  destruct (str_lt 0 (hat_l f) (streamless_plus_one Xstr)) as [i [j [ijneq [H1 H2]]]].
  simpl in fi.
  unfold hat_l in H2.
  rewrite fi in H2.
  destruct (f j) as [xj|yj] eqn:fj.
  exists i,j.
  split.
  omega.
  rewrite fi,fj.
  inversion H2; reflexivity.
  discriminate H2.
  simpl in fi.
  destruct (str_lt (subseq (streamless_plus_one Xstr) (hat_l f) k) (hat_l f) (streamless_plus_one Xstr))
    as [i [j [ijneq [H1 H2]]]].
  simpl in fi.
  unfold hat_l in H2.
  rewrite fi in H2.
  destruct (f j) as [xj|yj] eqn:fj.
  exists i,j.
  split.
  omega.
  rewrite fi,fj.
  inversion H2; reflexivity.
  discriminate H2.
  destruct (f (is l)) as [xl|yl] eqn:fj.
  discriminate fkl.
  exists (is k),(is l).
  split.
  apply incr_inj.
  apply subseq_incr.
  exact klneq.
  rewrite fi,fj.
  inversion fkl; reflexivity.
Qed.

Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.

Definition ded_fin(X : Set) := forall f : X -> X, inj f -> surj f.

Section df_inh_cancel_sgroups.

Variable X : Set.
Variable x0 : X.
Variable m : X -> X -> X.

Infix "*" := m.

Hypothesis X_df : ded_fin X.
Hypothesis assoc : forall x y z, x * (y * z) = (x * y) * z.
Hypothesis l_cancel : forall x y z, x * y = x * z -> y = z.
Hypothesis r_cancel : forall x y z, y * x = z * x -> y = z.

Lemma l_mult_inj : forall x, inj (m x).
Proof.
  intros x y z H.
  exact (l_cancel _ _ _ H).
Qed.

Lemma r_mult_inj : forall x, inj (fun y => m y x).
Proof.
  intros x y z H.
  exact (r_cancel _ _ _ H).
Qed.

Lemma r_eq_solve : forall a b, {x : X & a * x = b}.
Proof.
  intros.
  destruct (X_df (m a) (l_mult_inj a) b).
  exists x; exact e.
Qed.

Lemma l_eq_solve : forall a b, {x : X & x * a = b}.
Proof.
  intros.
  destruct (X_df (fun y => m y a) (r_mult_inj a) b).
  exists x; exact e.
Qed.

(* the identity *)
Definition e : X := projT1 (l_eq_solve x0 x0).

Lemma l_x0_id : e * x0 = x0.
Proof.
  unfold e.
  destruct (l_eq_solve x0 x0).
  simpl.
  exact e0.
Qed.

Theorem l_id : forall x, e * x = x.
Proof.
  intro.
  destruct (r_eq_solve x0 x) as [y Hy].
  rewrite <- Hy.
  rewrite assoc.
  rewrite l_x0_id.
  reflexivity.
Qed.

Theorem r_id : forall x, x * e = x.
Proof.
  intro.
  apply (r_cancel e).
  rewrite <- assoc.
  rewrite l_id.
  reflexivity.
Qed.

(* the inverse operations *)
Definition inv : X -> X := fun x => projT1 (l_eq_solve x e).

Theorem l_inv : forall x, (inv x) * x = e.
Proof.
  intro.
  unfold inv.
  destruct (l_eq_solve x e).
  simpl.
  exact e0.
Qed.

Theorem r_inv : forall x, x * (inv x) = e.
Proof.
  intro.
  apply (r_cancel x).
  rewrite <- assoc.
  rewrite l_inv.
  rewrite l_id, r_id.
  reflexivity.
Qed.

End df_inh_cancel_sgroups.
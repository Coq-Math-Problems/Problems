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

(* the identity *)
Definition e : X.
Admitted.

Theorem l_id : forall x, e * x = x.
Admitted.

Theorem r_id : forall x, x * e = x.
Admitted.

(* the inverse operation *)
Definition inv : X -> X.
Admitted.

Theorem l_inv : forall x, (inv x) * x = e.
Admitted.

Theorem r_inv : forall x, x * (inv x) = e.
Admitted.

End df_inh_cancel_sgroups.

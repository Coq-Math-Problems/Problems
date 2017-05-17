Definition LPO := forall f : nat -> bool, (exists x, f x = true) \/ (forall x, f x = false).

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

Definition infvalley(f : nat -> nat)(x : nat) := forall y, x <= y -> f y = f x.

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Admitted.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Admitted.

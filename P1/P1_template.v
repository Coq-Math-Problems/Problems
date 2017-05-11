Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

Definition valley(f : nat -> nat)(n x : nat) := forall y, x <= y -> y <= n+x -> f y = f x.

Lemma decr_valleys : forall n f, decr f -> exists x, valley f n x.
Admitted.

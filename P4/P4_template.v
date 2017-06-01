Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.

(* feel free to change this if you prefer other formalizations of Fin *)
Fixpoint Fin(n : nat) : Set :=
  match n with
  |0   => Empty_set
  |S m => unit + Fin m
  end.

Theorem inj_surj_same(n : nat) : forall f : Fin n -> Fin n, inj f <-> surj f.
Admitted.


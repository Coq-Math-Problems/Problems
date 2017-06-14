Definition streamless(X : Set) := forall f : nat -> X, 
  {i : nat & {j : nat & i <> j /\ f i = f j}}.

Theorem streamless_sum : forall X Y, streamless X -> streamless Y -> streamless (X + Y).
Admitted.

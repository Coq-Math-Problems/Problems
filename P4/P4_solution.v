Set Implicit Arguments.

Definition AC{X Y}(P : X -> Y -> Prop) :
  (forall x, {y : Y & P x y}) -> {f : X -> Y & forall x, P x (f x)}.
Proof.
  intro.
  exists (fun x => projT1 (X0 x)).
  intro.
  destruct (X0 x); simpl.
  exact p.
Qed.

Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.

Lemma inr_inj{X Y} : inj (@inr X Y).
Proof.
  intros x x' H.
  inversion H.
  reflexivity.
Qed.

Fixpoint Fin(n : nat) : Set :=
  match n with
  |0   => Empty_set
  |S m => unit + Fin m
  end.

Lemma Fin_dec_eq : forall (n : nat)(i j : Fin n), {i = j} + {i <> j}.
Proof.
  induction n; intros.
  destruct i.
  destruct i as [[]|i], j as [[]|j].
  left; reflexivity.
  right; discriminate.
  right; discriminate.
  destruct (IHn i j).
  left; rewrite e; reflexivity.
  right; intro; apply n0.
  inversion H; reflexivity.
Qed.

Definition transpose(n : nat)(i j : Fin n) : Fin n -> Fin n :=
  fun x => match Fin_dec_eq n i x with
           |left  _ => j
           |right _ => match Fin_dec_eq n j x with
                       |left  _ => i
                       |right _ => x
                       end
           end.

Lemma transpose_inj(n : nat) : forall i j, inj (transpose n i j).
Proof.
  unfold transpose.
  intros i j x x' H.
  destruct (Fin_dec_eq n i x).
  destruct (Fin_dec_eq n i x').
  transitivity i; auto.
  destruct (Fin_dec_eq n j x').
  rewrite <- H in n0; contradiction.
  contradiction.
  destruct (Fin_dec_eq n j x).
  destruct (Fin_dec_eq n i x').
  rewrite H in n0; contradiction.
  destruct (Fin_dec_eq n j x').
  rewrite <- e; exact e0.
  contradiction.
  destruct (Fin_dec_eq n i x').
  symmetry in H; contradiction.
  destruct (Fin_dec_eq n j x').
  symmetry in H; contradiction.
  exact H.
Qed.

Lemma transpose_correct(n : nat) : forall i j x : Fin n, transpose n i j x = j -> i = x.
Proof.
  unfold transpose; intros.
  destruct (Fin_dec_eq n i x).
  exact e.
  destruct (Fin_dec_eq n j x).
  transitivity j; auto.
  symmetry in H; contradiction.
Qed.

Theorem inj_to_surj(n : nat) : forall f : Fin n -> Fin n, inj f -> surj f.
Proof.
  induction n; intros f finj.
  intro y; destruct y.
  assert (forall x, {y : Fin n & transpose (S n) (f (inl tt)) (inl tt) (f (inr x)) = inr y}).
  intro.
  destruct (transpose (S n) (f (inl tt)) (inl tt) (f (inr x))) as [[]|y] eqn:G.
  pose (transpose_correct _ _ _ G).
  absurd (inl tt = inr x).
  discriminate.
  exact (finj _ _ e).
  exists y; reflexivity.
  destruct (AC _ H) as [fhat Hf].
  assert (inj fhat).
  intros x x' Hxx'.
  apply (@inr_inj unit).
  apply finj.
  apply (transpose_inj _ (f (inl tt)) (inl tt)).
  rewrite Hf; rewrite Hf.
  rewrite Hxx'; reflexivity.
  intro y.
  destruct (Fin_dec_eq (S n) (f (inl tt)) y).
  exists (inl tt); exact e.
  destruct (transpose _ (f (inl tt)) (inl tt) y) as [[]|y0] eqn:G.
  pose (transpose_correct _ _ _ G).
  contradiction.
  destruct (IHn _ H0 y0).
  exists (inr x).
  unfold transpose in G.
  rewrite <- e in G.
  rewrite <- Hf in G.
  destruct (Fin_dec_eq _ (f (inl tt)) y).
  contradiction.
  destruct (Fin_dec_eq (S n) (inl tt) y).
  unfold transpose in G.
  destruct (Fin_dec_eq (S n) (f (inl tt)) (f (inr x))).
  absurd (inl tt = inr x).
  discriminate.
  exact (finj _ _ e1).
  destruct (Fin_dec_eq (S n) (inl tt) (f (inr x))).
  rewrite <- e1; exact e0.
  contradiction.
  unfold transpose in G.
  destruct (Fin_dec_eq (S n) (f (inl tt)) (f (inr x))).
  symmetry in G; contradiction.
  destruct (Fin_dec_eq (S n) (inl tt) (f (inr x))).
  symmetry in G; contradiction.
  symmetry in G; auto.
Qed.

Lemma no_surj_n_Sn : forall (n : nat)(f : Fin n -> Fin (S n)), surj f -> False.
Proof.
  induction n; intros.
  destruct (X (inl tt)).
  destruct x.
  destruct (f (inl tt)) as [[]|x] eqn:G.
  pose (g := fun x => match f (inr x) with
                      |inl _ => inl tt
                      |inr y => y
                      end).
  apply (IHn g).
  intro y.
  destruct (X (inr y)).
  destruct x as [[]|x].
  rewrite e in G; discriminate G.
  exists x.
  unfold g.
  rewrite e.
  reflexivity.
  pose (g := fun z => match f (inr z) with
                      |inl _ => x
                      |inr y => y
                      end).
  apply (IHn g).
  intro y.
  destruct (X (inr y)).
  destruct x0 as [[]|x0].
  destruct (X (inl tt)).
  destruct x0 as [[]|x0].
  rewrite e0 in e; discriminate e.
  exists x0.
  unfold g.
  rewrite e0.
  rewrite e in G; inversion G; reflexivity.
  exists x0.
  unfold g.
  rewrite e.
  reflexivity.
Qed.

Lemma surj_to_inj(n : nat) : forall f : Fin n -> Fin n, surj f -> inj f.
Proof.
  intros f fsurj x x' H.
  destruct n.
  destruct x.
  destruct (Fin_dec_eq _ x x').
  exact e.
  destruct x as [[]|x].
  destruct x' as [[]|x'].
  elim n0; reflexivity.
  pose (g := fun x => f (inr x)).
  assert (surj g).
  unfold g.
  intro y.
  destruct (fsurj y) as [[[]|x] fx].
  exists x'.
  rewrite <- H; exact fx.
  exists x; exact fx.
  destruct (no_surj_n_Sn X).
  destruct x' as [[]|x'].
  pose (g := fun x => f (inr x)).
  assert (surj g).
  unfold g.
  intro y.
  destruct (fsurj y) as [[[]|x'] fx'].
  exists x; rewrite <- fx'; exact H.
  exists x'; exact fx'.
  destruct (no_surj_n_Sn X).
  pose (g := fun z => match Fin_dec_eq _ z x' with
                      |left _  => f (inl tt)
                      |right _ => f (inr z)
                      end).
  assert (surj g).
  intro y.
  unfold g.
  destruct (Fin_dec_eq _ (f (inl tt)) y).
  exists x'.
  destruct (Fin_dec_eq n x' x').
  exact e.
  elim n1; reflexivity.
  destruct (fsurj y) as [[[]|x''] fx''].
  contradiction.
  destruct (Fin_dec_eq _ x'' x').
  exists x.
  destruct (Fin_dec_eq n x x').
  elim n0; rewrite e0; reflexivity.
  rewrite H; rewrite  <- e; exact fx''.
  exists x''.
  destruct (Fin_dec_eq n x'' x').
  contradiction.
  exact fx''.
  destruct (no_surj_n_Sn X).
Qed.

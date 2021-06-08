From LF Require Export Basics.

Theorem plus_n_O : forall n : nat,
    n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n : nat,
    minus n n = 0.
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_O_r : forall n : nat,
    n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite plus_n_Sm. reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n : nat,
    double n = n + n.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> plus_n_Sm. reflexivity. Qed.

Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl.
    rewrite -> negb_involutive. reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H : 0 + n = n).
  { reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : m + n = n + m).
  { rewrite -> plus_comm. reflexivity. }
  rewrite <- H. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H : n + p = p + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  rewrite -> plus_comm.
  rewrite -> plus_assoc.
  reflexivity. Qed.

Lemma mult_destruct_r : forall n k : nat,
    n * (S k) = n + n * k.
Proof.
  intros n k. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> plus_swap. reflexivity. Qed.
    
Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
  intros m n. induction n as [| n' IHn'].
  - simpl. rewrite -> mult_O_r. reflexivity.
  - simpl. rewrite -> mult_destruct_r.
    rewrite -> IHn'. reflexivity. Qed.

Check leb.

Theorem leb_refl : forall n : nat,
    true = (n <=? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem zero_nbeq_S : forall n : nat,
    0 =? (S n) = false.
Proof.
  intros n. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
    andb b false = false.
Proof.
  intros [|].
  - reflexivity.
  - reflexivity. Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
    n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p. intros H. induction p as [| p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity. Qed.

Theorem S_nbeq_0 : forall n : nat,
    (S n) =? 0 = false.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_1_l : forall n : nat,
    1 * n = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> mult_comm. simpl.
    rewrite -> mult_comm. rewrite -> IHn'.
    reflexivity. Qed.

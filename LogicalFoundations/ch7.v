Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (E : ev n) : ev (S (S n)).

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS (E : wrong_ev n) : wrong_ev (S (S n)).

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl. apply ev_SS. apply ev_SS.
  apply H. Qed.

Theorem ev_plus4' : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. apply (ev_SS (S (S n)) (ev_SS n H)). Qed.

Theorem ev_double : forall n, ev (double n).
Proof.
  induction n as [| n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'. Qed.

Theorem ev_inversion :
  forall n : nat, ev n ->
           n = 0 \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split.
    + reflexivity.
    + apply E'. Qed.

Theorem ev_minus2 : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E. destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    simpl. apply ev_0.
  - (* E = ev_SS n' E' *)
    simpl. apply E'. Qed.

Theorem evSS_ev_remember : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as k eqn:Heqk.
  destruct E as [| n' E'] eqn:EE.
  - discriminate Heqk.
  - injection Heqk as Heq. rewrite <- Heq.
    apply E'. Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H.
  destruct H as [contra | H].
  - discriminate contra.
  - destruct H as [n' [Heq H]].
    injection Heq as Heq. rewrite Heq.
    apply H. Qed.

Theorem evSS_ev' : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  apply E'. Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intro H. apply ev_inversion in H.
  destruct H as [| [n [Hn _]]].
  - discriminate H.
  - discriminate Hn. Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intro H. inversion H. Qed.

Theorem SSSSev__even :
  forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. apply evSS_ev. apply evSS_ev.
  apply E. Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intro H. apply evSS_ev in H. apply evSS_ev in H.
  apply one_not_even in H. destruct H. Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall n : nat,
    S n = O ->
    2 + 2 = 5.
Proof.
  intros n H. inversion H. Qed.

Lemma ev_Even_firsttry : forall n : nat,
    ev n -> Even n.
Proof.
  unfold Even. intros n E.
  inversion E as [EQn | n' E' EQn].
  - (* n = 0 *) exists 0. reflexivity.
  - (* n = S (S n') *)
    assert (H: (exists k', n' = double k') -> (exists n0, S (S n') = double n0)).
    { intros [k' EQn']. exists (S k'). rewrite EQn'. reflexivity. }
    apply H. generalize dependent E'.
Abort. (* Fails because the second case is the same as the original statement. *)

Lemma ev_Even : forall n : nat,
    ev n -> Even n.
Proof.
  unfold Even. intros n E.
  induction E as [| n' E' IH].
  - (* n = 0 *) exists 0. reflexivity.
  - (* n = S (S n') *) destruct IH as [n EQn]. exists (S n).
    rewrite EQn. reflexivity. Qed.

Theorem ev_Even_iff : forall n : nat,
    ev n <-> Even n.
Proof.
  split.
  - apply ev_Even.
  - intros [k EQn]. rewrite EQn.
    generalize dependent n. induction k as [| k' IHk'].
    + intros n H. apply ev_0.
    + intros n H. simpl. apply ev_SS. apply (IHk' (pred (pred n))).
      rewrite H. reflexivity. Qed.

Theorem ev_Even_iff' : forall n : nat,
    ev n <-> Even n.
Proof.
  split.
  - apply ev_Even.
  - intros [k EQn]. rewrite EQn. apply ev_double. Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em. induction En as [| n' En' IH].
  - (* n = 0 *) simpl. apply Em.
  - (* n = S (S n') *) simpl. apply ev_SS. apply IH. Qed.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  split.
  - intro E. induction E as [| | n' m En' IHn' Em IHm].
    + (* n = 0 *) apply ev_0.
    + (* n = 2 *) apply ev_SS. apply ev_0.
    + (* n = n' + m *) apply ev_sum. apply IHn'. apply IHm.
  - intro E. induction E as [| n' En' IH].
    + (* n = 0 *) apply ev'_0.
    + (* n = S (S n') *) replace (S (S n')) with (2 + n').
      * apply ev'_sum. apply ev'_2. apply IH.
      * reflexivity. Qed.

Theorem ev_ev__ev : forall n m,
    ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Enm En. induction En as [| n' E' IH].
  - (* n = 0 *) simpl in Enm. apply Enm.
  - (* n = S (S n') *) simpl in Enm. apply evSS_ev in Enm.
    apply IH. apply Enm. Qed.

Theorem ev_plus_plus : forall n m p : nat,
    ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  assert (H: ev ((n + m) + (n + p))).
  { apply ev'_ev. apply ev'_sum.
    - rewrite ev'_ev. apply Hnm.
    - rewrite ev'_ev. apply Hnp. }
  rewrite add_assoc in H. rewrite (add_comm (n + m)) in H.
  rewrite add_assoc in H. rewrite <- (add_assoc (n + n) m p) in H.
  apply (ev_ev__ev (n + n) (m + p)) in H. apply H.
  rewrite <- double_plus. apply ev_double. Qed.

Module Playground.
  Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

  Notation "n <= m" := (le n m).

  Example test_le1 :
    3 <= 3.
  Proof.
    apply le_n. Qed.

  Example test_le2 :
    3 <= 6.
  Proof.
    apply le_S. apply le_S. apply le_S. apply le_n. Qed.

  Example test_le3 :
    (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intro H. inversion H. inversion H2. Qed.

  Definition lt (n m : nat) := le (S n) m.

  Notation "n < m" := (lt n m).
End Playground.

Inductive square_of : nat -> nat -> Prop :=
| sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
| ne_1 n (H: ev (S n)) : next_ev n (S n)
| ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
| tr_n_m (n m : nat) : total_relation n m.

Example test_tr : total_relation 4 9.
Proof. apply tr_n_m. Qed.

Inductive empty_relation : nat -> nat -> Prop :=.

Lemma le_trans : forall m n o,
    m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2.
  induction H2 as [| o' H IH].
  - (* o = n *) apply H1.
  - (* o = S o' *) apply le_S. apply IH. Qed.

Theorem O_le_n : forall n,
    0 <= n.
Proof.
  induction n as [| n' IHn'].
  - apply le_n.
  - apply le_S. apply IHn'. Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
    n <= m -> S n <= S m.
Proof.
  intros n m H. induction H as [| m' H IH].
  - apply le_n.
  - apply le_S. apply IH. Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
    S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply (le_trans n (S n) m).
    + apply le_S. apply le_n.
    + apply H1. Qed.

Theorem lt_ge_cases : forall n m,
    n < m \/ n >= m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m' IH].
  - right. apply O_le_n.
  - destruct n as [| n'].
    + left. unfold lt. apply n_le_m__Sn_le_Sm, O_le_n.
    + destruct (IH n').
      * (* n' < m' *) left. apply n_le_m__Sn_le_Sm, H.
      * (* n' >= m' *) right. apply n_le_m__Sn_le_Sm, H. Qed.

Theorem le_plus_l : forall a b,
    a <= a + b.
Proof.
  intros a b. induction b as [| b' IH].
  - rewrite add_0_r. apply le_n.
  - rewrite <- plus_n_Sm. apply le_S. apply IH. Qed.

Theorem plus_le : forall n1 n2 m,
    n1 + n2 <= m ->
    n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H. split.
  - apply (le_trans n1 (n1 + n2) m).
    + apply le_plus_l.
    + apply H.
  - rewrite add_comm in H.
    apply (le_trans n2 (n2 + n1) m).
    + apply le_plus_l.
    + apply H. Qed.

(* Hint: the next one may be easiest to prove by induction on n. *)
Theorem add_le_cases_firsttry : forall n m p q,
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n m p q. destruct (lt_ge_cases n p).
  - intro H1. left. unfold lt in H. apply (le_trans n (S n) p).
    + apply le_S, le_n.
    + apply H.
  - destruct (lt_ge_cases m q).
    + intro H1. right. unfold lt in H0. apply (le_trans m (S m) q).
      * apply le_S, le_n.
      * apply H0.
    + intro H1. inversion H; inversion H0.
      * auto.
      * auto.
      * auto.
      *
Abort.

Theorem add_le_cases : forall n m p q,
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
  induction n as [| n' IH].
  - intros m p q H. left. apply O_le_n.
  - intros m p q H. Admitted.

Theorem plus_le_compat_l : forall n m p,
    n <= m ->
    p + n <= p + m.
Proof.
  intros n m p H. induction p as [| p' IH].
  - apply H.
  - simpl. apply n_le_m__Sn_le_Sm. apply IH. Qed.

Theorem plus_le_compat_r : forall n m p,
    n <= m ->
    n + p <= m + p.
Proof.
  intros n m p. rewrite (add_comm n p), (add_comm m p).
  exact (plus_le_compat_l n m p). Qed.

Theorem le_plus_trans : forall n m p,
    n <= m ->
    n <= m + p.
Proof.
  intros n m p H. apply (le_trans n m (m + p)).
  - apply H.
  - apply le_plus_l. Qed.

Theorem n_lt_m__n_le_m : forall n m,
    n < m ->
    n <= m.
Proof.
  intros n m H. unfold lt in H. apply (le_trans n (S n) m).
  - apply le_S, le_n.
  - apply H. Qed.

Theorem plus_lt : forall n1 n2 m,
    n1 + n2 < m ->
    n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m. unfold lt. assert (HS: S (n1 + n2) = S n1 + n2).
  { reflexivity. } rewrite HS. destruct m as [| m'] eqn:EQm.
  - simpl. intro H. inversion H.
  - simpl. intro H. apply Sn_le_Sm__n_le_m in H.
    split.
    + apply n_le_m__Sn_le_Sm. apply (plus_le n2).
      rewrite add_comm. apply H.
    + apply n_le_m__Sn_le_Sm. apply (plus_le n1).
      apply H. Qed.

Theorem leb_complete : forall n m,
    n <=? m = true -> n <= m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m' IH].
  - destruct n as [| n'].
    + intro H. apply le_n.
    + intro H. discriminate H.
  - destruct n as [| n'].
    + intro H. apply O_le_n.
    + simpl. intro H. apply n_le_m__Sn_le_Sm.
      apply IH, H. Qed.

(* Hint: The next one may be easiest to prove by induction on m. *)
Theorem leb_correct : forall n m,
    n <= m ->
    n <=? m = true.
Proof.
  intros n m H. generalize dependent n.
  induction m as [| m' IH].
  - (* m = 0 *) destruct n as [| n'].
    + intro H. reflexivity.
    + intro H. inversion H.
  - (* m = S m' *) intros n H. destruct n as [| n'].
    + reflexivity.
    + simpl. apply IH. apply Sn_le_Sm__n_le_m, H. Qed.

(* Hint: The next one can easily be proved without using induction. *)
Theorem leb_true_trans : forall n m o,
    n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o Hnm Hmo. apply leb_complete in Hnm, Hmo.
  apply leb_correct. apply (le_trans n m o); trivial. Qed.

Theorem leb_iff : forall n m,
    n <=? m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct. Qed.

Module R.
  Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o) : R (S m) n (S o)
  | c3 m n o (H : R m n o) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o) : R n m o.

  Definition fR : nat -> nat -> nat :=
    fun m n => m + n.

  (* The next one is my first try, used so many rewriting
     that I can't remember anything after proving. *)
  Theorem R_equiv_fR_firsttry : forall m n o, R m n o <-> fR m n = o.
  Proof.
    unfold fR. intros m n o. split.
    - intro E. induction E.
      + reflexivity.
      + simpl. rewrite IHE. reflexivity.
      + rewrite add_comm. rewrite <- IHE. simpl.
        rewrite add_comm. reflexivity.
      + simpl in IHE. rewrite <- plus_n_Sm in IHE.
        injection IHE as H. apply H.
      + rewrite add_comm. apply IHE.
    - intro E. rewrite <- E.
      generalize dependent o. generalize dependent n.
      induction m as [| m' IHm].
      + induction n as [| n' IHn].
        * intros o H. apply c1.
        * simpl. simpl in IHn. intros o H. apply c3.
          apply (IHn (pred o)). rewrite <- H. reflexivity.
      + induction n as [| n' IHn].
        * rewrite add_0_r. intros o H. apply c2.
          assert (Hm': R m' 0 m' <-> R m' 0 (m' + 0)).
          { rewrite add_0_r. reflexivity. } rewrite Hm'.
          apply (IHm 0 m'). rewrite add_0_r. reflexivity.
        * intros o H. simpl. apply c3. assert (Hmn: m' + S n' = S m' + n').
          { rewrite <- plus_n_Sm. reflexivity. } rewrite Hmn.
          apply (IHn (pred o)). rewrite <- H. simpl. rewrite Hmn.
          reflexivity. Qed.

  (* This one is much better. *)
  Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
  Proof.
    unfold fR. intros m n o. split.
    - intro E. induction E.
      + reflexivity.
      + simpl. rewrite IHE. reflexivity.
      + rewrite add_comm. rewrite <- IHE. simpl.
        rewrite add_comm. reflexivity.
      + simpl in IHE. rewrite <- plus_n_Sm in IHE.
        injection IHE as H. apply H.
      + rewrite add_comm. apply IHE.
    - generalize dependent o.
      induction m as [| m' IHm]; induction n as [| n' IHn].
      + intros o H. rewrite <- H. apply c1.
      + intros o H. rewrite <- H. apply c3, IHn. reflexivity.
      + intros o H. rewrite <- H. rewrite add_0_r. apply c2, IHm. apply add_0_r.
      + intros o H. rewrite <- H. simpl. apply c2, IHm. reflexivity. Qed.
End R.

Inductive subseq : list nat -> list nat -> Prop :=
| ss_E (x : list nat) : subseq [] x  (* empty sequence *)
| ss_H h (x y : list nat) (H: subseq x y) : subseq (h :: x) (h :: y)  (* equal heads *)
| ss_I h (x y : list nat) (H: subseq x y) : subseq x (h :: y).  (* irrelevant head *)

Theorem subseq_refl : forall l : list nat, subseq l l.
Proof.
  induction l as [| h t IH].
  - apply ss_E.
  - apply ss_H, IH. Qed.

Theorem subseq_app : forall l1 l2 l3 : list nat,
    subseq l1 l2 ->
    subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 E. generalize dependent l3.
  induction E as [| h x y E IH | h x y E IH].
  - intro l3. apply ss_E.
  - intro l3. simpl. apply ss_H, IH.
  - intro l3. simpl. apply ss_I, IH. Qed.

Theorem subseq_trans : forall l1 l2 l3 : list nat,
    subseq l1 l2 ->
    subseq l2 l3 ->
    subseq l1 l3.
Proof.
  intros l1 l2 l3 H12 H23. generalize dependent l1.
  induction H23 as [x | h x y E IH | h x y E IH].
  - intros l1 E. inversion E. apply ss_E.
  - intros l1 E1. inversion E1.
    + (* l1 = [] *) apply ss_E.
    + (* l1 = h :: x0 *) apply ss_H. apply IH. apply H1.
    + apply ss_I. apply IH. apply H1.
  - intros l1 E1. apply ss_I. apply IH. apply E1. Qed.

Inductive nostutter {X : Type} : list X -> Prop :=
| NS0 : nostutter []
| NS1 h : nostutter [h]
| NSCons x h l (H1 : x <> h) (H2 : nostutter (h :: l)) : nostutter (x :: h :: l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto. Qed.

Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; auto. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
           h: nostutter _ |- _ => inversion h; clear h; subst
         end.
  contradiction; auto. Qed.

Inductive in_order_merge {X} : list X -> list X -> list X -> Prop :=
| IOM0 : in_order_merge [] [] []
| IOMH1 h l1 l2 l (H : in_order_merge l1 l2 l) :
    in_order_merge (h :: l1) l2 (h :: l)
| IOMH2 h l1 l2 l (H : in_order_merge l1 l2 l) :
    in_order_merge l1 (h :: l2) (h :: l).

Theorem filter_challenge : forall X (l1 l2 l : list X) (test : X -> bool),
    in_order_merge l1 l2 l ->
    (forall x1, In x1 l1 -> test x1 = true) ->
    (forall x2, In x2 l2 -> test x2 = false) ->
    filter test l = l1.
Proof.
  intros X l1 l2 l test HIOM Hl1 Hl2. induction HIOM.
  - (* IOM0 *) reflexivity.
  - (* IOMH1 *) simpl. rewrite Hl1.
    + f_equal. apply IHHIOM.
      * intros x1 H. apply Hl1. simpl. right. apply H.
      * apply Hl2.
    + simpl. left. reflexivity.
  - (* IOMH2 *) simpl. rewrite Hl2.
    + apply IHHIOM.
      * apply Hl1.
      * intros x2 H. apply Hl2. simpl. right. apply H.
    + simpl. left. reflexivity.
Qed.

Theorem filter_challenge2 : True.
Proof. Admitted.

Lemma the_second_induction_principle : forall P : nat -> Prop,
    (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof.
  intros P H n. apply H. induction n as [| n' IHn'].
  - intros m Hm. inversion Hm.
  - intros m Hm. inversion Hm.
    + apply H. apply IHn'.
    + apply IHn'. apply H1. Qed.

Lemma nat_induction : forall P : nat -> Prop,
    P 0 -> P 1 ->
    (forall n, P n -> P (S (S n))) ->
    forall n, P n.
Proof.
  intros P H0 H1 H. apply the_second_induction_principle.
  intros n Hsec. induction n as [| n' IHn'].
  - apply H0.
  - destruct n' as [| n''].
    + apply H1.
    + apply H. apply Hsec. apply le_S. apply le_n. Qed.

Lemma list_length_0 : forall X (l : list X),
    length l = 0 <-> l = [].
Proof.
  intros X l. split.
  - intro H. destruct l as [| h l'].
    + reflexivity.
    + discriminate H.
  - intro H. rewrite H. reflexivity. Qed.

Lemma list_length_1 : forall X (l : list X),
    length l = 1 <-> exists x, l = [x].
Proof.
  intros X l. split.
  - intro H. induction l as [| h l' IHl'].
    + discriminate H.
    + exists h. simpl in H. injection H as H.
      apply list_length_0 in H.
      rewrite H. reflexivity.
  - intro H. destruct H as [x H].
    rewrite H. reflexivity. Qed.

Lemma cons_app : forall X x (l1 l2 : list X),
    x :: l1 ++ l2 = (x :: l1) ++ l2.
Proof. reflexivity. Qed.

Lemma same_length : forall X (l1 l2 : list X),
    l1 = l2 -> length l1 = length l2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma app_one_length : forall X x (l : list X),
    length (l ++ [x]) = S (length l).
Proof.
  intros X x l. induction l as [| h l' IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH. Qed.

Lemma app_one : forall X x1 x2 (l1 l2 : list X),
    l1 ++ [x1] = l2 ++ [x2] <-> l1 = l2 /\ x1 = x2.
Proof.
  intros X x1 x2 l1 l2. split.
  - intro H. generalize dependent l2.
    induction l1 as [| h1 l1' IHl1'].
    + destruct l2 as [| h2 l2'].
      * intro H. simpl in H. inversion H. split; trivial.
      * intro H. simpl in H. inversion H. apply same_length in H2.
        rewrite app_one_length in H2. discriminate H2.
    + destruct l2 as [| h2 l2'].
      * intro H. simpl in H. apply same_length in H.
        rewrite cons_app in H. simpl in H. rewrite app_one_length in H.
        injection H as H. discriminate H.
      * intro H. simpl in H. injection H. intros H1 H2.
        destruct (IHl1' l2' H1). split.
        -- f_equal; trivial.
        -- apply H3.
  - intros [H1 H2]. rewrite H1. rewrite H2. reflexivity. Qed.

Lemma rev_empty : forall X (l : list X),
    rev l = [] <-> l = [].
Proof.
  intros X l. split.
  - induction l as [| h l' IHl'].
    + trivial.
    + simpl. intro H. apply same_length in H.
      rewrite app_one_length in H. discriminate H.
  - intro H. rewrite H. reflexivity. Qed.

Lemma rev_length : forall X (l : list X),
    length l = length (rev l).
Proof.
  intros X l. induction l as [| h l' IHl'].
  - trivial.
  - simpl. rewrite app_one_length. f_equal. apply IHl'. Qed.

Theorem rev_injective : forall X (l1 l2 : list X),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H. assert (H0 : rev (rev l1) = l1).
  { rewrite rev_involutive. reflexivity. }
  rewrite <- H0. rewrite H. rewrite rev_involutive.
  reflexivity. Qed.

Lemma list_split_head : forall X (l : list X) n,
    length l = S n ->
    exists x l', length l' = n /\ l = x :: l'.
Proof.
  intros. generalize dependent l. induction n as [| n' IHn'].
  - intros l H. apply list_length_1 in H. destruct H as [x H].
    exists x. exists []. split; trivial.
  - intros l H. destruct l as [| h l'].
    + discriminate H.
    + simpl in H. injection H as H. exists h. exists l'. split; trivial. Qed.

Lemma list_split_tail : forall X (l : list X) n,
    length l = S n ->
    exists x l', length l' = n /\ l = l' ++ [x].
Proof.
  intros. generalize dependent l. induction n as [| n' IHn'].
  - intros l H. apply list_length_1 in H. destruct H as [x H].
    exists x. exists []. rewrite H. split; trivial.
  - intros l H. remember (rev l) as l__r. destruct l__r as [| h l__r'].
    + symmetry in Heql__r. rewrite rev_empty in Heql__r.
      rewrite Heql__r in H. discriminate H.
    + exists h. exists (rev l__r'). split.
      * symmetry in H. rewrite rev_length in H.
        rewrite <- Heql__r in H. injection H as H.
        rewrite <- rev_length. symmetry. apply H.
      * rewrite <- (rev_involutive _ (h :: l__r')) in Heql__r.
        apply rev_injective in Heql__r. rewrite <- Heql__r.
        reflexivity. Qed.

Lemma list_split : forall X (l : list X) n,
    length l = S (S n) ->
    exists x1 x2 l', length l' = n /\ l = x1 :: l' ++ [x2].
Proof.
  intros X l n H. apply list_split_head in H.
  destruct H as [x1 [l' [H Hl]]]. apply list_split_tail in H.
  destruct H as [x2 [l'' [H Hl']]]. rewrite Hl' in Hl.
  exists x1. exists x2. exists l''. split; trivial. Qed.

(* Put lists of the same length into the same group. Treat the
   groups of lists as natural numbers and does induction. *)
Lemma list_induction_on_length : forall X (P : list X -> Prop),
    (forall n l, length l = n -> P l) -> forall l, P l.
Proof.
  intros X P H. intro l. apply (H (length l)). reflexivity. Qed.

Lemma list_induction : forall X (P : list X -> Prop),
    P [] -> (forall x, P [x]) ->
    (forall x1 x2 l, P l -> P (x1 :: l ++ [x2])) ->
    forall l, P l.
Proof.
  intros X P H0 H1 IH. apply list_induction_on_length. intro n.
  apply (nat_induction (fun n => forall l, length l = n -> P l)) with (n:=n).
  - (* P 0 *) intros H Hlen. rewrite list_length_0 in Hlen.
    rewrite Hlen. apply H0.
  - (* P 1 *) intros H Hlen. rewrite list_length_1 in Hlen.
    destruct Hlen as [x Hlen]. rewrite Hlen. apply H1.
  - (* P n → P (S (S n)) *) intros n' H3 l H4. apply list_split in H4.
    destruct H4 as [x1 [x2 [l' [H4 H5]]]]. rewrite H5. apply IH.
    apply H3. apply H4. Qed.

Lemma rev_app : forall X x (l : list X),
    rev (l ++ [x]) = x :: rev l.
Proof.
  intros X x l. induction l as [| h l' IH].
  - reflexivity.
  - simpl. rewrite cons_app. rewrite app_one. split.
    + apply IH.
    + reflexivity. Qed.

Inductive pal {X} : list X -> Prop :=
| Pal0 : pal []
| Pal1 x : pal [x]
| PalAdd x p (H : pal p) : pal (x :: p ++ [x]).

Theorem pal_app_rev : forall X (l : list X),
    pal (l ++ rev l).
Proof.
  intros X l. induction l as [| x l' IH].
  - apply Pal0.
  - simpl. rewrite app_assoc. apply PalAdd. apply IH. Qed.

Theorem pal_rev : forall X (l : list X),
    pal l -> l = rev l.
Proof.
  intros X l E. induction E as [| x | x l' E IH].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite rev_app_distr. simpl.
    rewrite <- IH. reflexivity. Qed.

Theorem pal_rev_converse : forall X (l : list X),
    l = rev l -> pal l.
Proof.
  intro X. apply (list_induction _ (fun l => l = rev l -> pal l)).
  - intro H. apply Pal0.
  - intros x H. apply Pal1.
  - intros x1 x2 l IH Hrev. simpl in Hrev. rewrite cons_app in Hrev.
    rewrite app_one in Hrev. destruct Hrev as [Hrev Heq].
    rewrite Heq. apply PalAdd. rewrite rev_app in Hrev.
    rewrite Heq in Hrev. apply IH. inversion Hrev.
    rewrite rev_involutive. symmetry. apply H0. Qed.

Definition disjoint X (l1 l2 : list X) : Prop :=
  forall x, (In x l1 -> ~ In x l2) /\ (In x l2 -> ~ In x l1).

Compute disjoint _ [1;3;5] [2;4;6].

Inductive NoDup X : list X -> Prop :=
| ND0 : NoDup X []
| NDAdd x l (H1 : NoDup X l) (H2 : ~ In x l) : NoDup X (x :: l).

Lemma tail_nodup : forall X h (t : list X),
    NoDup X (h :: t) <-> ~ In h t /\ NoDup X t.
Proof.
  intros X h t. split.
  - intro H. inversion H. split; trivial.
  - intro H. destruct H. apply NDAdd; trivial. Qed.

Lemma tail_disjoint : forall X h t1 l2,
    disjoint X (h :: t1) l2 <->
    ~ In h l2 /\ disjoint X t1 l2.
Proof.
  intros X h t1 l2. split.
  - intros H. split.
    + destruct (H h). apply H0. simpl. left. reflexivity.
    + intro x. destruct (H x). split.
      * intro Ht1. apply H0. right. apply Ht1.
      * intro Hl2. intro Ht1. apply (H1 Hl2). right. apply Ht1.
  - intros [H1 H2]. intro x. destruct (H2 x). split.
    + intro Ht1. simpl in Ht1. inversion Ht1.
      * (* h = x *) rewrite H3 in H1. apply H1.
      * (* In x t1 *) simpl in Ht1. apply (H H3).
    + intros Hl2 Ht1. assert (Hhx: h <> x).
      { intro Ehx. apply H1. rewrite Ehx. apply Hl2. }
      inversion Ht1.
      * apply (Hhx H3).
      * apply (H0 Hl2 H3). Qed.

Theorem app_nodup_preservation : forall X (l1 l2 : list X),
    NoDup X l1 -> NoDup X l2 ->
    disjoint X l1 l2 ->
    NoDup X (l1 ++ l2).
Proof.
  intros X l1 l2 HND1 HND2 HDis.
  induction l1 as [| x l1' IH].
  - apply HND2.
  - simpl. apply NDAdd.
    + rewrite tail_nodup in HND1.
      destruct HND1 as [_ HND1]. apply (IH HND1).
      rewrite tail_disjoint in HDis.
      destruct HDis as [_ HDis]. apply HDis.
    + rewrite tail_disjoint in HDis. inversion HND1.
      destruct HDis as [HDis _]. rewrite In_app_iff.
      intro goal. destruct goal as [goal | goal].
      * apply (H3 goal).
      * apply (HDis goal). Qed.

Lemma in_split : forall X x (l : list X),
    In x l ->
    exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l H. induction l as [| h t IH].
  - destruct H.
  - simpl in H. destruct H as [H | H].
    + exists []. exists t. rewrite H. reflexivity.
    + destruct (IH H) as [l1 [l2 IH']].
      exists (h :: l1). exists l2. simpl. rewrite IH'. reflexivity. Qed.

(* Using ∀ instead of (H : …) makes its meaning clear. *)
Inductive repeats {X} : list X -> Prop :=
| RepAdd : forall x l, In x l -> repeats (x :: l)
| RepPrsv : forall x l, repeats l -> repeats (x :: l).

Theorem pigeonhole_principle_firsttry :
  excluded_middle ->
  forall X (l1 l2 : list X),
    (forall x, In x l1 -> In x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof.
  intros EM X l1. induction l1 as [| x l1' IHl1'].
  - (* l1 = [] *)
    intros l2 _ contra.
    apply Le.le_n_0_eq in contra.
    discriminate contra.
  - (* l1 = x :: l1' *)
    intros l2 Hin Hlen. destruct (EM (In x l1')).
    + (* In x l1' *)
      apply RepAdd. apply H.
    + (* ¬ In x l1' *)
      apply RepPrsv. destruct l2 as [| y l2'] eqn:El2.
      * (* l2 = [] *)
        exfalso. simpl in Hin. apply (Hin x). left. reflexivity.
      * (* l2 = y :: l2' *)
        simpl in Hlen. apply Lt.lt_S_n in Hlen.
        generalize dependent Hlen. apply IHl1'.
        (* Lacks evidence, cannot go further. *)
Abort.

Theorem pigeonhole_principle :
  excluded_middle ->
  forall X (l1 l2 : list X),
    (forall x, In x l1 -> In x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof.
  intros EM X. induction l1 as [| x l1' IHl1'].
  - (* l1 = [] *) intros l2 _ contra. inversion contra.
  - (* l1 = h :: l1' *) intros l2 Hin Hlen. destruct (EM (In x l1')).
    + (* In x l1' *) apply RepAdd. apply H.
    + (* ¬ In x l1' *) Admitted.

(* UNFINISHED: add_le_cases filter_challenge2 pigeonhole_principle *)

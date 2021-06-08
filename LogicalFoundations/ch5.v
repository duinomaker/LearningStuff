From LF Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
    n = m ->
    (n = m -> [n;o] = [m;p]) ->
    [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
    (n,n) = (m,m) ->
    (forall (p q : nat), (p,p) = (q,q) -> [p] = [q]) ->
    [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex :
  (forall n : nat, evenb n = true -> oddb (S n) = false) ->
  evenb 2 = true ->
  oddb 3 = true.
Proof.
  intros eq1 eq2. apply eq2. Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H. symmetry. apply H. Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
    rev l = l' ->
    rev l' = l.
Proof.
  intros l l' H. rewrite <- H.
  apply rev_involutive. Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite eq1. rewrite eq2. reflexivity. Qed.

Theorem trans_eq : forall (X : Type) (a b c : X),
    a = b -> b = c -> a = c.
Proof.
  intros X a b c eq1 eq2.
  rewrite eq1. rewrite eq2. reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. apply trans_eq with (b:=[c;d]).
  apply eq1. apply eq2. Qed.

Theorem S_injective : forall (n m : nat),
    S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)).
  { reflexivity. }
  rewrite H2. rewrite H1. reflexivity. Qed.

Theorem S_injective' : forall (n m : nat),
    S n = S m -> n = m.
Proof.
  intros n m H. injection H as Hnm.
  apply Hnm. Qed.

Theorem injection_ex1 : forall (n m o : nat),
    [n; m] = [o; o] ->
    [n] = [m].
Proof.
  intros n m o H. injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity. Qed.

Theorem injection_ex2 : forall (n m o : nat),
    [n ; m] = [o; o] ->
    [n] = [m].
Proof.
  intros n m o H. injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity. Qed.

Theorem injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    j = z :: l ->
    x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H1 as H3 H4. rewrite H3.
  assert (H5: z :: l = y :: l).
  { rewrite H4. rewrite H2. reflexivity. }
  injection H5 as H6. apply H6. Qed.

Theorem eqb_0_l : forall n,
    0 =? n = true -> n = 0.
Proof.
  intro n. destruct n as [| n'].
  - reflexivity.
  - simpl. intro H. discriminate H. Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n H. discriminate H. Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H. discriminate H. Qed.

Theorem f_equal : forall (X Y : Type) (f : X -> Y) (n m : X),
    n = m -> f n = f m.
Proof.
  intros X Y f n m H. rewrite H. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m H. f_equal. apply H. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
    (S n =? S m) = b ->
    (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n H1 H2. symmetry in H2.
  apply H1 in H2. symmetry. apply H2. Qed.

Theorem double_injective_FAILED : forall (n m : nat),
    double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. intro eq. destruct m as [| m'] eqn:E.
    + (* m = 0 *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl. intro eq. destruct m as [| m'] eqn:E.
    + (* m = 0 *) discriminate eq.
    + (* m = S m' *) f_equal.
Abort.

Theorem double_injective : forall (n m : nat),
    double n = double m -> n = m.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *) simpl. intros m H. destruct m as [| m'] eqn:E.
    + (* m = 0 *) reflexivity.
    + (* m = S m' *) discriminate H.
  - (* n = S n' *) simpl. intros m H. destruct m as [| m'] eqn:E.
    + (* m = 0 *) discriminate H.
    + (* m = S m' *) f_equal. simpl in H. injection H as Hdb.
      apply IHn'. apply Hdb. Qed.

Theorem eqb_true : forall (n m : nat),
    (n =? m) = true -> n = m.
Proof.
  induction n as [| n' IHn'].
  - (* n = 0 *) destruct m as [| m'] eqn:E.
    + reflexivity.
    + intro H. discriminate H.
  - (* n = S n' *) destruct m as [| m'] eqn:E.
    + intro H. discriminate H.
    + intro H. f_equal. apply IHn'.
      simpl in H. apply H. Qed.

Theorem plus_n_n_injective' : forall n m,
    n + n = m + m ->
    n = m.
Proof.
  intros n m.
  assert (Hn: n + n = double n).
  { induction n as [| n' IHn''].
    + reflexivity.
    + simpl. rewrite plus_comm.
      simpl. f_equal. f_equal. apply IHn''. }
  assert (Hm: m + m = double m).
  { induction m as [| m' IHm''].
    + reflexivity.
    + simpl. rewrite plus_comm.
      simpl. f_equal. f_equal. apply IHm''. }
  rewrite Hm. rewrite Hn. apply double_injective. Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m ->
    n = m.
Proof.
  induction n as [| n' IHn'].
  - simpl. intros m H. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate H.
  - simpl. rewrite plus_comm. simpl. intros m H.
    destruct m as [| m'] eqn:E.
    + discriminate H.
    + f_equal. apply IHn'. simpl in H. injection H as H.
      symmetry in H. rewrite plus_comm in H. injection H as H.
      symmetry. apply H. Qed.

Theorem double_injective' : forall (n m : nat),
    double n = double m -> n = m.
Proof.
  intros n m. generalize dependent n.
Abort.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    nth_error l n = None.
Proof.
  intros n X l. generalize dependent n.
  induction l as [| h l' IHl'].
  - (* l = [ ] *) reflexivity.
  - (* l = h :: l' *) intros n H. simpl in H.
    destruct n as [| n'] eqn:E.
    + (* n = 0 *) discriminate H.
    + (* n = S n' *) simpl. apply IHl'.
      injection H as goal. apply goal. Qed.

Definition square (x : nat) := x * x.

Lemma square_mult : forall n m,
    square (n * m) = (square n) * (square m).
Proof.
  intros n m. unfold square. rewrite <- mult_assoc.
  assert (H: m * (n * m) = n * m * m).
  { rewrite mult_comm.  reflexivity. }
  rewrite H. rewrite mult_assoc. rewrite mult_assoc.
  rewrite mult_assoc. reflexivity. Qed.

Definition foo (n : nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intro m. reflexivity. Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intro m. destruct m as [| m'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intro m. unfold bar. destruct m as [| m'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
       else false.

Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.
Proof.
  intro n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - reflexivity.
  - destruct (n =? 5) eqn:E2.
    + reflexivity.
    + reflexivity. Qed.

Fixpoint split {X Y : Type} (l : list (X * Y))
  : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
  end.
Theorem combine_split : forall (X Y : Type) (l : list (X * Y)) l1 l2,
    split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
  induction l as [| (x, y) l' IHl'].
  - (* l = [] *) intros l1 l2 H. simpl in H.
    injection H as H1 H2. rewrite <- H1. rewrite <- H2.
    reflexivity.
  - (* l = (x, y) :: l' *) intros l1 l2 H. simpl in H.
    destruct (split l') eqn:E. injection H as H1 H2.
    rewrite <- H1. rewrite <- H2. simpl. f_equal.
    apply IHl'. reflexivity. Qed.

Definition sillyfun1 (n : nat) : bool :=
    if n =? 3 then true
    else if n =? 5 then true
         else false.

Theorem eqb_true' : forall (n m: nat),
    (n =? m) = true ->
    n = m.
Proof.
  induction n as [| n' IHn'].
  - destruct m as [| m'] eqn:E.
    + reflexivity.
    + intro H. discriminate H.
  - destruct m as [| m'] eqn:E.
    + intro H. discriminate H.
    + intro H. f_equal. apply IHn'.
      simpl in H. apply H. Qed.

Theorem sillyfun1_odd : forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
  intros n H. unfold sillyfun1 in H.
  destruct (n =? 3) eqn:E1.
  - apply eqb_true in E1. rewrite E1. reflexivity.
  - destruct (n =? 5) eqn:E2.
    + apply eqb_true in E2. rewrite E2. reflexivity.
    + (* sillyfun1 n = false *) discriminate H. Qed.

Theorem bool_fn_applied_trice :
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intro f.
  destruct (b) eqn:E1.
  - destruct (f true) eqn:E2.
    + rewrite E2. rewrite E2. reflexivity.
    + destruct (f false) eqn:E3.
      * rewrite E2. reflexivity.
      * rewrite E3. reflexivity.
  - destruct (f true) eqn:E2.
    + destruct (f false) eqn:E3.
      * rewrite E2. rewrite E2. reflexivity.
      * rewrite E3. rewrite E3. reflexivity.
    + destruct (f false) eqn:E3.
      * rewrite E2. rewrite E3. reflexivity.
      * rewrite E3. rewrite E3. reflexivity. Qed.

Theorem eqb_sym : forall (n m : nat),
    (n =? m) = (m =? n).
Proof.
  induction n as [| n' IHn'].
  - destruct m as [| m'] eqn:E.
    + reflexivity.
    + reflexivity.
  - destruct m as [| m'] eqn:E.
    + reflexivity.
    + simpl. apply IHn'. Qed.

Theorem eqb_trans : forall n m p,
    n =? m = true ->
    m =? p = true ->
    n =? p = true.
Proof.
  intros n m p Hnm. apply eqb_true in Hnm.
  rewrite Hnm. intro H. apply H. Qed.

Definition split_combine_statement: Prop
  := forall (X Y : Type) l1 l2 (l : list (X * Y)),
    length l1 = length l2 ->
    combine l1 l2 = l ->
    split l = (l1, l2).

Theorem split_combine: split_combine_statement.
Proof.
  intros X Y. induction l1 as [| x l1' IH].
  - simpl. destruct l2 as [| y l2'] eqn:El2.
    + intros l Hlen H. rewrite <- H. reflexivity.
    + intros l Hlen. discriminate Hlen.
  - destruct l2 as [| y l2'] eqn:El2.
    + intros l Hlen. discriminate Hlen.
    + intros l Hlen. simpl in Hlen. injection Hlen as Hlen.
      apply IH with (l:=combine l1' l2') in Hlen.
      * simpl. intro H. rewrite <- H. simpl.
        destruct (split (combine l1' l2')) eqn:Espl.
        injection Hlen as Hl1 Hl2. rewrite Hl1. rewrite Hl2.
        reflexivity.
      * reflexivity. Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x.
  induction l as [| h t IHt].
  - simpl. intros lf H. discriminate H.
  - simpl. destruct (test h) eqn:Etest.
    + intros lf H. injection H as Hhx.
      rewrite <- Hhx. apply Etest.
    + apply IHt. Qed.

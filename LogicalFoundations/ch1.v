Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example text_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: true || false || false = true.
Proof. simpl. reflexivity. Qed.

Check true : bool.
Check negb : bool -> bool .

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Check primary : rgb -> color.

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Compute (monochrome (primary red)).
Compute (isred (primary red)).

Module Playground.
  Definition b : rgb := blue.
End Playground.

Check Playground.b : rgb.

Module TuplePlayground.
  Inductive bit : Type :=
    | B0
    | B1.

  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

  Check (bits B0 B1 B0 B1)
    : nybble.

  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.

  Compute (all_zero (bits B0 B0 B0 B0)).
End TuplePlayground.

Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

  Check (S (S (S (S O)))).
  Compute (pred (S (S (S O)))).

  Example test_nat1: (pred (S O)) = O.
  Proof. simpl. reflexivity. Qed.
End NatPlayground.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
  Fixpoint plus (m n : nat) : nat :=
    match n with
    | O => m
    | S n' => (plus (S m) n')
    end.

  Compute (plus 2 3).

  Fixpoint mult (m n : nat) : nat :=
    match n with
    | O => O
    | S O => m
    | S n' => plus m (mult m n')
    end.

  Compute (mult 4 7).

  Fixpoint minus (m n : nat) : nat :=
    match m, n with
    | O, _ => O
    | _, O => m
    | S m', S n' => minus m' n'
    end.

  Compute (minus 17 5).
End NatPlayground2.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_fact1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_fact2: (factorial 6) = 720.
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.

Check (1 + 2 * 3) : nat.

Example test_nat_notation1: 1 + 2 * 3 = 7.
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (m n : nat) : bool :=
  match m, n with
  | O, O => true
  | O, _ => false
  | _, O => false
  | S m', S n' => eqb m' n'
  end.

Example test_eqb1: (eqb 10 24) = false.
Proof. simpl. reflexivity. Qed.

Example test_eqb2: (eqb 24 10) = false.
Proof. simpl. reflexivity. Qed.

Example test_eqb3: (eqb 15 15) = true.
Proof. simpl. reflexivity. Qed.

Fixpoint leb (m n : nat) : bool :=
  match m with
  | O => true
  | S m' =>
    match n with
    | O => false
    | S n' => leb m' n'
    end
  end.

Example test_leb1: (leb 10 24) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: (leb 24 10) = false.
Proof. simpl. reflexivity. Qed.

Example test_leb3: (leb 15 15) = true.
Proof. simpl. reflexivity. Qed.

Fixpoint ltb (m n : nat) : bool :=
  match m with
  | O =>
    match n with
    | O => false
    | _ => true
    end
  | S m' =>
    match n with
    | O => false
    | S n' => ltb m' n'
    end
  end.

Example test_ltb1: (ltb 10 24) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 24 10) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 15 15) = false.
Proof. simpl. reflexivity. Qed.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Example test_leb4': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall m n : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros m n.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.

Check plus_O_n.
Check plus_id_exercise.

Theorem mult_n_O_m_O : forall p q : nat,
    (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  rewrite -> plus_O_n.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commute : forall b c,
    andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity. Qed.

Theorem andb_commute2 : forall b c,
    andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity. Qed.

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c. destruct c eqn:Ec.
  - intros H. reflexivity.
  - intros H. rewrite <- H.
    destruct b eqn:Eb.
    + reflexivity.
    + reflexivity. Qed.

Theorem plus_1_neq_0' : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' : forall b c,
    andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

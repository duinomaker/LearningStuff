Require Import Setoid.

(* Natural Numbers *)

Reserved Notation "x =? y" (at level 70).

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => n' =? m'
  | _, _ => false
  end
where "n =? m" := (eqb n m) : nat_scope.

Lemma eq_S : forall n m, n = m <-> S n = S m.
Proof.
  split.
  - intros. rewrite H. reflexivity.
  - intros. injection H as H. apply H. Qed.

Lemma eqb_refl : forall n, n =? n = true.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. apply IH. Qed.

Theorem eqb_eq : forall n m, n =? m = true <-> n = m.
Proof.
  split.
  - generalize dependent m. induction n as [| n' IH].
    + intros m H. destruct m as [| m'].
      * reflexivity.
      * discriminate H.
    + intros m H. destruct m as [| m'].
      * discriminate H.
      * rewrite <- eq_S. simpl in H. apply (IH m' H).
  - intro H. rewrite H. apply eqb_refl. Qed.

Theorem eq_cancel : forall n x y, n + x = n + y <-> x = y.
Proof.
  split.
  - generalize dependent x. generalize dependent y.
    induction n as [| n' IH].
    + intros. apply H.
    + intros. inversion H. apply (IH _ _ H1).
  - intros. rewrite H. reflexivity. Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => S (S (double n'))
  end.

Lemma n_plus_Sm_Sn_plus_m : forall n m, n + S m = S (n + m).
Proof.
  induction n as [| n' IH].
  - intro m. reflexivity.
  - intro m. simpl. rewrite IH. reflexivity. Qed.

Theorem double_destruct : forall n, double n = n + n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite n_plus_Sm_Sn_plus_m.
    rewrite IH. reflexivity. Qed.

Theorem plus_assoc : forall n m o, n + (m + o) = n + m + o.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - intros. assert (H: S n' + (m + o) =  S (n' + (m + o))).
    { reflexivity. } rewrite H. rewrite IH. reflexivity. Qed.

Lemma plus_0 : forall n, n + 0 = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - replace (S n' + 0) with (S (n' + 0)).
    rewrite IH. reflexivity.
    + reflexivity. Qed.

Theorem plus_comm : forall n m, n + m = m + n.
Proof.
  induction n as [| n' IH].
  - intros. rewrite plus_0. reflexivity.
  - intros. rewrite n_plus_Sm_Sn_plus_m.
    rewrite <- IH. reflexivity. Qed.

(* Binary Trees and Lengths *)

Inductive btree (X : Type) : Type :=
| bt_nil
| bt_node (l : btree X) (x : X) (r : btree X).

Arguments bt_nil {X}.
Arguments bt_node {X}.

Notation "{ }" := bt_nil.
Notation "{ l , x , r }" := (bt_node l x r).

Fixpoint internal_length {X} (t : btree X) (h : nat) : nat :=
  match t with
  | {} => 0
  | {l,x,r} => h + (internal_length l (S h)) +
              (internal_length r (S h))
  end.

Fixpoint external_length {X} (t : btree X) (h : nat) : nat :=
  match t with
  | {} => h
  | {l,x,r} => (external_length l (S h)) +
              (external_length r (S h))
  end.

Fixpoint non_leaf_count {X} (t : btree X) : nat :=
  match t with
  | {} => 0
  | {l,x,r} => 1 + (non_leaf_count l) +
              (non_leaf_count r)
  end.

Example test_internal_length1 : internal_length {{},3,{}} 0 = 0.
Proof. reflexivity. Qed.

Example test_external_length1 : external_length {{},3,{}} 0 = 2.
Proof. reflexivity. Qed.

Example test_non_leaf_count1 : non_leaf_count {{},3,{}} = 1.
Proof. reflexivity. Qed.

Example test_internal_length2 :
  internal_length {{{},2,{}},1,{{{},4,{}},3,{}}} 0 = 4.
Proof. reflexivity. Qed.

Example test_external_length2 :
  external_length {{{},2,{}},1,{{{},4,{}},3,{}}} 0 = 12.
Proof. reflexivity. Qed.

Example test_non_leaf_count2 :
  non_leaf_count {{{},2,{}},1,{{{},4,{}},3,{}}} = 4.
Proof. reflexivity. Qed.

(* Lemmas and the Theorem *)

Lemma internal_length_S : forall n X (t : btree X),
    internal_length t n + non_leaf_count t =
    internal_length t (S n).
Proof.
  intros. generalize dependent n.
  induction t as [| l IHl x r IHr].
  - reflexivity.
  - simpl. intro n. rewrite <- plus_assoc. rewrite n_plus_Sm_Sn_plus_m.
    rewrite n_plus_Sm_Sn_plus_m. rewrite <- eq_S. rewrite <- plus_assoc.
    rewrite <- plus_assoc. rewrite eq_cancel. rewrite plus_assoc.
    rewrite plus_assoc.
    replace (internal_length l (S n) + internal_length r (S n) +
             non_leaf_count l + non_leaf_count r) with
        (internal_length l (S n) + non_leaf_count l +
         (internal_length r (S n) + non_leaf_count r)).
    rewrite IHl. rewrite IHr. reflexivity.
    + rewrite plus_assoc.
      replace (internal_length l (S n) + non_leaf_count l +
               internal_length r (S n) + non_leaf_count r) with
          (internal_length l (S n) +
           (non_leaf_count l + internal_length r (S n)) +
           non_leaf_count r).
      rewrite (plus_comm (non_leaf_count l) (internal_length r (S n))).
      rewrite plus_assoc. reflexivity.
      * rewrite plus_assoc. reflexivity. Qed.

Lemma external_length_S : forall n X (t : btree X),
    1 + external_length t n + non_leaf_count t =
    external_length t (S n).
Proof.
  intros. generalize dependent n.
  induction t as [| l IHl x r IHr].
  - intros. rewrite plus_0. reflexivity.
  - intros. simpl in *.
    replace (S (external_length l (S n) + external_length r (S n) +
                S (non_leaf_count l + non_leaf_count r))) with
        (S (external_length l (S n) + non_leaf_count l) +
         S (external_length r (S n) + non_leaf_count r)).
    rewrite IHl. rewrite IHr. reflexivity.
    + simpl. rewrite <- eq_S. rewrite n_plus_Sm_Sn_plus_m.
      rewrite n_plus_Sm_Sn_plus_m. rewrite <- eq_S.
      rewrite <- plus_assoc.
      rewrite (plus_assoc (non_leaf_count l)
                          (external_length r (S n))
                          (non_leaf_count r)).
      rewrite (plus_comm (non_leaf_count l)
                         (external_length r (S n))).
      rewrite plus_assoc. rewrite plus_assoc.
      rewrite plus_assoc. reflexivity. Qed.

(* Too many `rewrite`-s! Can't Coq resolve equalities automatically? *)
Theorem the_theorem : forall X (t : btree X),
    external_length t 0 = internal_length t 0 + double (non_leaf_count t).
Proof.
  induction t as [| l IHl x r IHr].
  - reflexivity.
  - simpl.
    rewrite double_destruct in IHl. rewrite plus_assoc in IHl.
    rewrite (internal_length_S 0) in IHl.
    rewrite double_destruct in IHr. rewrite plus_assoc in IHr.
    rewrite (internal_length_S 0) in IHr.
    replace (internal_length l 1 + internal_length r 1 +
             S (S (double (non_leaf_count l + non_leaf_count r)))) with
        (1 + (internal_length l 1 + non_leaf_count l) + non_leaf_count l +
         (1 + (internal_length r 1 + non_leaf_count r) + non_leaf_count r)).
    rewrite <- IHl. rewrite <- IHr. rewrite (external_length_S 0).
    rewrite (external_length_S 0). reflexivity.
    + simpl. rewrite n_plus_Sm_Sn_plus_m. rewrite n_plus_Sm_Sn_plus_m.
      rewrite n_plus_Sm_Sn_plus_m. rewrite <- eq_S. rewrite <- eq_S.
      rewrite double_destruct. rewrite plus_assoc. rewrite plus_assoc.
      rewrite plus_assoc. rewrite plus_assoc. rewrite plus_assoc.
      assert (H: non_leaf_count l + non_leaf_count l +
                 internal_length r 1 + non_leaf_count r =
                 internal_length r 1 + non_leaf_count l +
                 non_leaf_count r + non_leaf_count l).
      { rewrite <- (plus_assoc (non_leaf_count l)
                              (non_leaf_count l)
                              (internal_length r 1)).
        rewrite (plus_comm (non_leaf_count l) (internal_length r 1)).
        rewrite plus_assoc. rewrite (plus_comm (non_leaf_count l)
                                               (internal_length r 1)).
        rewrite <- (plus_assoc (internal_length r 1 + non_leaf_count l)
                              (non_leaf_count l)
                              (non_leaf_count r)).
        rewrite (plus_comm (non_leaf_count l) (non_leaf_count r)).
        rewrite plus_assoc. reflexivity. }
      assert (H1: internal_length l 1 + non_leaf_count l +
                  non_leaf_count l + internal_length r 1 +
                  non_leaf_count r + non_leaf_count r =
                  internal_length l 1 +
                  (non_leaf_count l +
                   non_leaf_count l + internal_length r 1 +
                   non_leaf_count r) + non_leaf_count r).
      { rewrite plus_assoc. rewrite plus_assoc.
        rewrite plus_assoc. reflexivity. }
      rewrite H1. rewrite H. rewrite plus_assoc. rewrite plus_assoc.
      rewrite plus_assoc. reflexivity. Qed.

Print Assumptions the_theorem.

(* UNUSED Definitions and Lemmas *)

Inductive list (X : Type) : Type :=
| nil
| cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

Notation "[ ]" := nil.
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Fixpoint length {X} (l : list X) : nat :=
  match l with
  | nil => O
  | _ :: l' => S (length l')
  end.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. discriminate. Qed.

Inductive dir : Type :=
| Left
| Right.

(* Say a list of directions "proper," if a leaf node
   is just reached by following the list. *)
Fixpoint ld_proper {X} (t : btree X) (ld : list dir) : bool :=
  match t, ld with
  | {}, [] => true
  | {l,x,r}, h :: ld' =>
    match h with
    | Left => ld_proper l ld'
    | Right => ld_proper r ld'
    end
  | _, _ => false
  end.

Fixpoint extend_leaf {X} (t : btree X) (ld : list dir) (x' : X) : btree X :=
  match t with
  | {} => {{},x',{}}
  | {l,x,r} =>
    match ld with
    | [] => {l,x,r}  (* avoid extending non-leaf nodes *)
    | h :: ld' =>
      match h with
      | Left => {extend_leaf l ld' x',x,r}
      | Right => {l,x,extend_leaf r ld' x'}
      end
    end
  end.

Example test_extend_leaf1 :
  extend_leaf {} [] 1 = {{},1,{}}.
Proof. reflexivity. Qed.

Example test_extend_leaf2 :
  extend_leaf {{{},2,{}},1,{{},3,{}}} [Right; Left] 4 =
  {{{},2,{}},1,{{{},4,{}},3,{}}}.
Proof. reflexivity. Qed.

Example test_extend_leaf3 :
  extend_leaf {{{},2,{}},1,{{},3,{}}} [Right; Left; Right] 4 =
  {{{},2,{}},1,{{{},4,{}},3,{}}}.
Proof. reflexivity. Qed.

Example test_extend_leaf4 :
  extend_leaf {{{},2,{}},1,{{},3,{}}} [Right] 4 =
  {{{},2,{}},1,{{},3,{}}}.
Proof. reflexivity. Qed.

Definition leaf_eqb {X} (t : btree X) : bool :=
  external_length t 0 =? 0.

Lemma leaf_eqb_eq : forall X (t : btree X),
    t = {} <-> leaf_eqb t = true.
Proof.
  split.
  - intro H. rewrite H. reflexivity.
  - unfold leaf_eqb. intro H. apply eqb_eq in H.
    induction t as [| l IHl x r IHr].
    + reflexivity.
    + simpl in H. rewrite <- external_length_S in H.
      discriminate H. Qed.

Theorem leaf_eqP : forall X (t : btree X),
    reflect (t = {}) (leaf_eqb t).
Proof.
  intros. apply iff_reflect. apply leaf_eqb_eq. Qed.

Lemma non_leaf_is_properly_extended : forall X (t : btree X),
    ~ (t = {}) ->
    exists t' ld x', ld_proper t' ld = true /\ t = extend_leaf t' ld x'.
Proof.
  induction t as [| l IHl x r IHr].
  - intros contra. exfalso. apply contra. reflexivity.
  - intros _. destruct (leaf_eqP _ l).
    + destruct (leaf_eqP _ r).
      * exists {}. exists []. exists x. simpl. rewrite H. rewrite H0.
        split; reflexivity.
      * apply IHr in H0. destruct H0 as [t' [ld [x' H0]]].
        exists {l,x,t'}. exists (Right :: ld). exists x'.
        simpl. destruct H0 as [H0 H1]. rewrite H0. rewrite H1.
        split; reflexivity.
    + apply IHl in H. destruct H as [t' [ld [x' H]]].
      exists {t',x,r}. exists (Left :: ld). exists x'.
      simpl. destruct H as [H0 H1]. rewrite H0. rewrite H1.
      split; reflexivity. Qed.

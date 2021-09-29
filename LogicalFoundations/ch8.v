From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Locate "+".
Locate "_ + _".
Print Init.Nat.add.

(* Equality between Strings *)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string, eqb_string s s = true.
Proof.
  intro s. unfold eqb_string.
  destruct (string_dec s s) as [Heq | Hne].
  - reflexivity.
  - destruct Hne. reflexivity. Qed.

Theorem eqb_string_true_iff : forall (x y : string),
    eqb_string x y = true <-> x = y.
Proof.
  intros x y. split.
  - unfold eqb_string. destruct (string_dec x y) as [Heq | Hne].
    + intro. apply Heq.
    + discriminate.
  - intro Heq. rewrite Heq. apply eqb_string_refl. Qed.

Theorem eqb_string_false_iff : forall (x y : string),
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

(* Total Maps *)

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  fun _ => v.

Definition t_update {A : Type} (m : total_map A)
           (x : string) (v : A) : total_map A :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' !-> v" := (t_empty v)
                            (at level 100, right associativity).
Notation "x !-> v ; m" := (t_update m x v)
                                (at level 100, v at next level, right associativity).

Definition example_empty := (_ !-> false).
Definition example_map :=
  ( "bar" !-> true
  ; "foo" !-> true
  ; _     !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof. intros A x v. unfold t_empty. reflexivity. Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) (x : string) (v : A),
    (x !-> v; m) x = v.
Proof.
  intros A m x v. unfold t_update. rewrite eqb_string_refl.
  reflexivity. Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) (x1 x2 : string) (v : A),
    x1 <> x2 -> (x1 !-> v; m) x2 = m x2.
Proof.
  intros A m x1 x2 v Hne. unfold t_update.
  rewrite <- eqb_string_false_iff in Hne. rewrite Hne. reflexivity. Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2; x !-> v1; m) = (x !-> v2; m).
Proof.
  intros A m x v1 v2. apply functional_extensionality. intro x'.
  unfold t_update. destruct (eqb_string x x') as [Heq | Hne].
  - reflexivity.
  - reflexivity. Qed.

Lemma eqb_stringP : forall (x y : string),
    reflect (x = y) (eqb_string x y).
Proof.
  intros x y. destruct (eqb_string x y) eqn:E.
  - apply ReflectT. rewrite <- eqb_string_true_iff. apply E.
  - apply ReflectF. rewrite <- eqb_string_true_iff. intro nE.
    rewrite E in nE. discriminate. Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x; m) = m.
Proof.
  intros A m x. apply functional_extensionality. intro x'.
  unfold t_update. destruct (eqb_stringP x x') as [Heq | Hne].
  - rewrite Heq. reflexivity.
  - reflexivity. Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1; x2 !-> v2; m) =
    (x2 !-> v2; x1 !-> v1; m).
Proof.
  intros A m v1 v2 x1 x2 Hxne. apply functional_extensionality. intro x.
  unfold t_update. destruct (eqb_stringP x1 x) as [E1 | nE1].
  - destruct (eqb_stringP x2 x) as [E2 | nE2].
    + rewrite E1 in Hxne. rewrite E2 in Hxne. destruct Hxne. reflexivity.
    + reflexivity.
  - reflexivity. Qed.

(* Partial Maps *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := _ !-> None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) : partial_map A := (x !-> Some v; m).

Notation "x |-> v ; m" := (update m x v)
                            (at level 100, v at next level, right associativity).

Notation "x |-> v" := (update empty x v)
                        (at level 100).

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof. intros A x. unfold empty. apply t_apply_empty. Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) (x : string) (v : A),
    (x |-> v; m) x = Some v.
Proof. intros A m x v. unfold update. apply t_update_eq. Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) (x1 x2 : string) (v : A),
    x2 <> x1 ->
    (x2 |-> v; m) x1 = m x1.
Proof.
  intros A m x1 x2 v Hne. unfold update.
  apply t_update_neq. apply Hne. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2; x |-> v1; m) = (x |-> v2; m).
Proof. intros A m x v1 v2. unfold update. apply t_update_shadow. Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same. Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A) v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 |-> v1; x2 |-> v2; m) =
    (x2 |-> v2; x1 |-> v1; m).
Proof.
  intros A m v1 v2 x1 x2 Hne. unfold update.
  apply t_update_permute. apply Hne. Qed.

Definition inclusion {A : Type} (m m' : partial_map A) : Prop :=
  forall (x : string) (v : A), m x = Some v -> m' x = Some v.

Lemma inclusion_update : forall (A : Type) (m m' : partial_map A)
                           (x : string) (v : A),
    inclusion m m' ->
    inclusion (x |-> v; m) (x |-> v; m').
Proof.
  intros A m m' x v H. unfold inclusion in *. intros x0 v0.
  unfold update. unfold t_update.
  destruct (eqb_stringP x x0).
  - trivial.
  - apply (H x0 v0). Qed.

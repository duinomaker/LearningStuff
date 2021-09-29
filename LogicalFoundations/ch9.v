Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

(* a playground module that helps me to recall the refined reflection *)
Module Silly.
  Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

  Theorem eqb_natP : forall a b : nat, reflect (a = b) (a =? b).
  Proof.
    intros a b. destruct (a =? b) eqn:E.
    - apply ReflectT. apply eqb_true. apply E.
    - apply ReflectF. intro contra. rewrite contra in E.
      rewrite eqb_refl in E. discriminate E. Qed.

  Theorem silly_refl : forall n : nat, n =? n = true.
  Proof.
    intros n. Show Proof. destruct (eqb_natP n n). Show Proof.
    - reflexivity. Show Proof.
    - exfalso. Show Proof.
      apply n0. Show Proof. reflexivity. Show Proof. Qed.
End Silly.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof. apply ev_SS.
  Show Proof. apply ev_SS.
  Show Proof. apply ev_0.
  Show Proof. Qed.

Theorem ev_8 : ev 8.
Proof.
  apply ev_SS. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Definition ev_8' : ev 8 := (ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0)))).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. apply ev_SS. apply ev_SS.
  apply H. Show Proof. Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) (H : ev n) => (ev_SS (S (S n)) (ev_SS n H)).

Definition add1 : nat -> nat.
  intro n. Show Proof.
  apply S. Show Proof.
  apply n. Show Proof.
Defined.

Print add1.

Module Props.
  Module And.
    Inductive and (P Q : Prop) : Prop :=
    | conj : P -> Q -> and P Q.

    Arguments conj [P] [Q].
    Notation "P /\ Q" := (and P Q) : type_scope.

    Theorem proj1' : forall P Q, P /\ Q -> P.
    Proof.
      intros P Q H. destruct H as [HP HQ]. apply HP.
      Show Proof. Qed.

    Lemma and_comm : forall P Q, P /\ Q <-> Q /\ P.
    Proof.
      intros P Q. Show Proof. split. Show Proof.
      - intro H. Show Proof. destruct H as [HP HQ]. Show Proof.
        split. Show Proof.
        + apply HQ. Show Proof.
        + apply HP. Show Proof.
      - intros [HQ HP]. split.
        + apply HP.
        + apply HQ. Show Proof. Qed.
  End And.

  Definition and_comm'_aux (P Q : Prop) (H : P /\ Q) : Q /\ P :=
    match H with
    | conj HP HQ => conj HQ HP
    end.

  Check and_comm'_aux.

  Definition and_comm' : forall (P Q : Prop), P /\ Q <-> Q /\ P.
    split.
    - intro H. apply (and_comm'_aux P Q). apply H.
    - intro H. apply (and_comm'_aux Q P). apply H. Defined.

  Definition and_comm'' : forall (P Q : Prop), P /\ Q <-> Q /\ P :=
    fun (P Q : Prop) => conj (fun H : P /\ Q => and_comm'_aux P Q H)
                        (fun H : Q /\ P => and_comm'_aux Q P H).

  (* Currying is brilliant! *)
  Definition and_comm''' (P Q : Prop) : P /\ Q <-> Q /\ P :=
    conj (and_comm'_aux P Q) (and_comm'_aux Q P).

  Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
    fun P Q R => (fun HPQ : P /\ Q =>
                 match HPQ with
                 | conj HP _ =>
                   (fun HQR : Q /\ R =>
                      match HQR with
                      | conj _ HR => conj HP HR
                      end)
                 end).

  Module Or.
    Inductive or (P Q : Prop) : Prop :=
    | or_introl : P -> or P Q
    | or_intror : Q -> or P Q.

    Arguments or_introl [P] [Q].
    Arguments or_intror [P] [Q].
    Notation "P \/ Q" := (or P Q) : type_scope.

    Definition inj_l : forall P Q : Prop, P -> P \/ Q :=
      fun P Q : Prop => fun HP : P => or_introl HP.

    Theorem inj_j' : forall P Q : Prop, P -> P \/ Q.
    Proof.
      intros P Q HP. Show Proof. left. (* selects the `or_introl` constructor *)
      Show Proof. apply HP. Qed.

    Definition or_elim : forall (P Q R : Prop), P \/ Q -> (P -> R) -> (Q -> R) -> R :=
      fun P Q R (H : P \/ Q) (HPR : P -> R) (HQR : Q -> R) =>
        match H with
        | or_introl HP => HPR HP
        | or_intror HQ => HQR HQ
        end.
  End Or.

  Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
    fun P Q (H : P \/ Q) =>
      match H with
      | or_introl HP => (@or_intror Q P) HP
      | or_intror HQ => (@or_introl Q P) HQ
      end.

  Module Ex.
    (* ex: "Show me a witness of the Prop, and I'll know there
            exists something that witnesses the Prop..." *)
    Inductive ex {A : Type} (P : A -> Prop) : Prop :=
    | ex_intro (x : A) : P x -> ex P.

    Notation "'exists' x , p" :=
      (ex (fun x => p)) (at level 200, right associativity) : type_scope.
  End Ex.

  Check @ex.
  Check @ex_intro.

  Check ex (fun n => ev n) : Prop.
  Definition some_nat_is_even : exists n, ev n :=
    ex_intro ev 0 ev_0.

  Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
    ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

  Inductive True : Prop :=
  | I : True.

  Definition p_implies_true : forall P : Prop, P -> True :=
    fun P (_ : P) => I.

  Inductive False : Prop :=.

  Definition ex_falso_quodlibet' : forall P, False -> P :=
    fun P (contra : False) =>
      match contra with end.
End Props.

Module MyEquality.
  Inductive eq {X : Type} : X -> X -> Prop :=
  | eq_refl : forall (x : X), eq x x.

  Notation "x == y" := (eq x y) (at level 70, no associativity).

  Definition singleton : forall (X : Type) (x : X), [] ++ [x] == x :: [] :=
    fun X x => eq_refl [x].

  Lemma equality__leibniz_equality : forall (X : Type) (x y : X),
      x == y -> forall (P : X -> Prop), P x -> P y.
  Proof.
    intros X x y [x_y] P HPx. apply HPx. Qed.

  Lemma leibniz_equality__equality : forall (X : Type) (x y : X),
      (forall P : X -> Prop, P x -> P y) -> x == y.
  Proof.
    intros X x y Leib. apply (Leib (eq x)).
    apply (eq_refl x). Qed.

  Theorem try_leibniz_refl : forall (X : Type) (x y : X),
      (forall P : X -> Prop, P x -> P y) -> (forall P : X -> Prop, P y -> P x).
  Proof.
    intros X x y Hxy P.
    apply (Hxy (fun t : X => P t -> P x)).
    intro H. apply H.
  Qed.
End MyEquality.

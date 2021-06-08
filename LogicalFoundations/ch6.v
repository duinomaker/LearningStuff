Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Theorem S_inj : injective S.
Proof.
  intros x y H. injection H as goal.
  apply goal. Qed.

Check @eq : forall A : Type, A -> A -> Prop.

Example and_example: 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity. Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB. Qed.

Example and_example': 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity. Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. destruct n as [| n'] eqn:En.
  - destruct m as [| m'] eqn:Em.
    + split.
      * reflexivity.
      * reflexivity.
    + discriminate H.
  - discriminate H. Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity. Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H. apply and_exercise in H.
  destruct H as [Hn Hm]. rewrite Hn. rewrite Hm.
  reflexivity. Qed.

Lemma proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q H. destruct H as [HP _]. apply HP. Qed.

Lemma proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q H. destruct H as [_ HQ]. apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q H. destruct H as [HP HQ]. split.
  - apply HQ.
  - apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR. Qed.

Check and : Prop -> Prop -> Prop.

Search (_ * 0 = 0).

Lemma eq_mult_0 : forall n m : nat,
    n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O. reflexivity. Qed.

Lemma or_intro_l : forall A B : Prop,
    A -> A \/ B.
Proof.
  intros A B H. left. apply H. Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intro n. destruct n as [| n'] eqn:E.
  - left. reflexivity.
  - right. reflexivity. Qed.

Module MyNot.
  Definition not (P : Prop) := P -> False.

  Notation "~ x" := (not x) : type_scope.

  Check not : Prop -> Prop.
End MyNot.

Theorem ex_falso_quodlibet : forall (P : Prop), False -> P.
Proof.
  intros P contra. destruct contra. Qed.

Theorem implies_false_implies_neg : forall (P : Prop),
    (P -> False) -> ~ P.
Proof.
  intros P H. unfold not. apply H. Qed.

Theorem not_p_implies_q_implies_p_and_not_q :
  forall (P Q : Prop), ~ (P -> Q) -> ~ P /\ Q.
Proof.
  intros P Q H. Abort.

Example implication_test : forall (P Q : Prop),
    ((P -> Q) -> False) -> P.
Proof.
  intros P Q HnPQ. apply implies_false_implies_neg in HnPQ. Abort.
  
Fact not_implies_our_not : forall (P : Prop),
    ~ P -> (forall Q : Prop, P -> Q).
Proof.
  intros P HnP Q HP. destruct HnP. apply HP. Qed.

Notation "x <> y" := (~ (x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not. intro H. discriminate H. Qed.

Theorem not_false : ~ False.
Proof.
  unfold not. intro H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P HP. unfold not. intros HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem contrapositive : forall P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ. unfold not. intro HNQ. intro HP.
  apply HPQ in HP. apply HNQ in HP. destruct HP. Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~ (P /\ ~P).
Proof.
  intro P. unfold not. intros [HP HNP].
  apply HNP in HP. destruct HP. Qed.

Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros b H. unfold not in H.
  destruct b.
  - apply ex_falso_quodlibet. apply H. reflexivity.
  - reflexivity. Qed.

Theorem not_true_is_false' : forall b : bool,
    b <> true -> b = false.
Proof.
  intros b H. destruct b eqn:Eb.
  - unfold not in H. exfalso.
    apply H. reflexivity.
  - reflexivity. Qed.

Check I : True.

Module MyIff.
  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

  Notation "P <-> Q" := (iff P Q)
                          (at level 95, no associativity)
                        : type_scope.
End MyIff.

Theorem iff_sym : forall (P Q : Prop),
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q. unfold iff. intros [HPQ HQP]. split.
  - apply HQP.
  - apply HPQ. Qed.

Lemma not_true_iff_false : forall b : bool,
    b <> true <-> b = false.
Proof.
  unfold iff. split.
  - apply not_true_is_false.
  - intro H. rewrite H. intro H'. discriminate H'. Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. unfold iff. split.
  - intros [HP | HQR].
    + split.
      * left. apply HP.
      * left. apply HP.
    + destruct HQR as [HQ HR]. split.
      * right. apply HQ.
      * right. apply HR.
  - intros [HPoQ HPoR]. destruct HPoQ as [HP | HQ].
    + destruct HPoR as [HP' | HR].
      * left. apply HP.
      * left. apply HP.
    + destruct HPoR as [HP' | HR].
      * left. apply HP'.
      * right. split.
        apply HQ. apply HR. Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - destruct n as [| n'].
    + destruct m as [| m'].
      * intro H. left. reflexivity.
      * intro H. left. reflexivity.
    + destruct m as [| m'].
      * intro H. right. reflexivity.
      * intro H. simpl in H. discriminate H.
  - apply eq_mult_0.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 : forall n m p,
    n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p. rewrite mult_0. rewrite mult_0.
  rewrite or_assoc. reflexivity. Qed.

Definition Even x := exists n : nat, x = double n.

Theorem four_is_even : Even 4.
Proof.
  unfold even. exists 2. reflexivity. Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) ->
    (exists o, n = 2 + o).
Proof.
  intro n. intros [m Hm]. exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists {X : Type} (P : X -> Prop) :
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros HA [x HE]. unfold not in HE.
  apply HE. apply HA. Qed.

Theorem dist_exists_or {X : Type} (P Q : X -> Prop) :
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  unfold iff. split.
  - intros H. destruct H as [x HE] eqn:E.
    destruct HE as [HP | HQ].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros HE. destruct HE as [HP | HQ].
    + destruct HP as [x HE]. exists x. left. apply HE.
    + destruct HQ as [x HE]. exists x. right. apply HE. Qed.

Fixpoint In {X : Type} (x : X) (l : list X) : Prop :=
  match l with
  | [] => False
  | h :: t => h = x \/ In x t
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity. Qed.

Example In_example_2 : forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl. intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity. Qed.

Theorem In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  induction l as [| h t IHt].
  - intros x. simpl. intros [].
  - simpl. intros x [Hhx | Hin].
    + left. rewrite Hhx. reflexivity.
    + right. apply IHt. apply Hin. Qed.

Theorem In_map_iff : forall (A B : Type) (f : A -> B)
                       (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [| h t IHt].
    + intros [].
    + simpl. intros [Hfh | Hy].
      * (* f h = y *) exists h. rewrite Hfh. split.
        reflexivity. left. reflexivity.
      * (* In y (map f t) *) apply IHt in Hy.
        destruct Hy as [x [Hy Hin]]. exists x. split.
        apply Hy. right. apply Hin.
  - intros [x [Hy Hin]]. rewrite <- Hy. apply In_map.
    apply Hin. Qed.

Theorem In_app_iff : forall (A : Type) (l l' : list A) (a : A),
    In a (l ++ l') <-> (In a l) \/ (In a l').
Proof.
  intros A l. split.
  - induction l as [| h t IHt].
    + (* In a l' *) simpl. intro H. right. apply H.
    + (* In a h::t *) simpl. intros [Hha | Hin].
      * left. left. apply Hha.
      * apply or_assoc. right. apply IHt. apply Hin.
  - induction l as [| h t IHt].
    + (* In a l' *) simpl. intros [[] | H]. apply H.
    + (* In a h::t *) simpl. rewrite <- or_assoc.
      intros [Hha | Hin].
      * left. apply Hha.
      * right. apply IHt. apply Hin. Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  := match l with
     | [] => True
     | h :: t => P h /\ All P t
     end.

Theorem All_in : forall (T : Type) (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P. split.
  - intro H. induction l as [| h t IHt].
    + reflexivity.
    + simpl. simpl in H. split.
      * (* P h *) apply H. left. reflexivity.
      * (* All P t *) apply IHt. intros x Hin.
        apply H. right. apply Hin.
  - intro H. induction l as [| h t IHt].
    + intros x Hin. simpl in Hin. destruct Hin.
    + simpl in H. destruct H as [HPh HPt].
      simpl. intros x H. destruct H as [Hh | Ht].
      * rewrite <- Hh. apply HPh.
      * apply IHt. apply HPt. apply Ht. Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  := fun n : nat =>
       match (odd n) with
       | true => Podd n
       | false => Peven n
       end.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n. destruct (odd n) eqn:E.
  - intros Hodd Heven. unfold combine_odd_even.
    rewrite E. apply Hodd. reflexivity.
  - intros Hodd Heven. unfold combine_odd_even.
    rewrite E. apply Heven. reflexivity. Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n H. unfold combine_odd_even in H.
  intro Hodd. rewrite Hodd in H. apply H. Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    even n = true ->
    Peven n.
Proof.
  intros Podd Peven n H. unfold combine_odd_even in H.
  intro Heven. unfold odd in H. rewrite Heven in H.
  simpl in H. apply H. Qed.

Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc : forall n, ~ (O = S n).
Proof.
  intros n H1. assert (H2: disc_fn O).
  { reflexivity. }
  rewrite H1 in H2. simpl in H2. apply H2. Qed.

Check add_comm.

Theorem in_not_nil : forall (X : Type) (x : X) (l : list X),
    In x l -> l <> [].
Proof.
  intros X x l H. unfold not. intro Hl.
  rewrite Hl in H. simpl in H. apply H. Qed.

Theorem in_not_nil_42 : forall (l : list nat),
    In 42 l -> l <> [].
Proof.
  intros l H. apply in_not_nil with (x:=42).
  apply H. Qed.

Theorem in_not_nil_42' : forall (l : list nat),
    In 42 l -> l <> [].
Proof.
  intros l H. apply in_not_nil in H.
  apply H. Qed.

Theorem in_not_nil_42'' : forall (l : list nat),
    In 42 l -> l <> [].
Proof.
  intros l H. Check (in_not_nil nat 42).
  apply (in_not_nil nat 42). apply H. Qed.

Theorem in_not_nil_42''' : forall (l : list nat),
    In 42 l -> l <> [].
Proof.
  intros l H. Check (in_not_nil _ _ _ H).
  apply (in_not_nil _ _ _ H). Qed.

Module MyPlayground.
  Theorem matching_test : forall (x : nat) (P : nat -> Prop), P x -> P (S x).
  Admitted.

  Theorem matching_test' : forall (P : nat -> Prop),
      P 12 -> P (S 12).
  Proof.
    intros P H. Check (matching_test _ _ H). Abort.
End MyPlayground.

Axiom functional_extensionality : forall {X Y : Type}
                                    {f g : X -> Y},
    (forall x : X, f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intro x.
  apply add_comm. Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Compute rev_append [1;2;3] [7;8;9].
Compute tr_rev [1;2;3].
Compute rev [1;2;3].

Fixpoint app' (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | x :: l1' => x :: (app' l1' l2)
  end.

Theorem tr_rev_correct : forall X,  @tr_rev X = @rev X.
Proof.
  intro X. apply functional_extensionality.
  intro l. induction l as [| h t IHt].
  - reflexivity.
  - unfold tr_rev. simpl.
    assert (H: forall l l1 l2 : list X, rev_append l (l1 ++ l2) = rev_append l l1 ++ l2).
    { induction l as [| h' t' IHt'].
      - reflexivity.
      - intros l1 l2. simpl. rewrite <- IHt'. reflexivity. }
    rewrite H with (l1:=[]) (l2:=[h]). f_equal. rewrite <- IHt.
    reflexivity. Qed.

Lemma evenb_double : forall k,
    even (double k) = true.
Proof.
  intro k. induction k as [| k' IHk'].
  - reflexivity.
  - simpl. apply IHk'. Qed.

Lemma evenb_double_conv : forall n, exists k,
      n = if even n then double k else S (double k).
Proof.
  intro n. induction n as [| n' IHn'].
  - exists 0. reflexivity.
  - destruct IHn' as [k H]. destruct (even n') eqn:E.
    + rewrite even_S. rewrite E. simpl. exists k.
      rewrite H. reflexivity.
    + rewrite even_S. rewrite E. simpl. exists (S k).
      simpl. rewrite H. reflexivity. Qed.

Theorem even_bool_prop : forall n : nat,
    even n = true <-> Even n.
Proof.
  split.
  - intro H. destruct (evenb_double_conv n) as [k Hn].
    rewrite H in Hn. exists k. apply Hn.
  - intros [k Hn]. rewrite Hn. apply evenb_double. Qed.

Example not_even_1001' : ~ (Even 1001).
Proof.
  rewrite <- even_bool_prop.
  unfold not.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma eqb_eq : forall n m : nat, (n =? m) = true <-> n = m.
Proof.
  split.
  - generalize dependent m. induction n as [| n' IHn'].
    + destruct m as [| m'] eqn:Em.
      * reflexivity.
      * discriminate.
    + destruct m as [| m'] eqn:Em.
      * discriminate.
      * intro H. f_equal. apply IHn'.
        simpl in H. apply H.
  - intro H. rewrite H. apply eqb_refl. Qed.

Lemma plus_eqb_example : forall n m p : nat,
    n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intro H. split.
    + destruct b1. reflexivity. discriminate H.
    + destruct b1.
      * simpl in H. apply H.
      * simpl in H. discriminate H.
  - intros [H1 H2]. rewrite H1. rewrite H2. reflexivity. Qed.

Theorem orb_true_iff : forall b1 b2 : bool,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intro H. destruct b1.
    + left. reflexivity.
    + right. simpl in H. apply H.
  - intros [H1 | H2].
    + rewrite H1. reflexivity.
    + rewrite H2. destruct b1.
      * reflexivity.
      * reflexivity. Qed.

Theorem eqb_neq : forall n m : nat, (n =? m) = false <-> n <> m.
Proof.
  intros n m. rewrite <- not_true_iff_false.
  unfold not. rewrite eqb_eq. reflexivity. Qed.

Fixpoint eqb_list {A : Type}
         (eqb : A -> A -> bool)
         (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ | _, [] => false
  | h1 :: t1, h2 :: t2 =>
    (eqb h1 h2) && (eqb_list eqb t1 t2)
  end.

Theorem eqb_list_true_iff :
  forall (A : Type) (eqb : A -> A -> bool),
    (forall a1 a2 : A, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2 : list A, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H. split.
  - generalize dependent l2. induction l1 as [| h1 t1 IHt1].
    + destruct l2 as [| h2 t2] eqn:E.
      * reflexivity.
      * simpl. discriminate.
    + destruct l2 as [| h2 t2] eqn:E.
      * simpl. discriminate.
      * simpl. intro Ht. rewrite andb_true_iff in Ht.
        destruct Ht as [HEh HEt]. rewrite H in HEh.
        f_equal. apply HEh. apply IHt1. apply HEt.
  - generalize dependent l2. induction l1 as [| h1 t1 IHt1].
    + destruct l2 as [| h2 t2] eqn:E.
      * reflexivity.
      * discriminate.
    + destruct l2 as [| h2 t2] eqn:E.
      * discriminate.
      * simpl. intro HEht. injection HEht. intros HEt HEh.
        rewrite andb_true_iff. split.
        rewrite H. apply HEh.
        apply IHt1. apply HEt. Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  split.
  - induction l as [| h t IHt].
    + reflexivity.
    + simpl. intro HEht. rewrite andb_true_iff in HEht.
      destruct HEht as [HEh HEt]. split.
      * apply HEh.
      * apply IHt. apply HEt.
  - induction l as [| h t IHt].
    + reflexivity.
    + simpl. intros [HEh HEt].
      rewrite andb_true_iff. split.
      * apply HEh.
      * apply IHt. apply HEt. Qed.

Definition excluded_middle := forall P : Prop,
    P \/ ~ P.

Theorem restricted_excluded_middle : forall (P : Prop) (b : bool),
    (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra.
    discriminate contra. Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
    n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (eqb n m)).
  symmetry. apply eqb_eq. Qed.

Theorem excluded_middle_irrefutable : forall (P : Prop),
    ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H. Check double_neg.
  assert (HP: ~ P -> ~ ~ ~ P).
  { unfold not. intros H1 H2. apply H2. apply H1. }
  unfold not in HP. apply HP.
  - intro H1. apply H. left. apply H1.
  - intro H1. apply H. right. apply H1. Qed.

Theorem excluded_middle_irrefutable' : forall (P : Prop),
    ~ ~ (P \/ ~ P).
Proof.
  unfold not.
  intros P HPPFF.
  apply HPPFF.
  right. intros HP. apply HPPFF.
  left. apply HP.
Qed.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros EM X P. intro HNE. unfold not in HNE.
  intro x. destruct (EM (P x)).
  - (* P x *) apply H.
  - (* ~ P x *) exfalso. apply HNE.
    exists x. unfold not in H. apply H. Qed.

Definition peirce := forall P Q : Prop,
    ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P : Prop,
    ~ ~ P -> P.

Definition de_morgan_not_and_not := forall P Q : Prop,
    ~ (~ P /\ ~ Q) -> P \/ Q.

Definition implies_to_or := forall P Q : Prop,
    (P -> Q) -> (~ P \/ Q).

Theorem excluded_middle__pierce :
  excluded_middle -> peirce.
Proof.
  intro EM. intros P Q HPQP.
Abort.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.
From LF Require Export ch7.

Inductive reg_exp (T : Type) : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp T)
| Union (r1 r2 : reg_exp T)
| Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
| MEmpty : [] =~ EmptyStr
| MChar x : [x] =~ Char x
| MApp s1 re1 s2 re2
       (H1 : s1 =~ re1)
       (H2 : s2 =~ re2)
  : s1 ++ s2 =~ App re1 re2
| MUnionL s re1 re2
          (H : s =~ re1)
  : s =~ Union re1 re2
| MUnionR s re1 re2
          (H : s =~ re2)
  : s =~ Union re1 re2
| MStar0 re : [] =~ Star re
| MStarApp s1 s2 re
        (H1 : s1 =~ re)
        (H2 : s2 =~ (Star re))
  : (s1 ++ s2) =~ Star re
where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof. apply (MApp [1]). apply MChar. apply MChar. Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof. unfold not. intro H. inversion H. Qed.

Fixpoint reg_exp_of_list {T} (l : list T) : reg_exp T :=
  match l with
  | [] => EmptyStr
  | h :: t => App (Char h) (reg_exp_of_list t)
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  apply (MApp [1]). apply MChar.
  apply (MApp [2]). apply MChar.
  apply (MApp [3]). apply MChar.
  apply MEmpty. Qed.

Lemma MStar1 : forall T s (re : reg_exp T),
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H. assert (Hs: s = s ++ []).
  { rewrite app_nil_r. reflexivity. } rewrite Hs.
  apply (MStarApp s []).
  - apply H.
  - apply MStar0. Qed.

Lemma MStar1' : forall T s (re : reg_exp T),
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0. Qed.

Lemma empty_is_empty : forall T (s : list T),
    ~ (s =~ EmptySet).
Proof.
  intros T s H. inversion H. Qed.

Lemma MUnion' : forall T (s : list T) re1 re2,
    s =~ re1 \/ s =~ re2 ->
    s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H1 | H2].
  - apply MUnionL, H1.
  - apply MUnionR, H2. Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
    (forall s, In s ss -> s =~ re) ->
    (fold app ss []) =~ Star re.
Proof.
  intros T ss re H. induction ss as [| hs ts IH].
  - (* ss = [] *) apply MStar0.
  - (* ss = hs :: ts *) simpl. apply MStarApp.
    + (* hs =~ re ? *)
      apply H. simpl. left. reflexivity.
    + (* fold app ts [] =~ re ? *)
      apply IH. intros s Hs. apply H.
      simpl. right. apply Hs. Qed.

(* TODO: Figure out what happens when I prove. *)
Lemma reg_exp_of_list_spec_firsttry : forall T (s1 s2 : list T),
    s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. split.
  - intro H. generalize dependent s1.
    induction s2 as [| h2 t2 IH]; destruct s1 as [| h1 t1] eqn:Es1.
    + reflexivity.
    + simpl. intro H. inversion H.
    + simpl. intro H. inversion H. inversion H3. rewrite <- H5 in H1.
      discriminate H1.
    + intro H. f_equal.
      * inversion H. inversion H3. rewrite <- H5 in H3.
        rewrite <- H5 in H1. inversion H1.
        rewrite <- H7. rewrite <- H8. reflexivity.
      * apply IH. inversion H. inversion H3. rewrite <- H5 in H1.
        inversion H1. rewrite <- H9. apply H4.
  - intro H. generalize dependent s2.
    induction s1 as [| h t IH].
    + simpl. intros s2 H. rewrite <- H. apply MEmpty.
    + simpl. intros s2 H. assert (Happ: h :: t = [h] ++ t).
      { reflexivity. } rewrite <- H. simpl. rewrite Happ. apply MApp.
      * apply MChar.
      * apply IH. reflexivity. Qed.

(* This one is simpler, without a redundant `destruct`;
   it works, because `inversion` does destructions automatically. *)
Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
    s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. split.
  - generalize dependent s1. induction s2 as [| h t IH].
    + intros s1 H. inversion H. reflexivity.
    + simpl. intros s1 H. inversion H. apply IH in H4.
      rewrite H4. inversion H3. reflexivity.
  - generalize dependent s1. induction s2 as [| h t IH].
    + intros s1 H. rewrite H. apply MEmpty.
    + simpl. intros s1 H. rewrite H. replace (h :: t) with ([h] ++ t).
      * apply MApp.
        -- apply MChar.
        -- apply IH. reflexivity.
      * reflexivity. Qed.
    
Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_regexp : forall T (s : list T) (re : reg_exp T) (x : T),
    s =~ re ->
    In x s ->
    In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s re1 re2 Hmatch IH | s re1 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)
    destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin. apply Hin.
  - (* MApp *)
    simpl. rewrite In_app_iff in *. destruct Hin as [Hin | Hin].
    + left. apply (IH1 Hin).
    + right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff. left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff. right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    rewrite In_app_iff in Hin. simpl in *. destruct Hin.
    + apply (IH1 H).
    + apply (IH2 H).
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App r1 r2 => (re_not_empty r1) && (re_not_empty r2)
  | Union r1 r2 => (re_not_empty r1) || (re_not_empty r2)
  | Star _ => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
    (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros [s E]. induction E
      as [| x'
          | s1 re1 s2 re2 E1 IH1 E2 IH2
          | s re1 re2 E IH | s re1 re2 E IH
          | re | s1 s2 re E1 IH1 E2 IH2].
    + (* MEmpty *)
      simpl. reflexivity.
    + (* MChar *)
      simpl. reflexivity.
    + (* MApp *)
      simpl. rewrite IH1. rewrite IH2. reflexivity.
    + (* MUnionL *)
      simpl. rewrite IH. reflexivity.
    + (* MUnionR *)
      simpl. rewrite IH. destruct (re_not_empty re1); reflexivity.
    + (* MStar0 *)
      simpl. reflexivity.
    + (* MStarApp *)
      apply IH2.
  - intro H. induction re
      as [| | t
          | r1 IH1 r2 IH2
          | r1 IH1 r2 IH2
          | r IH].
    + (* EmptySet *)
      simpl in H. discriminate H.
    + (* EmptyStr *)
      exists []. apply MEmpty.
    + (* Char *)
      exists [t]. apply MChar.
    + (* App *)
      simpl in H.
      destruct (re_not_empty r1); destruct (re_not_empty r2).
      * destruct IH1 as [s1].
        { reflexivity. }
        destruct IH2 as [s2].
        { reflexivity. }
        exists (s1 ++ s2). apply MApp.
        -- apply H0.
        -- apply H1.
      * discriminate H.
      * discriminate H.
      * discriminate H.
    + (* Union *)
      simpl in H.
      destruct (re_not_empty r1); destruct (re_not_empty r2).
      * destruct IH1 as [s].
        { reflexivity. }
        exists s. apply MUnionL. apply H0.
      * destruct IH1 as [s].
        { reflexivity. }
        exists s. apply MUnionL. apply H0.
      * destruct IH2 as [s].
        { reflexivity. }
        exists s. apply MUnionR. apply H0.
      * discriminate H.
    + (* Star *)
      exists []. apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
    s1 =~ Star re ->
    s2 =~ Star re ->
    s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1. generalize dependent s2.
  remember (Star re) as re'.
  induction H1
    as [| x'
        | s1' re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        | s re1 re2 Hmatch IH | s re1 re2 Hmatch IH
        | re' | s1' s2' re' Hmatch1 IH1 Hmatch2 IH2].
  - discriminate Heqre'.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - discriminate Heqre'.
  - (* MStar0 *) intros s2 goal. apply goal.
  - (* MStarApp *) intros s2 H1. rewrite <- app_assoc.
    apply MStarApp. apply Hmatch1. apply IH2.
    + apply Heqre'.
    + apply H1. Qed.

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
    s =~ Star re ->
    exists ss : list (list T),
      s = fold app ss []
      /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re HsMre.
  remember (Star re) as re'.
  induction HsMre
    as [| x'
        | s1' re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        | s re1 re2 Hmatch IH | s re1 re2 Hmatch IH
        | re' | s1' s2' re' Hmatch1 IH1 Hmatch2 IH2].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split.
    + reflexivity.
    + intros s' H. destruct H.
  - destruct (IH2 Heqre') as [ss [IHs2 IHss]]. exists (s1' :: ss).
    simpl. split.
    + rewrite IHs2. reflexivity.
    + intros s' H. destruct H as [H1 | H2]. injection Heqre' as Heqre''.
      * rewrite <- H1. rewrite <- Heqre''. apply Hmatch1.
      * apply IHss. apply H2. Qed.

Module Pumping.

  Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
    match re with
    | EmptySet => 1
    | EmptyStr => 1
    | Char _ => 2
    | App re1 re2 => pumping_constant re1 + pumping_constant re2
    | Union re1 re2 => pumping_constant re1 + pumping_constant re2
    | Star r => pumping_constant r
    end.

  Lemma pumping_constant_ge_1 : forall T (re : reg_exp T),
      pumping_constant re >= 1.
  Proof.
    intros T re. induction re.
    - simpl. apply le_n.
    - simpl. apply le_n.
    - simpl. apply le_S, le_n.
    - simpl. apply le_trans with (n:=pumping_constant re1).
      apply IHre1. apply le_plus_l.
    - simpl. apply le_trans with (n:=pumping_constant re1).
      apply IHre1. apply le_plus_l.
    - simpl. apply IHre. Qed.

  Lemma pumping_constant_0_false : forall T (re : reg_exp T),
      pumping_constant re = 0 -> False.
  Proof.
    intros T re H.
    destruct (pumping_constant_ge_1 T re); discriminate H.
  Qed.

  Fixpoint napp {T} (n : nat) (l : list T) : list T :=
    match n with
    | O => []
    | S n' => l ++ napp n' l
    end.
  
  Lemma napp_plus : forall T (n m : nat) (l : list T),
      napp (n + m) l = napp n l ++ napp m l.
  Proof.
    intros T n m l. induction n as [| n' IH].
    - reflexivity.
    - simpl. rewrite <- app_assoc. f_equal. apply IH. Qed.

  Lemma napp_star : forall T m s1 s2 (re : reg_exp T),
      s1 =~ re ->
      s2 =~ Star re ->
      napp m s1 ++ s2 =~ Star re.
  Proof.
    intros T m s1 s2 re H1 H2.
    induction m as [| m' IH].
    - simpl. apply H2.
    - simpl. rewrite <- app_assoc. apply MStarApp.
      + apply H1.
      + apply IH. Qed.

  Lemma cons_app : forall T x (s1 s2 : list T),
      x :: s1 ++ s2 = (x :: s1) ++ s2.
  Proof. reflexivity. Qed.

  Lemma weak_pumping : forall T (re : reg_exp T) s,
      s =~ re ->
      pumping_constant re <= length s ->
      exists s1 s2 s3,
        s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof.
    intros T re s Hmatch.
    induction Hmatch
      as [| x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
          | s1 re1 re2 Hmatch IH | s2 re1 re2 Hmatch IH
          | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    simpl. intros contra. inversion contra. inversion H0.
  - (* MApp *)
    rewrite app_length. simpl. intro H. apply add_le_cases in H.
    destruct H as [H | H].
    + apply IH1 in H. destruct H as [s3 [s4 [s5 H]]].
      exists s3. exists s4. exists (s5 ++ s2). destruct H as [H1 [H2 H3]]. split.
      * rewrite H1. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
      * split.
        -- apply H2.
        -- intro m. rewrite app_assoc. rewrite app_assoc.
           rewrite <- (app_assoc _ s3 (napp m s4) s5). apply MApp.
           ++ apply H3.
           ++ apply Hmatch2.
    + apply IH2 in H. destruct H as [s3 [s4 [s5 H]]].
      exists (s1 ++ s3). exists s4. exists s5. destruct H as [H1 [H2 H3]]. split.
      * rewrite H1. rewrite <- app_assoc. reflexivity.
      * split.
        -- apply H2.
        -- intro m. rewrite <- app_assoc. apply MApp.
           ++ apply Hmatch1.
           ++ apply H3.
  - (* MUnionL *)
    simpl. intro H. apply (le_trans (pumping_constant re1)) in H.
    + apply IH in H. destruct H as [s2 [s3 [s4 [H1 [H2 H3]]]]].
      exists s2. exists s3. exists s4. split.
      * apply H1.
      * split.
        -- apply H2.
        -- intro m. apply MUnionL. apply H3.
    + apply le_plus_l.
  - (* MUnionR *)
    simpl. intro H. apply (le_trans (pumping_constant re2)) in H.
    + apply IH in H. destruct H as [s3 [s4 [s5 [H1 [H2 H3]]]]].
      exists s3. exists s4. exists s5. split.
      * apply H1.
      * split.
        -- apply H2.
        -- intro m. apply MUnionR. apply H3.
    + rewrite add_comm. apply le_plus_l.
  - (* MStar0 *)
    intro H. inversion H. apply pumping_constant_0_false in H1.
    exfalso. apply H1.
  - (* MStarApp *)
    rewrite app_length. simpl in *. intro H. destruct s1.
    + apply (IH2 H).
    + destruct s2.
      * simpl in *. rewrite app_nil_r. rewrite add_0_r in H.
        apply IH1 in H. destruct H as [s2 [s3 [s4 [H1 [H2 H3]]]]].
        exists s2. exists s3. exists s4. split.
        apply H1. split.
        -- apply H2.
        -- intro m. apply MStar1. apply H3.
      * simpl in *. exists (x :: s1). exists (x0 :: s2). exists []. split.
        rewrite app_nil_r. reflexivity. split.
        -- intro contra. discriminate contra.
        -- intro m. simpl. rewrite app_nil_r.
           rewrite cons_app.
           apply MStarApp.
           ++ apply Hmatch1.
           ++ induction m as [| m' IHm].
              ** apply MStar0.
              ** simpl. rewrite cons_app. apply star_app.
                 apply Hmatch2. apply IHm.
  Qed.

  Lemma pumping : forall T (re : reg_exp T) s,
      s =~ re ->
      pumping_constant re <= length s ->
      exists s1 s2 s3,
        s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        length s1 + length s2 <= pumping_constant re /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof. Admitted.

End Pumping.

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [| m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(* … which essentially means *)
Inductive reflect' (P : Prop) : bool -> Prop :=
| Reflect'T : P -> reflect' P true
| Reflect'F : (P -> False) -> reflect' P false.
                                         
Check reflect : Prop -> bool -> Prop.
Check ReflectT True : True -> reflect True true.
Check ReflectF False : (False -> False) -> reflect False false.

(* … and is also equivalent to *)
Inductive reflect'' : Prop -> bool -> Prop :=
| Reflect''T (P : Prop) (H : P) : reflect'' P true
| Reflect''F (P : Prop) (H : ~ P) : reflect'' P false.

Inductive silly_equal (n : nat) : nat -> Prop :=
| Silly_0 (H : n = 0) : silly_equal n 0
| Silly_n : silly_equal n n.

Check silly_equal : nat -> nat -> Prop.
Check Silly_0 2 : (2 = 0) -> silly_equal 2 0.
Check Silly_n 4 : silly_equal 4 4.

Theorem iff_reflect : forall P b,
    (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:EQb.
  - apply ReflectT. apply H. reflexivity.
  - apply ReflectF. rewrite H. discriminate. Qed.

Theorem reflect_iff : forall P b,
    reflect P b -> (P <-> b = true).
Proof.
  intros P b H. inversion H.
  - split.
    + trivial.
    + trivial.
  - split.
    + intro contra. exfalso. apply (H0 contra).
    + discriminate. Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. symmetry. apply eqb_eq. Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [| m l' IH].
  - simpl. intro contra. apply contra. reflexivity.
  - simpl. destruct (eqbP n m).
    + (* ReflectT : n = m *)
      intro H1. left. rewrite H. reflexivity.
    + (* ReflectF : n ≠ m *)
      intro H1. right. apply (IH H1). Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
    count n l = 0 -> ~ (In n l).
Proof.
  intros n l H. induction l as [| m l' IHl'].
  - intro contra. destruct contra.
  - simpl in *. destruct (eqbP n m).
    + discriminate H.
    + intro contra. destruct contra as [C1 | C2].
      * symmetry in C1. apply (H0 C1).
      * apply (IHl' H C2). Qed.

(* UNFINISHED: pumping *)

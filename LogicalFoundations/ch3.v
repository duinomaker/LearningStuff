From LF Require Export Induction.

Module NatList.
  Inductive natprod : Type :=
  | pair (n1 n2 : nat).

  Check (pair 3 5) : natprod.

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Compute fst (pair 3 5).

  Notation "( x , y )" := (pair x y).

  Compute fst (3,5).

  Theorem surjective_pairing' : forall (n m : nat),
      (n,m) = (fst (n,m), snd (n,m)).
  Proof.
    reflexivity. Qed.

  Theorem surjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    intros [n m]. reflexivity. Qed.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | pair x y => (y,x)
    end.

  Theorem snd_fst_is_swap : forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof.
    intros [n m]. reflexivity. Qed.

  Theorem fst_swap_is_snd : forall (p : natprod),
      fst (swap_pair p) = snd p.
  Proof.
    intros [n m]. reflexivity. Qed.

  Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

  Definition my_list := (cons 1 (cons 2 (cons 3 nil))).

  Notation "x :: y" := (cons x y)
                         (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Definition my_list' := 1 :: 2 :: [3].

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l : natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y)
                         (at level 60, right associativity).

  Example test_app1 : [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.
  Example test_app2: nil ++ [4;5] = [4;5].
  Proof. reflexivity. Qed.
  Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof. reflexivity. Qed.

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

  Example test_hd1: hd 0 [1;2;3] = 1.
  Proof. reflexivity. Qed.
  Example test_hd2: hd 0 [] = 0.
  Proof. reflexivity. Qed.
  Example test_tl: tl [1;2;3] = [2;3].
  Proof. reflexivity. Qed.

  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
      match h with
      | O => nonzeros t
      | _ => h :: (nonzeros t)
      end
    end.
  Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
      match (oddb h) with
      | true => h :: (oddmembers t)
      | false => oddmembers t
      end
    end.
  Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.

  Definition countoddmembers (l : natlist) : nat :=
    (length (oddmembers l)).
  Example test_countoddmembers1:
    countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.
  Example test_countoddmembers2:
    countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed.
  Example test_countoddmembers3:
    countoddmembers nil = 0.
  Proof. reflexivity. Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h1 :: t1 =>
      match l2 with
      | nil => l1
      | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
      end
    end.
  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.
  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.
  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.
  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.

  Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => O
    | h :: t =>
      match (h =? v) with
      | true => S (count v t)
      | false => count v t
      end
    end.
  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. reflexivity. Qed.
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.

  Definition sum : bag -> bag -> bag
    := app.
  Example test_sum1 : count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.

  Definition add (v : nat) (s : bag) : bag
    := (cons v s).
  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.
  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Definition member (v : nat) (s : bag) : bool
    := (negb ((count v s) =? 0)).
  Example test_member1: member 1 [1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_member2: member 2 [1;4;1] = false.
  Proof. reflexivity. Qed.

  Fixpoint remove_one (v : nat) (s : bag) : bag
    := match s with
       | nil => nil
       | h :: t =>
         match (h =? v) with
         | true => t
         | false => (add h (remove_one v t))
         end
       end.
  Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed.

  Fixpoint remove_all (v : nat) (s : bag) : bag
    := match s with
       | nil => nil
       | h :: t =>
         match (h =? v) with
         | true => remove_all v t
         | false => add h (remove_all v t)
         end
       end.
  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint subset (s1 : bag) (s2 : bag) : bool
    := match s1 with
       | nil => true
       | h :: t =>
         match (member h s2) with
         | false => false
         | true => subset t (remove_one h s2)
         end
       end.
  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof. reflexivity. Qed.
 
  Theorem bag_theorem : forall (v : nat) (s : bag),
      (count v (add v s)) = (S (count v s)).
  Proof.
    intros v s. assert (H : v =? v = true).
    { induction v as [| v' IHv'].
      - reflexivity.
      - simpl. rewrite -> IHv'. reflexivity. }
    simpl. rewrite -> H. reflexivity. Qed.
 
  Theorem nil_app : forall l : natlist,
      [] ++ l = l.
  Proof. reflexivity. Qed.

  Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => (rev t) ++ [h]
    end.
  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    induction l1 as [| n1 l1' IHl1'].
    - reflexivity.
    - intros l2. simpl.
      rewrite <- IHl1'. reflexivity. Qed.

  Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
  Proof.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> app_length.
      simpl. rewrite -> IHl'. rewrite -> plus_comm.
      reflexivity. Qed.

  Search (_ * _ = _ + _) inside Induction.
  Search (?x + ?y = ?y + ?x).

  Theorem app_nil_r : forall l : natlist,
      l ++ [] = l.
  Proof.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem app_assoc : forall (l1 l2 l3 : natlist),
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite <- IHl1'. reflexivity. Qed.
  
  Theorem rev_app_distr: forall l1 l2 : natlist,
      rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IHl1'.
      rewrite -> app_assoc. reflexivity. Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> rev_app_distr.
      rewrite -> IHl'. reflexivity. Qed.

  Check app_assoc.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_assoc.
    rewrite -> app_assoc.
    reflexivity. Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - destruct n as [| n'] eqn:E.
      + simpl. rewrite <- IHl1'. reflexivity.
      + simpl. rewrite <- IHl1'. reflexivity. Qed.

  Fixpoint eqblist (l1 l2 : natlist) : bool
    := match l1 with
       | nil =>
         match l2 with
         | nil => true
         | _ => false
         end
       | h1 :: t1 =>
         match l2 with
         | nil => false
         | h2 :: t2 =>
           match (h1 =? h2) with
           | false => false
           | true => eqblist t1 t2
           end
         end
       end.
  Example test_eqblist1 :
    (eqblist nil nil = true).
  Proof. reflexivity. Qed.
  Example test_eqblist2 :
    eqblist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.
  Example test_eqblist3 :
    eqblist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.

  Theorem eqblist_refl : forall l : natlist,
      true = eqblist l l.
  Proof.
    induction l as [| n l' IHl'].
    - reflexivity.
    - assert (H : n =? n = true).
    { induction n as [| n' IHn'].
      - reflexivity.
      - simpl. rewrite -> IHn'. reflexivity. }
    simpl. rewrite -> H.
    rewrite -> IHl'. reflexivity. Qed.

  Theorem count_member_nonzero : forall (s : bag),
      1 <=? (count 1 (1 :: s)) = true.
  Proof.
    induction s as [| n s' IHs'].
    - reflexivity.
    - reflexivity. Qed.

  Theorem leb_n_Sn : forall n,
      n <=? (S n) = true.
  Proof.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'.
      reflexivity. Qed.

  Theorem remove_does_not_increase_count : forall (s : bag),
      (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
  Proof.
    induction s as [| n s' IHs'].
    - reflexivity.
    - destruct n as [| n'] eqn:E.
      + simpl. rewrite -> leb_n_Sn. reflexivity.
      + simpl. rewrite -> IHs'. reflexivity. Qed.

  Theorem bag_count_sum : forall (v : nat) (s1 s2 : bag),
      count v (sum s1 s2) = (count v s1) + (count v s2).
  Proof.
    intros v s1 s2. induction s1 as [| n s1' IHs1'].
    - reflexivity.
    - simpl. destruct (n =? v) as [|].
      + simpl. rewrite IHs1'. reflexivity.
      + rewrite IHs1'. reflexivity. Qed.

  Theorem rev_injective : forall (l1 l2 : natlist),
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H. assert (H0 : rev (rev l1) = l1).
    { rewrite rev_involutive. reflexivity. }
    rewrite <- H0. rewrite H. rewrite rev_involutive.
    reflexivity. Qed.

  Inductive natoption : Type :=
    | Some (n : nat)
    | None.

  Fixpoint nth_error (l : natlist) (n : nat) :=
    match l with
    | nil => None
    | h :: t =>
      match n with
      | O => Some h
      | S n' => nth_error t n'
      end
    end.
  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.
  Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
  Proof. reflexivity. Qed.
  Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
  Proof. reflexivity. Qed.

  Fixpoint nth_error' (l : natlist) (n : nat) :=
    match l with
    | nil => None
    | h :: t =>
      if n =? 0 then Some h
      else nth_error' t (pred n)
    end.
  Example test_nth_error'1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.
  Example test_nth_error'2 : nth_error [4;5;6;7] 3 = Some 7.
  Proof. reflexivity. Qed.
  Example test_nth_error'3 : nth_error [4;5;6;7] 9 = None.
  Proof. reflexivity. Qed.

  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.

  Definition hd_error (l : natlist) : natoption :=
    match l with
    | nil => None
    | h :: t => Some h
    end.
  Example test_hd_error1 : hd_error [] = None.
  Proof. reflexivity. Qed.
  Example test_hd_error2 : hd_error [1] = Some 1.
  Proof. reflexivity. Qed.
  Example test_hd_error3 : hd_error [5;6] = Some 5.
  Proof. reflexivity. Qed.

  Theorem option_elim_hd : forall (l : natlist) (default : nat),
      hd default l = option_elim default (hd_error l).
  Proof.
    intros l default. induction l as [| n l' IHl'].
    - reflexivity.
    - reflexivity. Qed.
End NatList.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (i1 i2 : id) : bool :=
  match i1, i2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall i, eqb_id i i = true.
Proof.
  intro i. destruct i as [n]. simpl.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

Module PartialMap.
  Export NatList.

  Inductive partial_map : Type :=
    | empty
    | record (i : id) (v : nat) (m : partial_map).

  Definition update (i : id) (v : nat)
             (m : partial_map) : partial_map :=
    record i v m.

  Fixpoint find (i : id) (m : partial_map) : natoption :=
    match m with
    | empty => None
    | record j v n =>
      if eqb_id i j then Some v
      else find i n
    end.

  Theorem update_eq : forall (i : id) (v : nat) (m : partial_map),
      find i (update i v m) = Some v.
  Proof.
    intros i v m. simpl. assert (H : eqb_id i i = true).
    { destruct i as [n]. simpl. induction n as [| n' IHn'].
      - reflexivity.
      - simpl. rewrite IHn'. reflexivity. }
    rewrite H. reflexivity. Qed.

  Theorem update_neq : forall (i j : id) (v : nat) (m : partial_map),
      eqb_id i j = false -> find i (update j v m) = find i m.
  Proof.
    intros i j v m. intro H.
    simpl. rewrite H. reflexivity. Qed.
End PartialMap.

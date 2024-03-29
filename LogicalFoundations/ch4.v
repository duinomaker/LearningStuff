From LF Require Export Lists.

Inductive list (X : Type) : Type :=
| nil
| cons (n : X) (l : list X).

Check cons nat 0 (nil nat) : list nat.

Check cons : forall X : Type, X -> list X -> list X.

Fixpoint repeat (X : Type) (x: X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.
Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.
  Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

  Inductive grumble (X : Type) : Type :=
  | d (m : mumble)
  | e (x : X).
End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.


Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat' _ x count')
  end.

Check repeat''.

Arguments nil {X}.
Arguments cons {X} n l.
Arguments repeat {X} x count.

Fixpoint repeat''' {X : Type} x count : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

Check repeat'''.

Inductive list' {X : Type} : Type :=
| nil'
| cons' (x : X) (l : list').

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons x l1' => cons x (app l1' l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons x l' => app (rev l') (cons x nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (length l')
  end.

Definition mynil : list nat := nil.
Check mynil : list nat.
Check @nil.

Notation "x :: y" := (cons x y)
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Definition mylist := 1 :: 2 :: [3] ++ [4;5;6].
Compute mylist.

Theorem app_nil_r : forall (X : Type), forall (l : list X),
      l ++ [] = l.
Proof.
  intros X l. induction l as [| x l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity. Qed.

Theorem app_assoc : forall (X : Type), forall (l1 l2 l3 : list X),
      (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof.
  intros X l1 l2 l3. induction l1 as [| x l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity. Qed.

Theorem app_length : forall (X : Type), forall (l1 l2 : list X),
      length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros X l1 l2. induction l1 as [| x l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity. Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
    rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros X l1 l2.  induction l1 as [| x l1' IHl1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity. Qed.

Theorem rev_involute : forall X (l : list X),
    rev (rev l) = l.
Proof.
  intros X l.  induction l as [| x l' IHl'].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'. reflexivity. Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Check (1,true).

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | pair x _ => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | pair _ y => y
  end.

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y)
  : list (X * Y) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: l1', y :: l2' => (x,y) :: (combine l1' l2')
  end.

Fixpoint split {X Y : Type} (l : list (X * Y))
  : (list X) * (list Y) :=
  match l with
  | nil => ([],[])
  | p :: l' => ((fst p) :: (fst (split l')), (snd p) :: (snd (split l')))
  end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.
  Inductive option (X : Type) : Type :=
  | Some (x : X)
  | None.

  Arguments Some {X} _.
  Arguments None {X}.

  Check @None nat.
  Definition myoption : (option nat) := None.
  Check myoption.
End OptionPlayground.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: _ => Some h
  end.

Check hd_error.
Check @hd_error : forall X : Type, list X -> option X.

Definition doit3times {X : Type} (f : X -> X) (x : X) : X :=
  f (f (f x)).
Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times : doit3times S O = 3.
Proof. reflexivity. Qed.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.
Example test_filter1 : filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Example test_filter2 :
  filter (fun l => length l =? 1) [[1;2];[3];[4;5;6];[7]] = [[3];[7]].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => negb (leb n 7)) (filter evenb l).
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. simpl. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type}
           (test : X -> bool)
           (l : list X) : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type}
         (f : X -> Y)
         (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.
Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_app_distr : forall (X Y : Type), forall (f : X -> Y) (l1 l2 : list X),
      map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2. induction l1 as [| x l1' IHl1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity. Qed.
    
Theorem map_rev : forall (X Y: Type), forall (f : X -> Y) (l : list X),
      map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| x l' IHl'].
  - reflexivity.
  - simpl. rewrite map_app_distr.
    simpl. rewrite IHl'. reflexivity. Qed.

Fixpoint flat_map {X Y : Type}
         (f : X -> list Y)
         (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Fixpoint fold {X Y : Type}
         (f : X -> Y -> Y)
         (l : list X)
         (b : Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.
Compute fold plus [1;2;3;4;5] 0.
Check fold andb : list bool -> bool -> bool.

Compute doit3times (plus 3) 0.

Module Exercises.
  Definition fold_length {X : Type} (l : list X) : nat :=
    fold (fun _ n => S n) l 0.

  Theorem fold_length_correct : forall X (l : list X),
      fold_length l = length l.
  Proof.
    intros X l. induction l as [| x l' IHl'].
    - reflexivity.
    - assert (H: fold_length (x :: l') = S (fold_length l')).
      { reflexivity. } rewrite H. simpl. rewrite IHl'.
      reflexivity. Qed.

  Definition fold_map {X Y : Type}
             (f: X -> Y) (l: list X) : list Y :=
    fold (fun x l' => (f x) :: l') l [].
  Example test_fold_map1:
    fold_map (fun x => plus 3 x) [2;0;2] = [5;3;5].
  Proof. reflexivity. Qed.
  Example test_fold_map2:
    fold_map oddb [2;1;2;5] = [false;true;false;true].
  Proof. reflexivity. Qed.
  Example test_fold_map3:
      fold_map (fun n => [evenb n;oddb n]) [2;1;2;5]
    = [[true;false];[false;true];[true;false];[false;true]].
  Proof. reflexivity. Qed.

  Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
      fold_map f l = map f l.
  Proof.
    intros X Y f l. induction l as [| x l' IHl'].
    - reflexivity.
    - assert (H: fold_map f (x :: l') =  (f x) :: (fold_map f l')).
      { reflexivity. } rewrite H. simpl. rewrite IHl'.
      reflexivity. Qed.

  Definition prod_curry {X Y Z : Type}
             (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

  Definition prod_uncurry {X Y Z : Type}
             (f : X -> Y -> Z) (p : X * Y) : Z
    := f (fst p) (snd p).
  
  Check @prod_uncurry : forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z.

  Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
      prod_curry (prod_uncurry f) x y = f x y.
  Proof.
    intros X Y Z f x y. reflexivity. Qed.

  Module Church.
    Definition cnat := forall X : Type, (X -> X) -> X -> X.

    Definition one : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => f x.

     Definition two : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => f (f x).

    Definition zero : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => x.

    Definition three := @doit3times.

    Definition succ (n : cnat) : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

    Example succ_1 : succ zero = one.
    Proof. reflexivity. Qed.
    Example succ_2 : succ one = two.
    Proof. reflexivity. Qed.
    Example succ_3 : succ two = three.
    Proof. reflexivity. Qed.

    Definition plus (n m : cnat) : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).
    Example plus_1 : plus zero one = one.
    Proof. reflexivity. Qed.
    Example plus_2 : plus two three = plus three two.
    Proof. reflexivity. Qed.
    Example plus_3 :
      plus (plus two two) three = plus one (plus three three).
    Proof. reflexivity. Qed.

    Definition mult (n m : cnat) : cnat :=
      fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.
    Example mult_1 : mult one one = one.
    Proof. reflexivity. Qed.
    Example mult_2 : mult zero (plus three three) = zero.
    Proof. reflexivity. Qed.
    Example mult_3 : mult two three = plus three three.
    Proof. reflexivity. Qed.

    Definition exp (n m : cnat) : cnat :=
      fun (X : Type) (f : X -> X) (x : X) =>
        m (X -> X) (n X) f x.
    Example exp_1 : exp two two = plus two two.
    Proof. reflexivity. Qed.
    Example exp_2 : exp three zero = one.
    Proof. reflexivity. Qed.
    Example exp_3 : exp three two = plus (mult two (mult two two)) one.
    Proof. reflexivity. Qed.

    Compute three nat S O.
  End Church.
End Exercises.

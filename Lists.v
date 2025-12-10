From LF Require Export Induction.
From LF Require Export Basics.

From Stdlib Require Import String.

Module NatList.

  Inductive natprod : Type :=
    | pair (n1 n2 : nat).

  Check (pair 2 4) : natprod.

  Definition fst (p: natprod) : nat :=
    match p with 
      | pair x y => x
    end.

  Definition snd (p : natprod ) : nat :=
    match p with 
      | pair x y => y
    end.

  Compute (fst ( pair 3 5)).

  Definition swap_pair(p : natprod ) : natprod :=
    match p with 
      | pair x y => pair y x
    end.

  Compute swap_pair(pair 3 5).

  Theorem surjective_pairing' : forall (n m : nat),
    pair n m = pair (fst(pair n m)) (snd (pair n m)).
  Proof.
    reflexivity. 
  Qed.

  Theorem surjective_pairing : forall (p: natprod),
    p = pair (fst p) (snd p).
  Proof.
    intros p.
    destruct p as [ n m].
    simpl. 
    reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod ),
    pair (snd p) (fst p) = swap_pair p.
  Proof.
    intros p.
    destruct p as [ n m].
    reflexivity.
  Qed.

  Theorem fst_swap_is_snd : forall (p : natprod),
    fst ( swap_pair p) = snd p.
  Proof.
    intros p.
    destruct p as [n m].
    reflexivity.
  Qed.



  (* LISTS OF NUMBERS *)

  (* A LIST IS EITHER THE EMPTY LIST OR ELSE A PAIR OF A NUMBER AND ANOTHER LIST. *)

  Inductive natlist : Type :=
    | nil 
    | cons ( n : nat ) (l : natlist ).

  Definition mylist := cons 1 ( cons 2 ( cons 3 nil)).

  Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..). 

  Definition mylist1 := 1 :: ( 2 :: ( 3 :: nil)).
  Definition mylist2 := 1 :: 2 :: 3 :: nil.
  Definition mylist3 := [1;2;3].

  Notation "x + y" := (plus x y) (at level 50, left associativity).


  (* Functions for Constructing and Manipulating lists. *)

  (* REPEAT *)
  Fixpoint repeat (n count : nat ) : natlist :=
    match count with 
      | O => nil
      | S count' => n :: (repeat n count')
    end.

  (* LENGTH *)
  Fixpoint length (l : natlist) : nat :=
    match l with 
      | nil => O 
      | h :: t => S ( length t)
    end.

  (* APPEND *)
  Fixpoint app ( l1 l2 : natlist ) : natlist :=
    match l1 with 
      | nil => l2
      | h :: t => h :: ( app t l2)
    end.

  Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

  Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.
  Example test_app2: nil ++ [4;5] = [4;5].
  Proof. reflexivity. Qed.
  Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof. reflexivity. Qed.

  (* HEAD AND TAIL *)
  Definition hd (default : nat ) ( l : natlist ) : nat :=
    match l with 
      | nil => default
      | h :: t => h 
    end.

  Definition tl (l : natlist ) : natlist :=
    match l with 
      | nil => nil  
      | h :: t => t 
    end.

  Example test_hd1 : hd 0 [ 1;2;3] =1.
  Proof. reflexivity. Qed.
  Example test_hd2 : hd 0 [] = 0.
  Proof. reflexivity. Qed.
  Example test_hd3 : hd 5 [] = 5.
  Proof. reflexivity. Qed.
  Example test_hd4 : hd 5 [] = 5.
  Proof. reflexivity. Qed.
  Example test_tl1 : tl [] = nil.
  Proof. reflexivity. Qed.
  Example test_tl2 : tl [1;2;3] = [2;3].
  Proof. reflexivity. Qed.


  Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | nil => nil
    | cons O x0 => nonzeros x0
    | cons x x0 => x :: nonzeros x0
  end.

  Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity.  Qed.
  
  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
      | nil => nil
      | cons x x0 =>
        if even x then oddmembers x0 else x :: oddmembers x0
    end.
  
  Example test_oddmembers:            oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity.  Qed.
  
  Fixpoint countoddmembers (l:natlist) : nat :=
    length (oddmembers l).
  
  Example test_countoddmembers1:    countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity.  Qed.
  Example test_countoddmembers2:    countoddmembers [0;2;4] = 0.
  Proof. reflexivity.  Qed.
  Example test_countoddmembers3:    countoddmembers nil = 0.
  Proof. reflexivity.  Qed.
  
  
  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
      | nil => l2
      | cons x x0 =>
        match l2 with
          | nil => l1
          | cons y y0 => x :: y :: alternate x0 y0
        end
    end.
  
  Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity.  Qed.
  Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity.  Qed.
  Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity.  Qed.
  Example test_alternate4:        alternate [] [20;30] = [20;30].
  Proof. reflexivity.  Qed.

(* ###################################################### *)
(** ** Bags via Lists *)

  (* BAGS VIA LISTS *)
  Definition bag := natlist.
  
  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => 0
    | h :: t =>
        if v =? h then 1 + count v t
        else count v t
    end.
  
  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. reflexivity. Qed.
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.
  
  Definition sum (s1 s2 : bag) : bag :=
    s1 ++ s2.
  
  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.
  
  Definition add (v : nat) (s : bag) : bag :=
    v :: s.
  
  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.
  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.
  
  Fixpoint member (v : nat) (s : bag) : bool :=
    match s with
    | nil => false
    | h :: t =>
        if v =? h then true
        else member v t
    end.
  
  Example test_member1: member 1 [1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_member2: member 2 [1;4;1] = false.
  Proof. reflexivity. Qed.
  
  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
    | nil => nil
    | h :: t =>
        if v =? h then t
        else h :: remove_one v t
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
  
  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t =>
        if v =? h then remove_all v t
        else h :: remove_all v t
    end.
  
  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.
  
  Fixpoint included (s1 : bag) (s2 : bag) : bool :=
    match s1 with
    | nil => true
    | h :: t =>
        if member h s2
        then included t (remove_one h s2)
        else false
    end.
  
  Example test_included1: included [1;2] [2;1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_included2: included [1;2;2] [2;1;4;1] = false.
  Proof. reflexivity. Qed.


  (* REASONING ABOUT LISTS *)

  Theorem nil_app : forall l :natlist,
    [] ++ l = l.
  Proof. reflexivity. Qed.

  Theorem app_nil_r : forall l : natlist,
    l ++ [] = l.
  Proof.
    induction l as [| n l' IHl'].
    - reflexivity. 
    - simpl.             
      rewrite -> IHl'.   
      reflexivity.
  Qed.

  Theorem tl_length_pred : forall l : natlist,
    pred (length l) = length (tl l).
  Proof.
    intros l.
    destruct l as [| n l'].
    - reflexivity.
    - simpl. reflexivity. 
  Qed.

  (* INDUCTION ON LISTS *)

  (* If we have in mind some proposition P that mentions a list l and we want to argue that P holds for ALL lists, we can reason as : 

  - First, show that P is true of l when l is nil.
  - Then show that P is true of l whne l is cons n l' for some number n and some smaller list l', assuming that P is true for l'

  *)

  Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. 
    induction l1 as [ | n l1' IHl1'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
  Qed.


  Theorem repeat_double_firsttry : forall c n : nat,
    repeat n c ++ repeat n c  = repeat n ( c + c).
  Proof.
    intros c.
    induction c as [| c' IHc'].
    - reflexivity.
    - intros n. simpl.
  Abort.


  (* 
  if we are stuck in a proof, we should try to prove a stronger statement, 
  quick trick : make the proof liberal enough to work on arbitrary second command 
  *)
  Theorem repeat_plus : forall c1 c2 n : nat,
    repeat n c1 ++ repeat n c2 = repeat n ( c1 + c2).
  Proof.  
    intros c1 c2 n.
    induction c1 as [ | c1' IHc1'].
    - simpl. reflexivity.
    - simpl. 
      rewrite <- IHc1'.
      reflexivity.
  Qed.

  Fixpoint rev (l:natlist) : natlist :=
    match l with 
      | nil => nil  
      | h :: t => rev t ++ [h]
    end.

  Example test_rev_1 : rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev_2 : rev nil = nil.
  Proof. reflexivity. Qed.


  Theorem rev_length_firsttry : forall l : natlist,
    length (rev l) = length l.
  Proof.
    intros l.
    induction l as [ | n l' IHl'].
    - reflexivity.
    - simpl. rewrite <- IHl'.
  Abort.

  Theorem app_rev_length_S_firsttry : forall l n,
    length (rev l ++ [n]) = S (length (rev l)).
  Proof.
    intros l.
    induction l as [| m l' IHl'].
    - intros n. simpl. reflexivity.
    - intros n. simpl.
  Abort.

  Theorem app_length_S : forall l n,
    length ( l ++ [n]) = S ( length l).
  Proof.
    intros l n.
    induction l as [ | m l' IHl'].
    - simpl. reflexivity.
    - simpl. 
      rewrite IHl'. 
      reflexivity.
  Qed.

  Theorem rev_length : forall l : natlist,
    length ( rev l) = length l.
  Proof.
    intros l. induction l as [ | n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite -> app_length_S.
      rewrite IHl'.
      reflexivity.
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2. induction l1 as [ | n l1' IHl1'].
    - simpl. reflexivity.
    - simpl. 
      rewrite -> IHl1'. 
      reflexivity.
  Qed.


  Theorem rev_app_distr: forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
  Qed.
  
  Theorem rev_involutive : forall l : natlist,
    rev (rev l) = l.
  Proof.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite -> rev_app_distr.
      rewrite -> IHl'.
      reflexivity.
  Qed.
  
  Theorem rev_injective : forall l1 l2 : natlist,
    rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H.
    rewrite <- (rev_involutive l1).
    rewrite <- (rev_involutive l2).
    rewrite -> H.
    reflexivity.
  Qed.

  Search rev.

  Search (_ + _ = _ + _) inside Induction.

  (* ------------ OPTIONS ------------- *)
  Fixpoint nth_bad ( l : natlist ) (n : nat) : nat :=
    match l with 
      | nil => 42
      | a :: l' => match n with 
                    | 0 => a 
                    | S n' => nth_bad l' n' 
                  end
    end.

  Inductive natoption : Type :=
    | Some( n : nat)
    | None.

  Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
    match l with 
      | nil => None 
      | a :: l' => match n with 
                    | O => Some a 
                    | S n' => nth_error l' n'
                    end 
      end.

  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.
  Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
  Proof. reflexivity. Qed.
  Example test_nth_error3 : nth_error [4;5;6;7] 19 = None.
  Proof. reflexivity. Qed.

  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with 
      | Some n' => n'
      | None => d 
      end.

  Definition hd_error (l : natlist) : natoption :=
    match l with 
      | nil => None
      | a :: l' => Some a 
      end.


  Example test_hd_error1 : hd_error [] = None.
  Proof. reflexivity. Qed.

  Example test_hd_error2 : hd_error [1] = Some 1.
  Proof. reflexivity. Qed.
  Example test_hd_error3 : hd_error [5;6] = Some 5.
  Proof. reflexivity. Qed.

  (* Theorem option_elim_hd : forall (l : natlist) (default :nat),
    hd default l = option_elim default (hd_error l).
  Proof. *)

  Theorem eqb_refl : forall n : nat, n =? n = true.
    Proof.
      intros n.
      induction n as [| n' IHn'].
      - simpl. reflexivity.
      - simpl.
        rewrite -> IHn'.
        reflexivity.
    Qed.

(* -------- PARTIAL MAPS ---------- *)

  Inductive id : Type :=
    | Id ( n : nat).
    
  Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => n1 =? n2
    end.

  Theorem eqb_id_refl : forall x, eqb_id x x = true.
  Proof.  
    intros x.
    destruct  x as [n].
    simpl.
    rewrite eqb_refl.
    reflexivity.
  Qed.

End NatList.

Module PartialMap.
  Export NatList.

  Inductive partial_map : Type :=
    | empty 
    | record (i : id)(v : nat)(m: partial_map).

  Definition update ( d : partial_map)
                    ( x : id) (value : nat)
                    : partial_map :=
    record x value d.

  Fixpoint find ( x : id)(d : partial_map) : natoption :=
    match d with  
      | empty => None 
      | record y v d' => if eqb_id x y 
                          then Some v 
                          else find x d'
  end.

  Theorem update_eq : 
    forall (d : partial_map) (x : id )(v :nat),
            find x (update d x v) = Some v.
  Proof.
    intros d.
    destruct x as [n].
    simpl.
    rewrite eqb_refl.
    reflexivity.
  Qed.

  Theorem update_neq : 
    forall (d : partial_map) ( x y : id) (o : nat),
            eqb_id x y = false -> find x (update d y o) = find x d.
  Proof.
    intros d x y o H_neq.
    simpl. 
    rewrite H_neq.
    reflexivity.
  Qed.
End PartialMap.
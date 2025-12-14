From LF Require Export Basics.
From Stdlib Require Export String.


Theorem add_0_r_firsttry: forall n:nat,
  n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n.
  destruct n as [ | n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem add_0_r : forall n:nat, n+0 = n.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. simpl. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S ( n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  
Qed.

Theorem add_comm : forall n m : nat, 
  n + m = m + n.
Proof.
  intros n m.
  induction m as [ | m' IHm'].
  - simpl. rewrite -> add_0_r. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite <- IHm'. simpl. reflexivity.  
Qed.

Theorem add_assoc : forall n m p : nat,
  n + ( m + p) = (n + m ) + p.
Proof.
  intros n m p.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. 
Qed.

Fixpoint double ( n : nat) := 
  match n with
  | O => O
  | S n' => S ( S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.  
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. simpl. reflexivity.  
Qed.


Theorem eqb_refl : forall n : nat,
  ( n =? n ) = true.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem even_S : forall n : nat,
  even ( S n) = negb ( even n).
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.  
Qed. 

(*  ------------------- PROOFS WITHIN PROOFS ----------------------- *)

Theorem mult_0_plus' : forall n m : nat,
  (n +0 + 0) * m = n * m.
Proof.  
  intros n m.
  replace (n+0+0) with n.
  - reflexivity.
  - rewrite add_comm. simpl. rewrite add_comm. reflexivity.
Qed.  

Theorem pluse_rearrange_firsttry : forall n m p q : nat,
  (n + m) + ( p + q) = ( m + n)+(p + q).
Proof.
  intros n m p q.
  rewrite add_comm.
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m)+(p + q) = (m + n)+(p+q).
Proof.
  intros n m p q.
  replace ( n + m) with ( m + n).
  - reflexivity.
  - rewrite add_comm. reflexivity.
Qed.


Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  replace (n + (m + p)) with ((n + m) + p).
  {
    replace (n + m) with (m + n).
    {
      rewrite add_assoc.
      reflexivity.
    }
    {
      rewrite add_comm.
      reflexivity.
    }
  }
  {
    rewrite <- add_assoc. 
    reflexivity.
  }
Qed.

Lemma mul_succ_r : forall n m : nat,
  n * (S m) = n + n * m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite add_assoc.
    rewrite add_assoc.
    rewrite (add_comm m n').
    reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m*n = n*m.
Proof.
  intros n m.
  induction n as [ | n' IHn'].
  - simpl. rewrite mult_0_r. reflexivity.
  - simpl. rewrite mul_succ_r. rewrite IHn'. reflexivity.
Qed.


Theorem leb_refl : forall n : nat,
  ( n <=? n) = true.
Proof.
  intros n.
  induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_neqb_S: forall n:nat,
  0=? (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b as [|] eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0: forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.  

Theorem mult_1_l : forall n : nat, 
  1*n = n.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - simpl. reflexivity.
  - simpl. rewrite add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
    = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl. 
    destruct c eqn:Ec.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity. 
Qed.  



Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m)*p = (n*p)+(m*p).
Proof.
  intros n m p.
  induction n as [ |n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite add_assoc. reflexivity.
Qed.


Theorem mult_assoc : forall n m p: nat, 
  n*(m*p) = (n*m)*p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl.  rewrite IHn'. rewrite mult_plus_distr_r. reflexivity.
Qed.  

Fixpoint incr ( m : bin) : bin :=
  match m with 
  | Z => B1 Z 
  | B0 n' => B1 n'
  | B1 n' => B0 ( incr n') 
  end.

Fixpoint bin_to_nat ( m : bin ) : nat :=
  match m with 
  | Z => O 
  | B0 n' => plus (bin_to_nat n') (bin_to_nat n')
  | B1 n' => S ( plus (bin_to_nat n') (bin_to_nat n'))
  end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [| n' IHn' | n' IHn'].
  
  - simpl.
    reflexivity.
    
  - simpl.
    reflexivity.

  - simpl.
    rewrite IHn'.
    simpl.
    rewrite <- plus_n_Sm.
    simpl.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Example test_nat_to_bin1 : (nat_to_bin 2) = B0 ( B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_nat_to_bin2 : (nat_to_bin 3) = B1 ( B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_nat_to_bin3 : (nat_to_bin O) = Z.
Proof. simpl. reflexivity. Qed.


Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. 
    reflexivity.
  - simpl.
    rewrite bin_to_nat_pres_incr.
    rewrite IHn'.
    reflexivity.
Qed.


Lemma double_incr : forall n : nat, double ( S n) = S ( S ( double n) ).
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Definition double_bin ( b : bin) : bin :=
  match b with 
  | Z => Z 
  | _ => B0 b 
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. simpl. reflexivity. Qed.

Lemma double_incr_bin : forall b,
  double_bin ( incr b) = incr ( incr ( double_bin b)).
Proof.
  intros b.
  induction b as [| b' IHb' | b' IHb'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fixpoint normalize ( b: bin) : bin :=
  match b with
  | Z => Z 
  | B1 n' => B1 ( normalize n')
  | B0 n' => double_bin(normalize n')
  end.

Example normalize_zero : normalize ( B0 Z) = Z.
Proof.
  simpl. reflexivity.
Qed.

Example normalize_zero_deep : normalize (B0 (B0 Z)) = Z.
Proof.
  simpl. reflexivity.
Qed.

Example normalize_no_op : normalize (B1 (B0 (B1 Z))) = B1 (B0 (B1 Z)).
Proof.
  simpl. reflexivity.
Qed.



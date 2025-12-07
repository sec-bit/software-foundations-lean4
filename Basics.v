Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day ( d: day) : day := 
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday 
  | saturday => monday
  | sunday => monday
  end.

Compute (next_working_day friday).

Compute (next_working_day (next_working_day saturday)).

Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
Proof. simpl. reflexivity.  Qed.

From Stdlib Require Export String.

Inductive bool: Type :=
 | true
 | false.

Definition negb (b: bool) : bool :=
  match b with 
  | true => false
  | false => true
  end .

Definition andb (b1: bool) (b2: bool) : bool := 
 match b1 with
 | true => b2
 | false => false
 end.

Definition orb (b1: bool) (b2: bool) : bool := 
 match b1 with 
 | true => true
 | false => b2
 end.

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (a: bool) : bool :=
 if a then false
 else true.

Definition andb' (a: bool) (b: bool) : bool := 
 if a then b
 else false.

Definition orb' (a: bool) (b: bool) : bool :=
 if a then true
 else b.

Inductive bw : Type :=
  | bw_black
  | bw_white.

Definition invert (x: bw) : bw :=
  if x then bw_white
  else bw_black.

Compute (invert bw_black).
Compute (invert bw_white).

Inductive bwr : Type :=
  | bwr_black
  | bwr_white
  | bwr_red.

Definition rotate(x: bwr) : bwr := 
  match x with 
  | bwr_black => bwr_white
  | bwr_white => bwr_red
  | bwr_red => bwr_black
  end.

Compute (rotate bwr_white).

Definition nandb (b1:bool) (b2:bool) : bool := 
  negb( andb b1 b2).

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with 
  | true => match b2 with 
            | true => match b3 with 
                      | true => true 
                      | false => false 
                      end
            | false => false 
            end
  | false => false 
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check true
  : bool.

Check (negb true)
  : bool.

Check negb.

Check negb
  : bool -> bool.

Check andb
  : bool -> bool -> bool.

Inductive rgb : Type :=
  | red 
  | green
  | blue.

Inductive color : Type :=
  | black
  | white 
  | primary ( p : rgb).

Definition monochrome (c: color) : bool := 
  match c with 
  | black => true
  | white => true 
  | primary p => false 
  end.
  
Compute (monochrome (primary red)).

Example test_monochrome1  : ( monochrome (primary red ) = false).
Proof. simpl. reflexivity. Qed.
Example test_monochrome2 : (monochrome black ) = true.
Proof. simpl. reflexivity. Qed.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module Playground.
  Definition foo : rgb := blue. 
End Playground.

Definition foo : bool := true.

Check Playground.foo.
Check foo.

Module TuplePlayground.

  Inductive bit : Type :=
  | B1 
  | B0.

  Inductive nybble : Type :=
  | bits ( b0 b1 b2 b3 : bit).

  Check (bits B1 B0 B1 B0).

  Definition all_zero( nb : nybble) : bool :=
    match nb with 
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false 
    end.

  Compute (all_zero (bits B1 B0 B1 B0)).
  Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.

Module NatPlayground.

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

Inductive nat : Type := 
  | O  
  | S ( n : nat ).

Print nat_ind.

Definition pred ( n : nat ) : nat := 
  match n with 
  | O => O 
  | S n' => n' 
  end.

End NatPlayground.

Check ( S ( S ( S ( S (0))))).

Definition minustwo ( n : nat ) : nat :=
  match n with 
  | O => O 
  | S O => O 
  | S ( S n' ) => n'
  end. 

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint even( n : nat ) : bool :=
  match n with 
  | O => true
  | S O => false 
  | S ( S n') => even n'
  end.




Definition odd ( n : nat ) : bool :=
  negb ( even n).

Example test_odd1 : odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd2 : odd 4 = false.
Proof. simpl. reflexivity. Qed.

Example test_even1 : even 3 = false.
Proof. simpl. reflexivity. Qed.

Example test_even2 : even 6 = true.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

  Fixpoint plus ( n : nat ) ( m : nat ) : nat :=
    match n with 
    | O => m
    | S n' => S ( plus n' m)
    end.

  Compute (plus 3 2).
  
  Fixpoint mult ( n m : nat ) : nat :=
    match n with 
    | O => O 
    | S n' => plus m ( mult n' m)
    end.

  Example test_mult1 : (mult 3 3 ) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus ( n m : nat ) : nat := 
    match n, m with 
    | O, _ => O 
    | S _ , O => n
    | S n' , S m' => minus n' m'
    end.

  End NatPlayground2.

  Fixpoint exp ( base power : nat ) : nat :=
    match power with 
    | O => S O 
    | S p => mult base ( exp base p)
    end.
  
  Example test_exp1 : (exp 3 5)  = 243.
  Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with 
  | O => S O 
  | S n' => mult n (factorial n')
  end.

Example test_factorial1:          (factorial 3) = 6.
  Proof. simpl. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
  Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      :nat_scope.

Check ( (0 + 1) + 1).

Fixpoint eqb(n m : nat) : bool := 
  match n with 
  | O => match m with 
          | O => true 
          | S m' => false 
          end
  | S n' => match m with 
              | O => false 
              | S m' => eqb  n' m' 
              end 
  end. 

Fixpoint leb (n m : nat) : bool :=
  match n with 
  | O => true
  | S n' => match m with 
              | O => false 
              | S m' => leb n' m'
            end
  end.

Fixpoint lb ( n m : nat ) : bool :=
  match n with 
  | O => match m with 
          | O => false 
          | S m' => true 
          end 
  | S n' => match m with 
            | O => false 
            | S m' => lb n' m'
            end 
  end.

Example test_lb1:                lb 2 2 = false.
Proof. simpl. reflexivity.  Qed.
Example test_lb2:                lb 2 4 = true.
Proof. simpl. reflexivity.  Qed.
Example test_lb3:                lb 4 2 = false.
Proof. simpl. reflexivity.  Qed.

Example test_leb1:                leb 2 2 = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:                leb 2 4 = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:                leb 4 2 = false.
Proof. simpl. reflexivity.  Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity.  Qed.

Definition ltb (n m : nat) : bool :=
  leb (S n) m.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2:             (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3:             (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed. 

Example plus_1_1 : 1 + 1 = 2.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity.  Qed.

Theorem plus_id_example : forall n m: nat,
  n = m ->
  n + n = m + m.

Proof. 
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Check mult_n_O.

Check mult_n_Sm.

    Theorem mult_n_0_m_0 : forall p q : nat,
    (p * 0) + (q * 0) = 0.
  Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    reflexivity. Qed.
  
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. 
Abort.

Theorem plus_1_neq_O : forall n : nat,
  (n+1) =? 0 = false.
Proof.
  intros n.
  destruct n as [ | n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb ( negb b ) = b.
Proof.
  intros b.
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb ( andb b c ) d = andb ( andb b d) c.
Proof.
  intros b c d. 
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
    + destruct d eqn:Eq.
      * reflexivity.
      * reflexivity.
  - destruct c eqn: Ec.
    + destruct d eqn:Ed.
      * reflexivity.
      * reflexivity.
    + destruct d eqn:Ed. 
      * reflexivity.
      * reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct b eqn:Eb. 
  - simpl in H. rewrite <- H. reflexivity.
  - simpl in H. 
    destruct c eqn:Ec.
      + reflexivity.
      + rewrite <- H. reflexivity. 
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  ( n + 1 ) =? 0 = false.
Proof.
  intros [ |n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'': forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [ |n].
  - reflexivity.
  - reflexivity.
Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

Definition pred(n : nat) : nat :=
  match n with 
  | O => O 
  | S n' => n'
  end.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall ( x : bool), f x = x) -> 
  forall ( b : bool), f ( f b) = b. 
Proof.
  intros f H b.
  rewrite -> H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f: bool -> bool),
  (forall (x: bool), f x = negb x) ->
  forall (b: bool), f ( f b ) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool), 
  (andb b c = orb b c) -> 
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b eqn:Eb.
  - simpl in H. rewrite -> H. reflexivity.
  - simpl in H. rewrite -> H. reflexivity.
Qed.

Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Inductive comparison : Type :=
  | Eq 
  | Lt 
  | Gt.

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Compute letter_comparison B A.

Compute letter_comparison D D.

Compute letter_comparison B F.

Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  intros l.
  destruct l.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
  
Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with 
  | (Grade l1 m1), (Grade l2 m2) =>
    match (letter_comparison l1 l2) with 
    | Gt => Gt
    | Lt => Lt
    | Eq => match m1, m2 with 
            | Plus, Plus => Eq
            | Plus, _ => Gt
            | Natural, Plus => Lt
            | Natural, Natural => Eq
            | Natural, _ => Gt
            | Minus, (Plus | Natural ) => Lt
            | Minus, Minus => Eq 
            end 
    end 
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. reflexivity. Qed.

Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. reflexivity. Qed.

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. reflexivity. Qed.

Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. reflexivity. Qed.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F 
  end.

Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. 
Abort.

Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l H.
  destruct l.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  -  reflexivity.
  - simpl in H.
    simpl.
    rewrite H.
    reflexivity.
Qed.

Definition lower_grade (g : grade) : grade :=
  match g with 
  | Grade l m =>
    match m with 
    | Plus => Grade l Natural
    | Natural => Grade l Minus
    | Minus => match l with 
                | F => Grade F Minus
                | _ => Grade (lower_letter l) Plus
                end
    end 
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
  reflexivity.
Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
  reflexivity.
Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
  reflexivity.
Qed.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
  reflexivity.
Qed.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
  reflexivity.
Qed.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
  reflexivity.
Qed.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
  reflexivity.
Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof.
  reflexivity.
Qed.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
  intros g H.
  destruct g as [ l m ] eqn:Eg.
  destruct m eqn:Em.
  - destruct l.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct l.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct l.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + rewrite lower_grade_F_Minus.
      rewrite H.
      reflexivity.
Qed.

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g  else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof.
  intros late_days g H.
  rewrite apply_late_policy_unfold.
  rewrite H.
  reflexivity.
Qed.

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
  intros late_days g H_lt9 H_lt17.
  rewrite apply_late_policy_unfold.
  rewrite H_lt9.
  rewrite H_lt17.
  reflexivity.
Qed.
End LateDays.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with 
  | Z => B1 Z 
  | B0 n' => B1 n'
  | B1 n' => B0 ( incr n')
  end.


Fixpoint bin_to_nat (m:bin) : nat :=
  match m with 
  | Z => O 
  | B0 n' => plus (bin_to_nat n') ( bin_to_nat n')
  | B1 n' => S (plus (bin_to_nat n') (bin_to_nat n'))
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
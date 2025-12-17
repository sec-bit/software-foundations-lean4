import «Poly»
import Basics
import Lean


-- THE APPLY TACTIC

theorem silly1 : forall (n m : nat), n = m -> n = m := by
  intro n m eq
  apply eq

theorem silly2 : forall (n m o p : Nat),
  n = m -> (n = m -> [n,o]=[m,p]) -> [n,o]=[m,p] := by
  intro n m o p eq1 eq2
  apply eq2
  apply eq1

theorem silly2a : forall (n m : Nat),
  (n, n) = (m, m) ->
  (forall (q r : Nat), (q, q) = (r, r) -> [q] = [r]) ->
  [n] = [m] := by
  intro n m eq1 eq2
  apply eq2
  apply eq1

theorem silly_ex : forall p : Nat,
  (forall n, even n = true -> even (Nat.succ n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (Nat.succ p) = true := by
  intro p h1 h2 hp
  apply h2
  apply h1
  exact hp

theorem silly3 : forall (n m : Nat),
  n = m ->
  m = n := by
  intro n m h
  exact h.symm
theorem rev_exercise1 : forall (l l' : List Nat),
  l = List.reverse l' ->
  l' = List.reverse l := by
  intro l l' h
  rw[h]
  apply Eq.symm
  exact List.reverse_reverse l'

--  THE APPLY WITH TACTIC

theorem trans_eq_example : forall (a b c d e f : Nat),
  [a, b] = [c, d] ->
  [c, d] = [e, f] ->
  [a, b] = [e, f] := by
  intro a b c d e f h1 h2
  rewrite [h1]
  exact h2

theorem trans_eq : forall {X : Type} (x y z : X),
  x = y -> y = z -> x = z := by
  intro X x y z h1 h2
  rewrite [h1]
  exact h2

theorem trans_eq_example' : forall (a b c d e f : Nat),
  [a, b] = [c, d] ->
  [c, d] = [e, f] ->
  [a, b] = [e, f] := by
  intro a b c d e f h1 h2
  -- Coq: apply trans_eq with (y := [c; d]).
  apply trans_eq (X := List Nat) (x := [a, b]) (y := [c, d]) (z := [e, f])
  · exact h1
  · exact h2

theorem trans_eq_example'' : forall (a b c d e f : Nat),
  [a, b] = [c, d] ->
  [c, d] = [e, f] ->
  [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  apply trans_eq (y := [c, d])
  · exact eq1
  · exact eq2

theorem trans_eq_exercise : forall (n m o p : Nat),
  m = minustwo o ->
  (n + p) = m ->
  (n + p) = (minustwo o) := by
  intro n m o p h hm
  apply Eq.trans hm h

-- THE INJECTION AND DISCRIMINATE TACTICS

theorem S_injective : forall (n m : Nat),
  Nat.succ n = Nat.succ m ->
  n = m := by
  intro n m h1
  have h2 : n = Nat.pred (Nat.succ n) := by rfl
  rewrite [h2]
  rewrite [h1]
  simp

theorem S_injective' : forall (n m : Nat),
  Nat.succ n = Nat.succ m ->
  n = m := by
  intro n m h
  cases h
  rfl

theorem injection_ex1 : forall (n m o : Nat),
  ([n, m] : List Nat) = [o, o] ->
  n = m := by
  intro n m o h
  cases h
  rfl

theorem injection_ex3 :
  forall (X : Type) (x y z : X) (l j : List X),
    x :: y :: l = z :: j ->
    j = z :: l ->
    x = y := by
  intro X x y z l j h hj
  cases h
  -- now z := x and j := y :: l
  -- hj : y :: l = x :: l
  cases hj
  rfl

theorem discriminate_ex1 : forall (n m : Nat),
  (false = true) ->
  n = m := by
  intro n m h
  cases h

theorem discriminate_ex2 : forall (n : Nat),
  Nat.succ n = 0 ->
  2 + 2 = 5 := by
  intro n h
  cases h

theorem discriminate_ex3 :
  forall (X : Type) (x y z : X) (l _j : List X),
    x :: y :: l = [] ->
    x = z := by
  intro X x y z l j h
  cases h

theorem eqb_0_l : forall n,
  (0 =? n) = true -> n = 0 := by
  intro n
  cases n with
  | zero =>
      intro h
      rfl
  | succ n' =>
      intro h
      cases h

theorem f_equal :
  forall {A B : Type} (f : A -> B) (x y : A),
    x = y -> f x = f y := by
  intro A B f x y h
  cases h
  rfl

theorem eq_implies_succ_equal : forall (n m : Nat),
  n = m -> Nat.succ n = Nat.succ m := by
  intro n m h
  apply f_equal Nat.succ
  exact h

theorem eq_implies_succ_equal' : forall (n m : Nat),
  n = m -> Nat.succ n = Nat.succ m := by
  intro n m h
  rw[h]

-- USING TACTICS ON HYPOTHESES

theorem S_inj : forall (n m : Nat) (b : Bool),
  ((Nat.succ n =? Nat.succ m) = b) ->
  ((n =? m) = b) := by
  intro n m b h
  dsimp at h
  exact h
  -- simpa using h -- ( works perfectly fine)

theorem silly4 : forall (n m p q : Nat),
  (n = m -> p = q) ->
  m = n ->
  q = p := by
  intro n m p q eq h
  have h' : n = m := h.symm
  have hpq : p = q := eq h'
  exact hpq.symm

theorem silly4' : forall (n m p q : Nat),
  (n = m -> p = q) ->
  m = n ->
  q = p := by
  intro n m p q eq h
  exact (eq h.symm).symm

/- SPECIALIZING HYPOTHESES -/

theorem specialize_example : forall n,
  (forall m, m * n = 0) ->
  n = 0 := by
  intro n h
  -- have h1 : 1 * n = 0 := h 1   -- > this works as well, just tried to make it more coq native
  -- specialize h 1  --> and this as well, but lean allows to pass arguments directly to h as well
  simpa [Nat.one_mul] using (h 1)

theorem trans_eq_example''' : forall (a b c d e f : Nat),
  [a, b] = [c, d] ->
  [c, d] = [e, f] ->
  [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  exact trans_eq _ _ _ eq1 eq2

-- VARYING THE INDUCTION HYPOTHESIS

def double (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ n' => Nat.succ (Nat.succ (double n'))

theorem double_injective : ∀ n m : Nat, double n = double m → n = m := by
  intro n m
  revert n
  induction m with
  | zero =>
      intro n h
      cases n with
      | zero => rfl
      | succ n' => cases h
  | succ m' ih =>
      intro n h
      cases n with
      | zero => cases h
      | succ n' =>
          have hs :
              Nat.succ (Nat.succ (double n')) =
              Nat.succ (Nat.succ (double m')) := by
            simpa [double] using h
          have h1 : Nat.succ (double n') = Nat.succ (double m') :=
            Nat.succ.inj hs
          have h2 : double n' = double m' :=
            Nat.succ.inj h1
          have hn : n' = m' := ih n' h2
          rw[hn]

theorem plus_n_n_injective : forall n m : Nat, n + n = m + m -> n = m := by
  intro n
  induction n with
  | zero =>
    intro m h
    cases m
    · rfl
    · contradiction -- 0 = succ... impossible
  | succ n' ih =>
    intro m h
    cases m with
    | zero => contradiction
    | succ m' =>
      rw [Nat.succ_add, Nat.succ_add] at h
      injection h with h
      injection h with h
      specialize ih m' h
      rw [ih]

theorem double_injective_take2 : forall n m, double n = double m -> n = m := by
  intro n m h
  -- "generalizing n" replaces "generalize dependent n"
  induction m generalizing n with
  | zero =>
    cases n
    · rfl
    · contradiction
  | succ m' ih =>
    cases n with
    | zero => contradiction
    | succ n' =>
      dsimp [double] at h
      injection h with h
      injection h with h
      specialize ih n' h
      rw [ih]

theorem nth_error_after_last :
    forall (n : Nat) (X : Type) (l : List X),
      List.length l = n ->
      nth_error l n = none := by
  intro n X l hlen
  revert n
  induction l with
  | nil =>
      intro n hlen
      cases n with
      | zero =>
          simp [nth_error] at *
      | succ n' =>
          have : (0 : Nat) = Nat.succ n' := by simp at hlen
          cases this
  | cons x l' ih =>
      intro n hlen
      cases n with
      | zero =>
          have : Nat.succ (List.length l') = 0 := by simp at hlen
          cases this
      | succ n' =>
          have hlen' : List.length l' = n' := by
            have : Nat.succ (List.length l') = Nat.succ n' := by simpa using hlen
            exact Nat.succ.inj this
          -- nth_error (x::l') (succ n') = nth_error l' n'
          simpa [nth_error] using ih n' hlen'

theorem sub_add_leb : forall n m, (Nat.ble n m) = true -> (m - n) + n = m := by
  intro n
  induction n with
  | zero =>
    intro m h
    simp
  | succ n' ih =>
    intro m h
    cases m with
    | zero =>
      simp [Nat.ble] at h
    | succ m' =>
      rw [Nat.succ_sub_succ]
      rw [Nat.add_succ]
      simp
      rw [ih m' h]

/- UNFOLDING DEFINITIONS -/

def square (n : Nat) : Nat := n * n

theorem mul_succ_r : forall n m : Nat,
  n * (Nat.succ m) = n + n * m := by
  intro n m
  induction n with
  | zero =>
      simp
  | succ n' ih =>
      simp [Nat.mul_succ, Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

theorem mul_comm : forall m n : Nat,
  m * n = n * m := by
  intro m n
  induction m with
  | zero =>
      simp
  | succ m' ih =>
      simp [Nat.succ_mul, ih, mul_succ_r]
      rw[<- ih]
      exact Nat.add_comm (m' * n) n


theorem square_mult : forall n m : Nat, square (n * m) = square n * square m := by
  intro n m
  -- expand square
  unfold square
  calc
    (n * m) * (n * m)
        = n * (m * (n * m)) := by
            simp [Nat.mul_assoc]
    _   = n * ((m * n) * m) := by
            simp [Nat.mul_assoc]
    _   = n * ((n * m) * m) := by
            simp [mul_comm]
    _   = (n * n) * (m * m) := by
            simp [Nat.mul_assoc]


def bar (x : Nat) : Nat :=
  match x with
  | 0 => 5
  | Nat.succ _ => 5

def sillyfun (n : Nat) : Bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false

theorem sillyfun_false : forall n : Nat, sillyfun n = false := by
  intro n
  unfold sillyfun
  cases h1 : (n =? 3) with
  | true =>
      simp
  | false =>
      cases h2 : (n =? 5) with
      | true =>
          simp
      | false =>
          simp

def combine' {X Y : Type} : List X -> List Y -> List (X × Y)
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: combine' xs ys

def split' {X Y : Type} (l : List (X × Y)) : (List X) × (List Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split' t with
      | (lx, ly) => (x :: lx, y :: ly)

theorem combine_split : ∀ X Y (l : List (X × Y)) l1 l2,
  split' l = (l1, l2) →
  combine' l1 l2 = l := by
  intro X Y l
  induction l with
  | nil =>
    intro l1 l2 h
    dsimp [split'] at h
    cases h
    simp [combine']
  | cons p l' ih =>
  intro l1 l2 h
  cases p with
  | mk x y =>
    cases hst : split' l' with
    | mk lx ly =>
      -- extract l1,l2 from h
      have hpair : x :: lx = l1 ∧ y :: ly = l2 := by
        simpa [split', hst] using h

      rcases hpair with ⟨h1, h2⟩
      cases h1
      cases h2

      have ht : combine' lx ly = l' := ih lx ly hst
      simp [combine', ht]

theorem bool_fn_applied_thrice :
    forall (f : Bool -> Bool) (b : Bool),
      f (f (f b)) = f b := by
  intro f b
  cases b <;> cases hff : f false <;> cases hft : f true <;> simp [hff, hft]

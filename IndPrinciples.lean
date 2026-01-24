-- IndPrinciples.lean
-- Induction Principles

import ProofObjects

-- Lean's induction principle for Nat is Nat.rec
#check @Nat.rec

theorem mul_0_r' : ∀ n : Nat, n * 0 = 0 :=
  Nat.rec rfl (fun _ _ => rfl)

-- n + 1 = Nat.succ n is definitional
theorem plus_one_r' : ∀ n : Nat, n + 1 = Nat.succ n :=
  fun _ => rfl

inductive Time : Type where
  | day
  | night

#check @Time.rec

inductive Rgb : Type where
  | red
  | green
  | blue

#check @Rgb.rec

inductive NatList : Type where
  | nnil
  | ncons (n : Nat) (l : NatList)

#check @NatList.rec

inductive NatList' : Type where
  | nnil'
  | nsnoc (l : NatList') (n : Nat)

#check @NatList'.rec

inductive BoolTree : Type where
  | bt_empty
  | bt_leaf (b : Bool)
  | bt_branch (b : Bool) (t1 t2 : BoolTree)

#check @BoolTree.rec

def BoolTreePropertyType : Type := BoolTree → Prop

def base_case (P : BoolTreePropertyType) : Prop :=
  P BoolTree.bt_empty

def leaf_case (P : BoolTreePropertyType) : Prop :=
  ∀ b : Bool, P (BoolTree.bt_leaf b)

def branch_case (P : BoolTreePropertyType) : Prop :=
  ∀ (b : Bool) (t1 : BoolTree), P t1 → ∀ (t2 : BoolTree), P t2 → P (BoolTree.bt_branch b t1 t2)

def BoolTreeIndType : Prop :=
  ∀ (P : BoolTreePropertyType),
    base_case P →
    leaf_case P →
    branch_case P →
    ∀ (t : BoolTree), P t

theorem booltree_ind_type_correct : BoolTreeIndType := by
  intro P hbase hleaf hbranch t
  induction t with
  | bt_empty => exact hbase
  | bt_leaf b => exact hleaf b
  | bt_branch b t1 t2 ih1 ih2 => exact hbranch b t1 ih1 t2 ih2

-- theorem Toy_correct : ∃ f g,
--     ∀ P : Toy → Prop,
--       (∀ b : Bool, P (f b)) →
--       (∀ (n : Nat) (t : Toy), P t → P (g n t)) →
--       ∀ t : Toy, P t :=
--   ⟨Toy.con1, Toy.con2, fun P h1 h2 t => by
--     induction t with
--     | con1 b => exact h1 b
--     | con2 n t ih => exact h2 n t ih⟩

-- -------------------- POLYMORPHISM --------------------

inductive Tree (α : Type) : Type where
  | leaf (x : α)
  | node (t1 t2 : Tree α)

#check @Tree.rec

inductive MyType (α : Type) : Type where
  | constr1 (x : α)
  | constr2 (n : Nat)
  | constr3 (m : MyType α) (n : Nat)

#check @MyType.rec

inductive Foo (α β : Type) : Type where
  | bar (x : α)
  | baz (y : β)
  | quux (f1 : Nat → Foo α β)

#check @Foo.rec

inductive Foo' (α : Type) : Type where
  | C1 (l : List α) (f : Foo' α)
  | C2

#check @Foo'.rec

-- -------------------- INDUCTION HYPOTHESES --------------------

def P_m0r (n : Nat) : Prop := n * 0 = 0

def P_m0r' : Nat → Prop := fun n => n * 0 = 0

theorem mul_0_r'' : ∀ n : Nat, P_m0r n := fun _ => rfl

theorem add_assoc' : ∀ n m p : Nat, n + (m + p) = (n + m) + p := by
  intro n m p
  induction n with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ n' ih => rw [Nat.succ_add, Nat.succ_add, ih, Nat.succ_add]

theorem add_comm' : ∀ n m : Nat, n + m = m + n := by
  intro n
  induction n with
  | zero => intro m; rw [Nat.zero_add, Nat.add_zero]
  | succ n' ih => intro m; rw [Nat.succ_add, Nat.add_succ, ih]

theorem add_comm'' : ∀ n m : Nat, n + m = m + n := by
  intro n m
  induction m with
  | zero => rw [Nat.add_zero, Nat.zero_add]
  | succ m' ih => rw [Nat.add_succ, Nat.succ_add, ih]

def Passoc (n m p : Nat) : Prop := n + (m + p) = (n + m) + p
def Pcomm (n m : Nat) : Prop := n + m = m + n

theorem add_assoc'' : ∀ n m p : Nat, Passoc n m p := by
  intro n m p
  unfold Passoc
  induction n with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ n' ih => rw [Nat.succ_add, Nat.succ_add, ih, Nat.succ_add]

theorem add_comm''' : ∀ n m : Nat, Pcomm n m := by
  intro n
  induction n with
  | zero => intro m; unfold Pcomm; rw [Nat.zero_add, Nat.add_zero]
  | succ n' ih => intro m; unfold Pcomm; rw [Nat.succ_add, Nat.add_succ, ih m]

-- -------------------- INDUCTION PRINCIPLES FOR PROPOSITIONS --------------------

#check @ev.rec

inductive ev' : Nat → Prop where
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum (n m : Nat) : ev' n → ev' m → ev' (n + m)

theorem ev_ev' : ∀ n, ev n → ev' n := by
  intro n h
  induction h with
  | ev_0 => exact ev'.ev'_0
  | ev_SS n' _ ih =>
    rw [Nat.add_comm]
    exact ev'.ev'_sum 2 n' ev'.ev'_2 ih

-- -------------------- PARAMETER VS INDEX --------------------

inductive Le1 : Nat → Nat → Prop where
  | le1_n (n : Nat) : Le1 n n
  | le1_S (n m : Nat) : Le1 n m → Le1 n (m + 1)

notation:50 m " <=1 " n => Le1 m n

inductive Le2 (n : Nat) : Nat → Prop where
  | le2_n : Le2 n n
  | le2_S (m : Nat) : Le2 n m → Le2 n (m + 1)

notation:50 m " <=2 " n => Le2 m n

#check @Le1.rec
#check @Le2.rec

-- -------------------- EXPLICIT PROOF OBJECTS FOR INDUCTION --------------------

#check @Nat.rec

def build_proof
    (P : Nat → Prop)
    (evP0 : P 0)
    (evPS : ∀ n : Nat, P n → P (n + 1))
    (n : Nat) : P n :=
  match n with
  | 0 => evP0
  | k + 1 => evPS k (build_proof P evP0 evPS k)

def nat_ind_tidy := build_proof

-- -------------------- CUSTOM INDUCTION PRINCIPLES --------------------

def even (n : Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | n + 2 => even n

def nat_ind2
    (P : Nat → Prop)
    (P0 : P 0)
    (P1 : P 1)
    (PSS : ∀ n : Nat, P n → P (n + 2))
    (n : Nat) : P n :=
  match n with
  | 0 => P0
  | 1 => P1
  | n' + 2 => PSS n' (nat_ind2 P P0 P1 PSS n')

theorem even_ev : ∀ n, even n = true → ev n := by
  intro n
  induction n using nat_ind2 with
  | P0 => intro _; exact ev.ev_0
  | P1 => intro h; contradiction
  | PSS n' ih =>
    intro h
    exact ev.ev_SS n' (ih h)

-- -------------------- NESTED INDUCTIVE TYPES --------------------

inductive TTree (α : Type) : Type where
  | t_leaf : TTree α
  | t_branch : TTree α → α → TTree α → TTree α

open TTree

def reflect {α : Type} (t : TTree α) : TTree α :=
  match t with
  | t_leaf => t_leaf
  | t_branch l v r => t_branch (reflect r) v (reflect l)


-- Standard induction works fine in Lean for this definition
-- no need for custom `better_t_tree_ind`
theorem reflect_involution : ∀ (α : Type) (t : TTree α), reflect (reflect t) = t := by
  intro α t
  induction t with
  | t_leaf => rfl
  | t_branch l v r ihl ihr => simp [reflect, ihl, ihr]

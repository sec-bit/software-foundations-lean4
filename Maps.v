(** * Maps: Total and Partial Maps *)
(** * The Coq Standard Library *)

From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Export Strings.String.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import List.
Import ListNotations.
Set Default Goal Selector "!".

Locate "+".
Print Init.Nat.add.

(** * Identifiers *)
Check String.eqb_refl.

Check String.eqb_eq.
Check String.eqb_neq.
Check String.eqb_spec.

(** * Total Maps *)

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v:A) :
  total_map A :=
    (fun _ => v).

Definition t_update {A:Type} (m : total_map A) (x:string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Check t_update.

Definition example_map := 
  t_update ( t_update (t_empty false) "foo" true) "bar" true.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).
Example example_empty := (_ !-> false).
Notation "x '!->' v ';' m" := (t_update m x v) (at level 100, v constr at level 100, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.
Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.
Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.
Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(* empty map returns its default element for all keys *)
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A), 
  ( _ !-> v ) x = v.
Proof.
  intros. unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall ( A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 -> 
  (x1 !-> v ; m ) x2 = m x2.
Proof.
  intros. unfold t_update. apply String.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality. intros x'.
  unfold t_update.
  destruct (eqb_spec x x') as [_ | _].
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x; m) = m.
Proof.
  intros.
  unfold t_update.
  apply functional_extensionality.
  intros x'.
  destruct (String.eqb_spec x x').
  - rewrite e. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  apply functional_extensionality.
  intros x'.
  unfold t_update.
  destruct (eqb_spec x1 x') as [H1 | H1].
  - destruct (eqb_spec x2 x') as [H2 | _].
    + exfalso. apply H. rewrite H1. rewrite H2. reflexivity.
    + reflexivity.
  - destruct (eqb_spec x2 x') as [H2 | H2].
    + reflexivity.
    + reflexivity.
Qed.


(* PARTIAL MAPS *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.
  
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 0, x constr, v at level 200, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 0, x constr, v at level 200).

Definition examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros.
  unfold empty.
  rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

#[global] Hint Resolve update_eq : core.

Theorem update_neq : forall ( A : Type ) (m : partial_map A) x1 x2 v,
  x2 <> x1 -> 
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq.
  - reflexivity.
  - apply H.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = ( x |-> v2 ; m).
Proof.
  intros A m x v1 v2.
  unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v -> 
  (x |-> v ; m) = m.
Proof.
  intros A m x v H.
  unfold update.
  rewrite <- H.
  rewrite t_update_same.
  reflexivity.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A) 
                            x1 x2 v1 v2,
  x2 <> x1 -> 
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Definition includedin {A : Type} (m m' : partial_map A) := 
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : forall ( A : Type ) (m m' : partial_map A)
                            (x : string) (vx : A),
  includedin m m' -> 
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vs H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.
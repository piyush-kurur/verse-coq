(** * Modular integers.

The primes that are of the form 2^n - c. We capture elements of this
ring

 *)

Require Import BinInt.
Require Import ZArith.
Require Import NArith.

Definition Modulus := { m : Z | (1 < m)%Z }.
Inductive  Zmod (m : Modulus) := Z2Zmod_raw : Z -> Zmod m.

(* begin hide *)
Arguments Z2Zmod_raw {m}.

Definition Modulus2Z (x : Modulus) :  Z := proj1_sig x.
Definition residue (m : Modulus)(x : Z) := (x mod (Modulus2Z m))%Z.
Definition Z2Zmod {m}(n : Z) : Zmod m := Z2Zmod_raw (residue m n).
(*end hide *)


(* begin hide *)
Lemma Modulus2Z_gt_1 : forall m, (1 < Modulus2Z m)%Z.
  intros;
  destruct m; simpl; trivial.
Qed.

Global Hint Resolve Modulus2Z_gt_1  : Zmod.
Lemma Modulus2Z_gt_0 : forall m, (0 < Modulus2Z m)%Z.
  intros.
  apply (@Z.lt_trans 0 1 _ eq_refl). eauto with Zmod.
Qed.

Global Hint Resolve Modulus2Z_gt_0  : Zmod.
Global Hint Resolve Z.lt_neq : Zmod.

Lemma Modulus2Z_neq_0 : forall m, (Modulus2Z m <> 0)%Z.
  intros.
  apply Z.neq_sym.
  eauto with Zmod.
Qed.

Global Hint Resolve Modulus2Z_neq_0 : Zmod.


Require Import setoid_ring.Algebra_syntax.

Definition Zmod2Z {m}(x : Zmod m) : Z :=
  match x with
  | Z2Zmod_raw n => residue m n
  end.

Instance Zmod_to_Z m : Bracket (Zmod m) Z := Zmod2Z.
Instance Z_to_Zmod m : Bracket Z (Zmod m) := Z2Zmod.


Definition arithm {m} (f : Z -> Z -> Z) : Zmod m -> Zmod m -> Zmod m
  := fun x y => [ f [ x ] [ y ] ].

Definition addZmod {m : Modulus} := @arithm m Z.add.
Definition mulZmod {m : Modulus} := @arithm m Z.mul.
Definition oppZmod {m : Modulus} (x : Zmod m) : Zmod m := [- [x] ]%Z.
Definition subZmod {m : Modulus}(x y : Zmod m) : Zmod m := [ [ x ] - [ y ] ]%Z.
Definition eqZmod {m}(x y : Zmod m) := @eq Z [ x ] [ y ].

Search (Z -> Z -> bool).

Definition eqb_Zmod {m}(x y : Zmod m) : bool := Z.eqb [x] [y].

(* end hide *)

Instance zero_Zmod (m : Modulus) : Zero (Zmod m)       := Z2Zmod_raw 0%Z.
Instance one_Zmod (m : Modulus) : One (Zmod m)         := Z2Zmod_raw 1%Z.
Instance add_Zmod (m : Modulus) : Addition (Zmod m)    := addZmod.
Instance mul_Zmod (m : Modulus) : Multiplication       := @mulZmod m.
Instance sub_Zmod (m : Modulus) : Subtraction (Zmod m) := subZmod.
Instance opp_Zmod (m : Modulus) : Opposite (Zmod m)    := oppZmod.
Instance eq_Zmod  (m : Modulus) : Equality     := @eqZmod m.


(* begin hide *)

Fixpoint pow_nat {m : Modulus}(x : Zmod m) (n : nat) : Zmod m :=
  match n with
  | 0   => 1
  | S m => x * pow_nat x m
  end.

Definition square {m : Modulus} (x : Zmod m) : Zmod m := x * x.
Fixpoint pow_positive {m : Modulus}(x : Zmod m)(p : positive) : Zmod m :=
  match p with
  | xH => x
  | xO pp => square (pow_positive x pp)
  | xI pp => x * square (pow_positive x pp)
  end.

(* end hide *)

Instance power_Zmod_nat (m : Modulus) : Power  := @pow_nat m.
Instance power_Zmod_positive (m : Modulus) : Power  := @pow_positive m.

Definition pow_N {m : Modulus}(x : Zmod m)(n : N) : Zmod m :=
  match n with
  | N0 => 1
  | Npos p => x ^ p
  end.
(* end hide *)
Instance power_Zmod_N (m : Modulus) : Power := @pow_N m.

Ltac unfold_equalities := unfold equality; unfold eq_Zmod; unfold eqZmod.
Ltac unfold_brackets   := unfold bracket; unfold Zmod_to_Z; unfold Z_to_Zmod; unfold Zmod2Z; unfold Z2Zmod;  unfold residue.
Ltac unfold_algebraic  := unfold addition; unfold add_Zmod;
                          unfold multiplication; unfold mul_Zmod;
                          unfold arithm.

Ltac rewrite_algebraic tac := unfold_algebraic; rewrite tac; eauto with Zmod.

Hint Rewrite Z.mod_mod Z.mod_1_l Z.mul_1_l : Zmod.





Ltac crush_step :=
                   match goal with
                   | [ |- context[_ == _] ] => unfold_equalities
                   | [ |- Zmod _ -> _ ] => intro
                   (* | [ |- _ = _ -> _ ]  =>  intro *)
                   (* | [ |- context[((_ mod _ + _ mod _) mod _)%N]] => rewrite <- N.add_mod *)
                   | [ x : Zmod _ |- _ ] => destruct x
                   | _ =>  try unfold_brackets; try unfold_algebraic; try unfold eqb_Zmod
                   end;
                   simpl;
                   autorewrite with Zmod;
                   eauto with Zmod.



Ltac crush := repeat crush_step.
Ltac crush_with_rewrite rule := crush; rewrite rule; crush.

Global Hint Resolve N.mod_mod : Zmod.

Lemma eq_eq_mod : forall m (x y : Zmod m), x = y -> x == y.
  intros m x y xEqY.
  rewrite xEqY; apply f_equal; trivial.
Qed.

Require Import Ring_theory.


Section Properties.
  Context (m : Modulus).

  Lemma eqZmod_refl : forall x : Zmod m, x == x.
    crush.
  Qed.

  Lemma eqZmod_sym : forall x y : Zmod m, x == y -> y == x.
    crush.
  Qed.

  Lemma eqZmod_trans : forall x y z: Zmod m, x == y -> y == z -> x == z.
    crush.

    intuition.
  Qed.


  Lemma Zmod_add_0_l : forall x : Zmod m, 0 + x == x.
    crush.
  Qed.


  Lemma Zmod_add_comm : forall x y : Zmod m, x + y == y + x.
    crush_with_rewrite Z.add_comm.
  Qed.

  Lemma add_mod_inner_r : forall (x y z M : Z), M <> 0%Z -> (x + (y mod M + z mod M) mod M = x + (y + z) mod M)%Z.
    intros.
    rewrite <- Z.add_mod; trivial.
  Qed.

  Lemma add_mod_inner_l : forall (x y z M : Z), M <> 0%Z -> ((x mod M + y mod M) mod M + z = (x + y) mod M + z )%Z.
    intros.
    rewrite <- Z.add_mod; trivial.
  Qed.

  Hint Rewrite add_mod_inner_r add_mod_inner_l : Zmod.

  Lemma Zmod_add_assoc : forall x y z : Zmod m, x + (y + z) == (x + y) + z.
    crush.
    repeat (rewrite <- Z.add_mod; crush).
    rewrite Z.add_assoc; trivial.
  Qed.

  Lemma Zmod_mul_1_l : forall x : Zmod m, 1 * x == x.
    crush.
  Qed.

  Lemma Zmod_mul_comm : forall x y : Zmod m, x * y == y * x.
    crush_with_rewrite Z.mul_comm.
  Qed.

  Check Z.mul_mod.
  Lemma mul_mod_inner_r : (forall (x y z M : Z), M <> 0 -> x * ((y mod M) * (z mod M) mod M) = x * ((y * z) mod M))%Z.
    intros.
    rewrite <- Z.mul_mod; trivial.
  Qed.

  Lemma mul_mod_inner_l : (forall (x y z M : Z), M <> 0%Z -> ((x mod M) * (y mod M) mod M) * z = ((x * y) mod M) * z)%Z.
    intros.
    rewrite <- Z.mul_mod; trivial.
  Qed.
  Hint Rewrite mul_mod_inner_r mul_mod_inner_l : Zmod.

  Lemma Zmod_mul_assoc : forall x y z : Zmod m, x * (y * z) == (x * y) * z.
    crush.
    repeat (rewrite <- Z.mul_mod; crush).
    rewrite Z.mul_assoc; trivial.
  Qed.

  Lemma add_mul_mod_inner : (forall (x y z M : Z), M <> 0 -> ((x mod M + y mod M) mod M) * z  = (x + y) mod M  * z)%Z.
    intros.
    rewrite <- Z.add_mod; trivial.
  Qed.

  Hint Rewrite add_mul_mod_inner : Zmod.
  (*
  Lemma mul_mod_inner_l : (forall (x y z M : N), M <> 0%N -> ((x mod M) * (y mod M) mod M) * z = ((x * y) mod M) * z)%Z.
    intros.
    rewrite <- Z.mul_mod; trivial.
  Qed.

  Hint Rewrite mul_mod_inner_r mul_mod_inner_l : Zmod.
   *)
  Lemma Zmod_distr_l : forall x y z : Zmod m,  (x + y) * z == x * z + y * z.
    crush.
    repeat rewrite <- Z.mul_mod; crush.
    repeat rewrite <- Z.add_mod; crush.
    rewrite Z.mul_add_distr_r; trivial.
  Qed.

  Lemma Zmod_sub_def : forall x y : Zmod m,  x - y == x + (- y).
    crush.
    rewrite <- Z.add_opp_r.
    rewrite Z.add_mod; crush.
  Qed.

  (*
  Hint Resolve Z.mod_le Z.mod_lt Z.lt_le_incl : Zmod.  *)

  Search ((_ - _ mod _) mod _)%Z.


  Lemma Zmod_opp_def : (forall x : Zmod m, (x + - x) == 0).
    crush.
    rewrite <- Z.add_mod; crush.
    rewrite Z.add_opp_r.
    rewrite Zminus_mod. crush.
    rewrite Z.sub_diag.
    trivial.
  Qed.

  Lemma Zmod_eqb_eq : forall x y : Zmod m, eqb_Zmod x y = true -> x == y.
    intros x y.
    unfold eqb_Zmod.
    intros.
    unfold_equalities.
    apply Z.eqb_eq; trivial.
  Qed.


  Program Definition Zmod_ring
    : ring_theory
        0
        1
        addition
        multiplication
        subtraction
        opposite
        (@eq_Zmod m)
    := {| Radd_0_l   := Zmod_add_0_l ;
          Radd_comm  := Zmod_add_comm ;
          Radd_assoc := Zmod_add_assoc ;
          Rmul_1_l   := Zmod_mul_1_l ;
          Rmul_comm  := Zmod_mul_comm ;
          Rmul_assoc := Zmod_mul_assoc ;
          Rdistr_l   := Zmod_distr_l ;
          Rsub_def   := Zmod_sub_def;
          Ropp_def   := Zmod_opp_def ;
       |}.

End Properties.


Require Export Setoid.
Require Export Relation_Definitions.
Add Parametric Relation m : (Zmod m) equality
    reflexivity proved by (eqZmod_refl m)
    symmetry proved by (@eqZmod_sym m)
    transitivity proved by (@eqZmod_trans m) as modular_arithmetic_equality.


Add Parametric Morphism (m : Modulus) : (@addition (Zmod m) _)
    with signature equality ==> equality ==> equality as modular_addition_morphism.
  crush.
  intro H1.
  crush.
  intro H2.
  rewrite H1; rewrite H2; trivial.
Qed.


Add Parametric Morphism m : (@multiplication (Zmod m) (Zmod m) _)
    with signature equality ==> equality ==> equality as modular_multiplication_morphism.
  crush.
  intro H1.
  crush.
  intro H2.
  rewrite H1.
  rewrite H2. trivial.
Qed.

Add Parametric Morphism m : (@opposite (Zmod m) _)
    with signature equality ==> equality  as modular_op_morphism.
  crush.
  intro H1.
  rewrite H1; trivial.
Qed.


(** Some interesting prime modulus *)
Definition P1305 : Modulus := exist _ (2^130 - 5)%Z eq_refl.
Definition P25519 : Modulus := exist _ (2^255 - 19)%Z eq_refl.
Add Ring GFP1305 : (Zmod_ring P1305).
Add Ring GFP25519 : (Zmod_ring P25519).

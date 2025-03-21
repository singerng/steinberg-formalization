/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Algebra.Ring.Basic

import Mathlib.Tactic.Ring

universe TR
variable {R : Type TR} [CommRing R]

def Bool.toRing {R : Type u} [CommRing R] (s : Bool) : R :=
  match s with
  | Bool.true => (1 : R)
  | Bool.false => (-1 : R)

theorem true_toRing : true.toRing = (1 : R) := by simp only [Bool.toRing]
theorem false_toRing : false.toRing = (-1 : R) := by simp only [Bool.toRing]

instance : Coe Bool R where
  coe x := x.toRing

theorem square_eq_one {a : Bool} : a.toRing^2 = (1 : R) := by
  rcases a
  all_goals (
    simp only [Bool.toRing]
    ring
  )

@[simp]
theorem Bool.int_of_neg {R : Type u} [CommRing R] (a : Bool) : @(!a).toRing R _ = -a.toRing := by
  rcases a
  all_goals simp only [Bool.not, Bool.toRing, neg_neg]

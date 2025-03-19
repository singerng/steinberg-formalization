/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

universe TI
variable {I : Type TI} [DecidableEq I] [Fintype I]

def SignedWithZero (I : Type TI) [DecidableEq I] [Fintype I] :=
  (Bool × I) ⊕ Unit
instance : DecidableEq (SignedWithZero I) := instDecidableEqSum
instance : Fintype (SignedWithZero I) := instFintypeSum _ _

-- NS: Maybe there is a more 'idiomatic' way to write this shortly?

def SignedWithZero.zero : SignedWithZero I := Sum.inr ()
def Bool.inj (s : Bool) (i : I) : SignedWithZero I := Sum.inl (s, i)

theorem SignedWithZero.zero_ne_signed {a : Bool} {i : I} : SignedWithZero.zero ≠ a.inj i := by
  simp only [Bool.inj, SignedWithZero.zero]
  by_contra
  injections

theorem SignedWithZero.signed_ne_zero {a : Bool} {i : I} : a.inj i ≠ SignedWithZero.zero := Ne.symm zero_ne_signed

theorem SignedWithZero.ne_of_neg {a : Bool} {i j : I} : (!a).inj i ≠ a.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  simp_all only [Bool.not_eq_eq_eq_not, Bool.eq_not_self]

theorem SignedWithZero.ne_of_ne {a b : Bool} {i j : I} (h : i ≠ j) : a.inj i ≠ b.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  contradiction

theorem SignedWithZero.neg_of_ne {a b : Bool} {i j : I} (h : a.inj i ≠ (!b).inj j) : (!a).inj i ≠ b.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  simp_all only [ne_eq, Bool.not_eq_eq_eq_not, not_true_eq_false]

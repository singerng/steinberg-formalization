/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

/-!
  Datatype which, given an instance `I` of `Fintype` and `DecidableEq`, produces a new type
  which is an instance of the same typeclasses and has cardinality `2|I|`, namely,
  `Bool × I`. We think of `Bool x I` as a "signed" version of `I`, and it admits a natural
  "negation" involution given by sending `(s, i)` to `(!s, i)`. The canonical example for this
  is where `I = Fin n`, in which case `Signed I` corresponds to integers between `-n` and `+n` excluding `0`.
-/

universe TI
variable {I : Type TI} [DecidableEq I] [Fintype I]

namespace Chevalley
open Chevalley

def Signed (I : Type TI) [DecidableEq I] [Fintype I] := Bool × I
instance : DecidableEq (Signed I) := instDecidableEqProd
instance : Fintype (Signed I) := instFintypeProd _ _

-- TODO-A: Maybe there is a more 'idiomatic' way to write this shortly?

theorem Signed.ne_of_neg {a : Bool} {i : I} : (!a, i) ≠ (a, i) := by
  by_contra
  injections
  simp_all only [Bool.not_eq_eq_eq_not, Bool.eq_not_self]

theorem Signed.ne_of_ne {a b : Bool} {i j : I} (h : i ≠ j) : (a, i) ≠ (b, j) := by
  by_contra
  injections
  contradiction

theorem Signed.neg_of_ne {a b : Bool} {i j : I} (h : (a, i) ≠ (!b, j)) : (!a, i) ≠ (b, j) := by
  by_contra
  injections
  simp_all only [ne_eq, Bool.not_eq_eq_eq_not, not_true_eq_false]

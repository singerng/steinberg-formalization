import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Group
import Init.Data.Nat.Basic

namespace Steinberg

/-! ### Notations for theorems involving group elements -/

/-
  These notations essentially act like "inline mathematical notation,"
  in the sense that using a `def` is too strong (i.e., it obscures
  the underlying notion behind a name that we would have to `unfold`
  or `rw` or supply `simp` lemmas for). Rather, this is shorthand
  for longer expressions that would otherwise take a while to type.
-/
scoped notation "triv_comm" "( " x ", " y " )" => ⁅ x, y ⁆ = 1
scoped notation "commutes" "( " x ", " y " )" => x * y = y * x
scoped notation "reorder_left" "( " x ", " y ", " z " )" => x * y = z * y * x
scoped notation "reorder_mid" "( " x ", " y ", " z " )" => x * y = y * z * x

variable {G : Type Tu} [Group G]
         {R : Type Tv} [Ring R]
         {w x y z : G}

/-! ### Theorems about commutators (holding in any group) -/

theorem comm_left_str  (x y : G) : x * y = ⁅x, y⁆ * y * x := by group
theorem comm_mid_str   (x y : G) : x * y = y * ⁅x, y⁻¹⁆⁻¹ * x := by group
theorem comm_right_str (x y : G) : x * y = y * x * ⁅x⁻¹, y⁻¹⁆ := by group

theorem commutes_of_triv_comm : triv_comm(x, y) → commutes(x, y) := by
  intro h
  rw [comm_left_str, h, one_mul]

theorem triv_comm_of_commutes : commutes(x, y) → triv_comm(x, y) := by
  intro h
  rw [commutatorElement_def, h, mul_inv_cancel_right, mul_inv_cancel]

theorem triv_comm_iff_commutes : triv_comm(x, y) ↔ commutes(x, y) :=
  ⟨commutes_of_triv_comm, triv_comm_of_commutes⟩

theorem eq_comm_of_reorder_left : reorder_left(x, y, z) → ⁅x, y⁆ = z := by
  intro h
  simp only [commutatorElement_def, h, mul_inv_cancel_right]

theorem reorder_left_of_eq_comm : ⁅x, y⁆ = z → reorder_left(x, y, z) := by
  rw [commutatorElement_def]
  rintro rfl
  simp_rw [inv_mul_cancel_right]

theorem reorder_left_iff_eq_comm : reorder_left(x, y, z) ↔ ⁅x, y⁆ = z :=
  ⟨eq_comm_of_reorder_left, reorder_left_of_eq_comm⟩

/- CC: For these `triv_comm` theorems, I don't like the approach of the proofs.
   So far, the proofs are essentially just unfolding the trivial commutator
   definition and applying commutativity as needed. But this sidesteps the
   potential usefulness of a `triv_comm` definition.

   While some definition-unfolding is necessary to establish an API/starting
   set of lemmas, I think things can be reworked here to use more
   "commutator theory."
-/

-- CC: Perhaps we can replace this with `triv_comm()`, but I think the statement is clearer this way.
@[symm]
theorem triv_comm_symm : ⁅ x, y ⁆ = 1 ↔ ⁅ y, x ⁆ = 1 := by
  simp_rw [triv_comm_iff_commutes]
  exact eq_comm

@[simp]
theorem inv_triv_comm_iff_triv_comm : triv_comm(x⁻¹, y) ↔ triv_comm(x, y) := by
  simp_rw [triv_comm_iff_commutes]
  apply Iff.intro
  · intro h
    apply @mul_left_cancel _ _ _ x⁻¹
    rw [inv_mul_cancel_left, ← mul_assoc, h, mul_assoc, inv_mul_cancel, mul_one]
  · intro h
    apply @mul_left_cancel _ _ _ x
    rw [mul_inv_cancel_left, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]

@[simp]
theorem inv_triv_comm_iff_triv_comm' : triv_comm(x, y⁻¹) ↔ triv_comm(x, y) := by
  simp_rw [@triv_comm_symm _ _ x]
  exact inv_triv_comm_iff_triv_comm

-- CC: Better name? Could be `triv_comm_trans_right` or `triv_comm_trans_mul_right`
theorem triv_comm_mul_right : triv_comm(x, y) → triv_comm(x, z) → triv_comm(x, y * z) := by
  simp_rw [triv_comm_iff_commutes]
  intro hxy hxz
  rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]

-- CC: Better name? Could be `triv_comm_trans_left`
theorem triv_comm_mul_left : triv_comm(x, z) → triv_comm(y, z) → triv_comm(x * y, z) := by
  simp_rw [triv_comm_iff_commutes]
  intro hxz hyz
  rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc]

theorem trivial_comm_mul_mul : triv_comm(x, w) → triv_comm(x, z)
    → triv_comm(y, w) → triv_comm(y, z) → triv_comm(x * y, w * z) := by
  simp_rw [triv_comm_iff_commutes]
  intro hxw hxz hyw hyz
  -- CC: Ripe for automation/a macro!
  rw [← mul_assoc, mul_assoc x, hyw, ← mul_assoc, hxw,
    mul_assoc, hyz, ← mul_assoc, mul_assoc w, hxz, ← mul_assoc, mul_assoc]

/- Deduce that two elements commute if one can "embed" them in a larger, trivial commutator where all other pairs commute. -/
theorem trivial_comm_from_embedded_comm_and_pairs : triv_comm(x * y, w * z) → triv_comm(x, w)
    → triv_comm(y, w) → triv_comm(y, z) → triv_comm(x, z) := by
  simp_rw [triv_comm_iff_commutes]
  intro h_all h_xw h_yw h_yz
  -- Add `y` on the right and `w` on the left to maintain relative orders wrt `x` and `z`
  apply @mul_right_cancel _ _ _ _ y
  apply @mul_left_cancel _ _ _ w
  simp_rw [← mul_assoc]
  rw [← h_xw, mul_assoc, ← h_yz, ← mul_assoc, mul_assoc x, ← h_yw, ← mul_assoc,
    mul_assoc, h_all, ← mul_assoc]


/-! ### Definition of Deg type -/

/-- Degrees `Deg` are the (sub)type of natural numbers (including 0)
    that do not exceed `n`, i.e., that `Deg n = {0, 1, ..., n}`. -/
abbrev Deg (n : ℕ) := Fin (n + 1)

end Steinberg

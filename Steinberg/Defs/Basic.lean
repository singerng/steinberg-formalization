import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Group

namespace Steinberg

variable {G : Type Tu} [Group G]
         {R : Type Tv} [Ring R]

/-! ### Theorems about commutators (holding in any group) -/

theorem comm_left_str  (x y : G) : x * y = ⁅x, y⁆ * y * x := by group
theorem comm_mid_str (x y : G)   : x * y = y * ⁅x, y⁻¹⁆⁻¹ * x := by group
theorem comm_right_str (x y : G) : x * y = y * x * ⁅x⁻¹, y⁻¹⁆ := by group

-- NS: Should combine the following two into an iff theorem
theorem trivial_comm_to_commutes {x y : G} : ⁅x, y⁆ = 1 → x * y = y * x := by
  intro h
  rw [comm_left_str, h, one_mul]

theorem commutes_to_trivial_comm {x y : G} : x * y = y * x → ⁅x, y⁆ = 1 := by
  intro h
  group
  rw [h]
  group

theorem comm_on_left {x y z : G} : x * y = z * y * x → ⁅x, y⁆ = z := by
  intro h
  group
  rw [h]
  group

theorem symm_of_trivial_comm {x y : G} : ⁅ x, y ⁆ = 1 → ⁅ y, x ⁆ = 1 := by
  intro h
  apply commutes_to_trivial_comm
  apply Eq.symm
  apply trivial_comm_to_commutes
  exact h

theorem inv_of_trivial_comm {x y : G} : ⁅ x , y ⁆ = 1 → ⁅ x⁻¹, y ⁆ = 1 := by
  intro h
  apply commutes_to_trivial_comm
  apply @mul_left_cancel _ _ _ x
  apply @mul_right_cancel _ _ _ _ x
  group
  apply trivial_comm_to_commutes
  apply symm_of_trivial_comm
  exact h

theorem trivial_comm_of_right {x y z : G} : ⁅ x, y ⁆ = 1 → ⁅ x, z ⁆ = 1 → ⁅ x, y * z ⁆ = 1 := by sorry
theorem trivial_comm_of_left {x y z : G} : ⁅ x, y ⁆ = 1 → ⁅ y, z ⁆ = 1 → ⁅ x * y, z ⁆ = 1 := by sorry
theorem trivial_comm_of_both {x y z w : G} : ⁅ x, z ⁆ = 1 → ⁅ x, w ⁆ = 1 → ⁅ y, z ⁆ = 1 → ⁅ y, w ⁆ = 1 → ⁅ x * y, z * w ⁆ = 1 := by sorry

/- Deduce that two elements commute if one can "embed" them in a larger, trivial commutator where all other pairs commute. -/
theorem trivial_comm_from_embedded_comm_and_pairs { x y z w : G } : (⁅x * y, z * w⁆ = 1) → (⁅x, w⁆ = 1) →
    (⁅y, z⁆ = 1) → (⁅y, w⁆ = 1) → (⁅x, z⁆ = 1) := by
  intro h_all h_xw h_yz h_yw
  rw [← h_all]
  apply @mul_left_cancel _ _ _ x⁻¹
  apply @mul_right_cancel _ _ _ _ z
  group
  have : y * z * w * y^(-1 : ℤ) = z * w := by
    have : y * z = z * y := by
      apply trivial_comm_to_commutes
      exact h_yz
    rw [this]
    rw [mul_assoc _ y]
    have : y * w = w * y := by
      apply trivial_comm_to_commutes
      exact h_yw
    rw [this]
    group
  rw [this]
  apply @mul_left_cancel _ _ _ z⁻¹
  apply @mul_right_cancel _ _ _ _ w
  group
  apply trivial_comm_to_commutes
  have : x^(-1 : ℤ) = x⁻¹ := by group
  rw [this]
  apply inv_of_trivial_comm
  exact h_xw

  -- group

/-! ### Notations for theorems involving group elements -/

scoped notation "triv_commutator" x y => ⁅ x, y ⁆ = 1
scoped notation "commutes" "( " x ", " y " )" => x * y = y * x
scoped notation "reorder_left" "( " x ", " y ", " z " )" => x * y = z * y * x
scoped notation "reorder_mid" "( " x ", " y ", " z " )" => x * y = y * z * x

/-! ### Definition of Deg type -/

/-- Degrees `Deg` are the (sub)type of natural numbers (including 0)
    that do not exceed `n`, i.e., that `Deg n = {0, 1, ..., n}`. -/
abbrev Deg (n : ℕ) := Fin (n + 1)

end Steinberg

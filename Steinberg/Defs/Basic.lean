import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.Group

namespace Steinberg

variable {G : Type Tu} [Group G]
         {R : Type Tv} [Ring R]

/- commutator identities (holding in any group) -/
theorem comm_left_str  (x y : G) : x * y = ⁅x, y⁆ * y * x := by group
theorem comm_mid_str (x y : G)   : x * y = y * ⁅x, y⁻¹⁆⁻¹ * x := by group
theorem comm_right_str (x y : G) : x * y = y * x * ⁅x⁻¹, y⁻¹⁆ := by group

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

/-- Degrees `Deg` are the (sub)type of natural numbers (including 0)
    that do not exceed `n`, i.e., that `Deg n = {0, 1, ..., n}`. -/
abbrev Deg (n : ℕ) := Fin (n + 1)

/- generic forms for propositions -/
/- group theory -/

scoped notation "triv_commutator" x y => ⁅ x, y ⁆ = 1
scoped notation "commutes" "( " x ", " y " )" => x * y = y * x
scoped notation "reorder_left" "( " x ", " y ", " z " )" => x * y = z * y * x
scoped notation "reorder_mid" "( " x ", " y ", " z " )" => x * y = y * z * x

end Steinberg

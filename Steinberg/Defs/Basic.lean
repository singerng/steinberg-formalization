import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.Group

variable {G : Type Tu} [Group G]

/- commutator identities (holding in any group) -/

theorem comm_left_str  (x y : G)   : x * y = ⁅x, y⁆ * y * x := by group
theorem comm_right_str (x y : G)  : x * y = y * x * ⁅x⁻¹, y⁻¹⁆ := by group

theorem comm_to_comm {x y : G} : ⁅x, y⁆ = 1 → x * y = y * x := by
  intro h; rw [comm_left_str, h, one_mul]

theorem comm_on_left {x y z : G} : x * y = z * y * x → ⁅x, y⁆ = z := by
  intro h
  group
  rw [h]
  group

import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.Group

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
  sorry

theorem comm_on_left {x y z : G} : x * y = z * y * x → ⁅x, y⁆ = z := by
  intro h
  group
  rw [h]
  group

/- generic forms for propositions -/
/- group theory -/
@[reducible]
-- `x * y = y * x`
def CommutesProp (x y : G) : Prop :=
  x * y = y * x

@[reducible]
-- `x * y = z * y * x`
def ReorderLeftProp (x y z : G) : Prop :=
  x * y = z * y * x

@[reducible]
-- `x * y = z * y * x`
def ReorderMidProp (x y z : G) : Prop :=
  x * y = y * z * x

@[reducible]
def TrivialCommutatorProp (x y : G) : Prop :=
  ⁅ x, y ⁆ = 1

@[reducible]
def CommutatorProp (x y z : G) : Prop :=
  ⁅ x, y ⁆ = z

/- groups and rings -/
@[simp]
-- `(f t) * (f u) = f (t + u)`
def LinearityProp (f : R → G) : Prop :=
  ∀ (t u : R), (f t) * (f u) = f (t + u)

-- `f(0) = 0`
abbrev IdentityProp (f : R → G) : Prop :=
  f (0 : R) = (1 : G)

-- `f(t)⁻¹ = f(-t)`
@[simp]
def InverseProp (f : R → G) : Prop :=
  ∀ (t : R), f (-t) = (f t)⁻¹

-- deduce an IdentityProp from an LinearityProp
theorem IdentityFromLinearity (f : R → G) : LinearityProp f → IdentityProp f := by
  intro h
  rw [IdentityProp]
  apply @mul_left_cancel _ _ _ (f 0)
  rw [mul_one]
  rw [h]
  rw [add_zero]
  done

-- deduce an InverseProp from a LinearityProp
theorem InverseFromLinearity (f : R → G) : LinearityProp f → InverseProp f := by
  intro h
  rw [InverseProp]
  intro t
  apply @mul_left_cancel _ _ _ (f t)
  rw [h]
  rw [add_neg_cancel t]
  rw [IdentityFromLinearity f h]
  rw [mul_inv_cancel]
  done

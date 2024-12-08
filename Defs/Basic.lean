import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Algebra.Ring.Defs

import Batteries.Data.UInt

namespace Steinberg

#check FreeGroup
#check commutatorElement_def

-- \α, α+β, β, β+γ, γ

variable {G : Type Tu} [Group G]
         {R : Type Tv} [Ring R]

/- commutator identities (holding in any group) -/

theorem comm_left_str (x y : G)   : x * y = ⁅x, y⁆ * y * x := by group
theorem comm_right_str (x y : G)  : x * y = y * x * ⁅x⁻¹, y⁻¹⁆ := by group

theorem comm_to_comm (x y : G) (h : ⁅x, y⁆ = 1) : x * y = y * x := by
  sorry

theorem comm_on_left (x y z : G) (h : x * y = z * y * x) : ⁅x, y⁆ = z := by
  group
  rw [h]
  group

/- defining the A3 positive root system -/
inductive Root
  | α | β | γ | αβ | βγ

namespace Root

def height : Root → Nat
  | Root.α => 1
  | Root.β => 1
  | Root.γ => 1
  | Root.αβ => 2
  | Root.βγ => 2

end Root

structure RootedElem (R : Type v) [Ring R] where
  root : Root
  coeff : R
  -- i : Fin root.height   -- CC: These two are equivalent
  i : Nat
  hi : i ≤ root.height

namespace RootedElem

open Root

/- defining the weak A3 unipotent group -/
def mk' {R : Type Tv} [Ring R] (r : Root) (coeff : R) {i : Nat} (hi : i ≤ r.height) : RootedElem R :=
  mk r coeff i hi

def mkOf {R : Type Tv} [Ring R] (r : Root) (coeff : R) {i : Nat} (hi : i ≤ r.height) := FreeGroup.of <| mk' r coeff hi

def Linearity (R : Type Tv) [Ring R] := ∀ (r : Root) (t u : R) {i : Nat} (hi : i ≤ r.height),
    (mkOf r t hi) * (mkOf r u hi) = (mkOf r (t + u) hi)

-- nontrivial commutators
def α_comm_β (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ α.height) (hj : j ≤ β.height),
 ⁅ mkOf α t hi, mkOf β u hj ⁆ = @mkOf _ _ αβ (t * u) (i + j) (by simp [height] at *; omega)

def β_comm_γ (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ β.height) (hj : j ≤ γ.height),
 ⁅ mkOf β t hi, mkOf γ u hj ⁆ = @mkOf _ _ Root.βγ (t * u) (i + j) (by simp [Root.height] at *; omega)

-- trivial commutators
def β_comm_αβ (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ β.height) (hj : j ≤ αβ.height),
 ⁅ mkOf β t hi, mkOf αβ u hj ⁆ = 1

def γ_comm_βγ (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ γ.height) (hj : j ≤ βγ.height),
 ⁅ mkOf γ t hi, mkOf βγ u hj ⁆ = 1

def α_comm_γ (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ Root.α.height) (hj : j ≤ γ.height),
 ⁅ mkOf α t hi, mkOf γ u hj ⁆ = 1

def αβ_comm_βγ (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ Root.αβ.height) (hj : j ≤ βγ.height),
 ⁅ mkOf αβ t hi, mkOf βγ u hj ⁆ = 1

structure WeakA3 (R : Type Tv) [Ring R] where
  h_lin : Linearity R
  h_α_β : α_comm_β R
  h_β_γ : β_comm_γ R
  h_α_γ : α_comm_γ R
  h_β_αβ : β_comm_αβ R
  h_γ_βγ : γ_comm_βγ R
  h_αβ_βγ : αβ_comm_βγ R

/- analysis of the group -/
-- deduce identity relations from linearity relations
@[simp]
theorem Identity (h : WeakA3 R) (r : Root) {i : Nat} (hi : i ≤ r.height) :
    mkOf r (0 : R) hi = 1 := by
  apply @mul_left_cancel _ _ _ (mkOf r 0 hi)
  rw [mul_one]
  rw [h.h_lin r (0 : R) (0 : R) hi]
  rw [add_zero]
  done

-- deduce inverse relations from linearity relations
@[simp]
theorem Inverse (h : WeakA3 R) (r : Root) (t : R) {i : Nat} (hi : i ≤ r.height) :
    mkOf r (-t : R) hi = (mkOf r t hi)⁻¹ := by
  apply @mul_left_cancel _ _ _ (mkOf r t hi)
  rw [h.h_lin r t (-t) hi]
  rw [add_neg_cancel t]
  rw [Identity h r hi]
  rw [mul_inv_cancel]
  done

-- explicit expressions of commutators
@[simp]
theorem expr_βγ_as_β_comm_γ (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ β.height) (hj : j ≤ γ.height) :
    @mkOf _ _ βγ (t*u) (i+j) (by simp [height] at *; omega) = (mkOf β t hi) * (mkOf γ u hj) * (mkOf β (-t) hi) * (mkOf γ (-u) hj) := by
  rw [Inverse h β t hi]
  rw [Inverse h γ u hj]
  rw [← commutatorElement_def]
  rw [← h.h_β_γ t u hi hj]
  done

-- rewrites for products of noncommuting elements
@[simp]
theorem expr_α_β_as_αβ_β_α (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ α.height) (hj : j ≤ β.height) :
    (mkOf α t hi) * (mkOf β u hj) = (@mkOf _ _ αβ (t*u) (i+j) (by simp [height] at *; omega)) * (mkOf β u hj) * (mkOf α t hi) := by
  rw [← h.h_α_β t u hi hj]
  rw [comm_left_str (mkOf α t hi) (mkOf β u hj)]
  done

@[simp]
theorem expr_β_γ_as_βγ_γ_β (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ β.height) (hj : j ≤ γ.height) :
    (mkOf β t hi) * (mkOf γ u hj) = (@mkOf _ _ βγ (t*u) (i+j) (by simp [height] at *; omega)) * (mkOf γ u hj) * (mkOf β t hi) := by
  rw [← h.h_β_γ t u hi hj]
  rw [comm_left_str (mkOf β t hi) (mkOf γ u hj)]
  done

-- rewrites for products of commuting elements
@[simp]
theorem expr_α_γ_as_γ_α (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ α.height) (hj : j ≤ γ.height) :
    (mkOf α t hi) * (mkOf γ u hj) = (mkOf γ u hj) * (mkOf α t hi) := by
  apply comm_to_comm
  rw [h.h_α_γ]
  done

@[simp]
theorem expr_β_αβ_as_αβ_β (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ β.height) (hj : j ≤ αβ.height) :
    (mkOf β t hi) * (mkOf αβ u hj) = (mkOf αβ u hj) * (mkOf β t hi) := by
  apply comm_to_comm
  rw [h.h_β_αβ]
  done

@[simp]
theorem expr_γ_βγ_as_βγ_γ (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ γ.height) (hj : j ≤ βγ.height) :
    (mkOf γ t hi) * (mkOf βγ u hj) = (mkOf βγ u hj) * (mkOf γ t hi) := by
  apply comm_to_comm
  rw [h.h_γ_βγ]
  done

@[simp]
theorem expr_αβ_βγ_as_βγ_αβ (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ αβ.height) (hj : j ≤ βγ.height) :
    (mkOf αβ t hi) * (mkOf βγ u hj) = (mkOf βγ u hj) * (mkOf αβ t hi) := by
  apply comm_to_comm
  rw [h.h_αβ_βγ]
  done

-- interchange theorem, ⁅α, βγ⁆ = ⁅αβ, γ⁆
theorem Interchange (h : WeakA3 R) (t u v : R) {i j k : Nat} (hi : i ≤ Root.α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
    ⁅ mkOf α t hi, @mkOf _ _ Root.βγ (u*v) (j+k) (by simp [height] at *; omega) ⁆ =
    ⁅ @mkOf _ _ αβ (t*u) (i+j) (by simp [height] at *; omega), mkOf Root.γ v hk ⁆:= by
  apply comm_on_left
  conv => lhs;
  -- phase I: push α to right
  rw [expr_βγ_as_β_comm_γ h u v hj hk]
  simp_rw [← mul_assoc]
  rw [expr_α_β_as_αβ_β_α h t u hi hj]
  rw [mul_assoc _ (mkOf α t hi) _]
  rw [expr_α_γ_as_γ_α h t v hi hk]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (mkOf α t hi) _]
  rw [expr_α_β_as_αβ_β_α h t (-u) hi hj]
  rw [mul_neg] -- rewrite t*(-u) as -(t*u)
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (mkOf α t hi) _]
  rw [expr_α_γ_as_γ_α h t (-v) hi hk]
  simp_rw [← mul_assoc]
  -- phase II: move β's together
  rw [mul_assoc _ (mkOf β u hj) _]
  rw [expr_β_γ_as_βγ_γ_β h u v hj hk]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (mkOf β u hj) _]
  rw [expr_β_αβ_as_αβ_β h u (-(t*u)) hj (by simp [height] at *; omega)]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (mkOf β u hj) _]
  rw [Inverse h β]
  group
  -- phase III: push βγ to the right
  rw [mul_assoc _ (@mkOf _ _ βγ (u*v) (j+k) (by simp [height] at *; omega)) _]
  rw [← expr_γ_βγ_as_βγ_γ]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (@mkOf _ _ βγ (u*v) (j+k) (by simp [height] at *; omega)) _]
  rw [← expr_αβ_βγ_as_βγ_αβ]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (@mkOf _ _ βγ (u*v) (j+k) (by simp [height] at *; omega)) _]
  rw [← expr_γ_βγ_as_βγ_γ]
  simp_rw [← mul_assoc]
  repeat rw [Inverse]
  rw [← commutatorElement_def]
  rfl
  done

end RootedElem

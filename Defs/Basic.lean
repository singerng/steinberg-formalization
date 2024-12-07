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

theorem comm_left_str (x y : G)   : x * y = ⁅x, y⁆ * y * x := by group
theorem comm_right_str (x y : G)  : x * y = y * x * ⁅x⁻¹, y⁻¹⁆ := by group

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

def mk' {R : Type Tv} [Ring R] (r : Root) (coeff : R) {i : Nat} (hi : i ≤ r.height) : RootedElem R :=
  mk r coeff i hi

def mkOf {R : Type Tv} [Ring R] (r : Root) (coeff : R) {i : Nat} (hi : i ≤ r.height) := FreeGroup.of <| mk' r coeff hi

def Linearity (R : Type Tv) [Ring R] := ∀ (r : Root) (t u : R) {i : Nat} (hi : i ≤ r.height),
    (mkOf r t hi) * (mkOf r u hi) = (mkOf r (t + u) hi)

def α_comm_β (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ α.height) (hj : j ≤ β.height),
 ⁅ mkOf α t hi, mkOf β u hj ⁆ = @mkOf _ _ αβ (t * u) (i + j) (by simp [height] at *; omega)

def β_comm_γ (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ β.height) (hj : j ≤ γ.height),
 ⁅ mkOf β t hi, mkOf .γ u hj ⁆ = @mkOf _ _ Root.βγ (t * u) (i + j) (by simp [Root.height] at *; omega)

def α_comm_γ (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ Root.α.height) (hj : j ≤ γ.height),
 ⁅ mkOf Root.α t hi, mkOf Root.γ u hj ⁆ = 1

def αβ_comm_βγ (R : Type Tv) [Ring R] := ∀ (t u : R) {i j : Nat} (hi : i ≤ Root.αβ.height) (hj : j ≤ βγ.height),
 ⁅ mkOf Root.αβ t hi, mkOf Root.βγ u hj ⁆ = 1

structure WeakA3 (R : Type Tv) [Ring R] where
  h_lin : Linearity R
  h_αβ : α_comm_β R
  h_βγ : β_comm_γ R
  h_αγ : α_comm_γ R
  h_αβ_βγ : αβ_comm_βγ R

@[simp]
theorem Identity (h : WeakA3 R) (r : Root) {i : Nat} (hi : i ≤ r.height) :
    mkOf r (0 : R) hi = 1 := by
  apply @mul_left_cancel _ _ _ (mkOf r 0 hi)
  rw [mul_one]
  rw [h.h_lin r (0 : R) (0 : R) hi]
  rw [add_zero]
  done

@[simp]
theorem Inverse (h : WeakA3 R) (r : Root) (t : R) {i : Nat} (hi : i ≤ r.height) :
    mkOf r (-t : R) hi = (mkOf r t hi)⁻¹ := by
  apply @mul_left_cancel _ _ _ (mkOf r t hi)
  rw [h.h_lin r t (-t) hi]
  rw [add_neg_cancel t]
  rw [Identity h r hi]
  rw [mul_inv_cancel]
  done

@[simp]
theorem expr_βγ_as_β_comm_γ (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ β.height) (hj : j ≤ γ.height) :
    @mkOf _ _ βγ (t*u) (i+j) (by simp [height] at *; omega) = (mkOf β t hi) * (mkOf γ u hj) * (mkOf β (-t) hi) * (mkOf γ (-u) hj) := by
  rw [Inverse h β t hi]
  rw [Inverse h γ u hj]
  rw [← commutatorElement_def]
  rw [← h.h_βγ t u hi hj]
  done

@[simp]
theorem expr_α_β_as_αβ_β_α (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ α.height) (hj : j ≤ β.height) :
    (mkOf α t hi) * (mkOf β u hj) = (@mkOf _ _ αβ (t*u) (i+j) (by simp [height] at *; omega)) * (mkOf β u hj) * (mkOf α t hi) := by
  rw [← h.h_αβ t u hi hj]
  rw [comm_left_str (mkOf α t hi) (mkOf β u hj)]

theorem expr_α_γ_as_γ_α (h : WeakA3 R) (t u : R) {i j : Nat} (hi : i ≤ α.height) (hj : j ≤ γ.height) :
    (mkOf α t hi) * (mkOf γ u hj) = (mkOf γ u hj) * (mkOf α t hi) := by
  sorry
  done

theorem Interchange (h : WeakA3 R) (t u v : R) {i j k : Nat} (hi : i ≤ Root.α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
  ⁅ @mkOf _ _ αβ (t*u) (i+j) (by simp [height] at *; omega), mkOf Root.γ v hk ⁆ =
    ⁅ mkOf α t hi, @mkOf _ _ Root.βγ (u*v) (j+k) (by simp [height] at *; omega) ⁆ := by
  have : (mkOf α t hi) * (@mkOf _ _ Root.βγ (u*v) (j+k) (by simp [height] at *; omega)) =
   ⁅ mkOf α t hi, @mkOf _ _ Root.βγ (u*v) (j+k) (by simp [height] at *; omega) ⁆ *
    (@mkOf _ _ Root.βγ (u*v) (j+k) (by simp [height] at *; omega)) * (mkOf α t hi) := by
    conv => lhs;
    rw [expr_βγ_as_β_comm_γ h u v hj hk]
    simp_rw [← mul_assoc]
    rw [expr_α_β_as_αβ_β_α h t u hi hj]
    rw [mul_assoc _ (mkOf α t hi) _]
    rw [expr_α_γ_as_γ_α h t v hi hk]
    simp_rw [← mul_assoc]
    rw [mul_assoc _ (mkOf α t hi) _]
    rw [expr_α_β_as_αβ_β_α h t (-u) hi hj]
    simp_rw [← mul_assoc]
    rw [mul_assoc _ (mkOf α t hi) _]
    rw [expr_α_γ_as_γ_α h t (-v) hi hk]
    simp_rw [← mul_assoc]
    -- simp_rw [← mul_assoc]
    --rw [expr_α_γ_as_γ_α h t v hi hk]
    done
  done

end RootedElem

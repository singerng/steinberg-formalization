import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Algebra.Ring.Defs

namespace Steinberg

-- A3PositiveRoots in A3: α, α+β, β, β+γ, γ, and missing α+β+γ

variable {G : Type Tu} [Group G]
         {R : Type Tv} [Ring R]

/- commutator identities (holding in any group) -/

def Deg (i : ℕ) := Fin (i+1)
def deg_add {n m : ℕ} (a : Deg n) (b : Deg m) : Deg (n + m) := ⟨ a.val + b.val, by omega ⟩

theorem comm_left_str  (x y : G)   : x * y = ⁅x, y⁆ * y * x := by group
theorem comm_right_str (x y : G)  : x * y = y * x * ⁅x⁻¹, y⁻¹⁆ := by group

theorem comm_to_comm (x y : G) (h : ⁅x, y⁆ = 1) : x * y = y * x := by
  sorry

theorem comm_on_left (x y z : G) (h : x * y = z * y * x) : ⁅x, y⁆ = z := by
  group
  rw [h]
  group

/- defining the A3 positive root system -/
inductive A3PositiveRoot
  | α | β | γ | αβ | βγ

namespace A3PositiveRoot

def height : A3PositiveRoot → Nat
  | A3PositiveRoot.α => 1
  | A3PositiveRoot.β => 1
  | A3PositiveRoot.γ => 1
  | A3PositiveRoot.αβ => 2
  | A3PositiveRoot.βγ => 2

end A3PositiveRoot

structure A3UnipGen (R : Type v) [Ring R] where
  root : A3PositiveRoot
  coeff : R
  i : Deg root.height   -- CC: These two are equivalent
  -- i : Nat
  -- hi : i ≤ root.height

namespace A3UnipGen

open A3PositiveRoot

/- defining the weak A3 unipotent group -/
def mk' {R : Type Tv} [Ring R] (r : A3PositiveRoot) (coeff : R) (i : Deg r.height) : A3UnipGen R :=
  mk r coeff i

def mkOf {R : Type Tv} [Ring R] (r : A3PositiveRoot) (coeff : R) (i : Deg r.height) := FreeGroup.of <| mk' r coeff i

def Linearity (R : Type Tv) [Ring R] := ∀ (r : A3PositiveRoot) (t u : R) (i : Deg r.height),
    (mkOf r t i) * (mkOf r u i) = (mkOf r (t + u) i)

-- nontrivial commutators
def α_comm_β (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg α.height) (j : Deg β.height),
 ⁅ mkOf α t i, mkOf β u j ⁆ = mkOf αβ (t * u) (deg_add i j)

def β_comm_γ (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg β.height) (j : Deg γ.height),
 ⁅ mkOf β t i, mkOf γ u j ⁆ = mkOf βγ (t * u) (deg_add i j)

-- trivial commutators
def β_comm_αβ (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg β.height) (j : Deg αβ.height),
 ⁅ mkOf β t i, mkOf αβ u j ⁆ = 1

def γ_comm_βγ (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg γ.height) (j : Deg βγ.height),
 ⁅ mkOf γ t i, mkOf βγ u j ⁆ = 1

def α_comm_γ (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg α.height) (j : Deg γ.height),
 ⁅ mkOf α t i, mkOf γ u j ⁆ = 1

def αβ_comm_βγ (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg αβ.height) (j : Deg βγ.height),
 ⁅ mkOf αβ t i, mkOf βγ u j ⁆ = 1

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
theorem Identity (h : WeakA3 R) (r : A3PositiveRoot) (i : Deg r.height) :
    mkOf r (0 : R) i = 1 := by
  apply @mul_left_cancel _ _ _ (mkOf r 0 i)
  rw [mul_one]
  rw [h.h_lin r (0 : R) (0 : R) i]
  rw [add_zero]
  done

-- deduce inverse relations from linearity relations
@[simp]
theorem Inverse (h : WeakA3 R) (r : A3PositiveRoot) (t : R) (i : Deg r.height) :
    mkOf r (-t : R) i = (mkOf r t i)⁻¹ := by
  apply @mul_left_cancel _ _ _ (mkOf r t i)
  rw [h.h_lin r t (-t) i]
  rw [add_neg_cancel t]
  rw [Identity h r i]
  rw [mul_inv_cancel]
  done

-- explicit expressions of commutators
@[simp]
theorem expr_βγ_as_β_comm_γ (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg γ.height) :
    mkOf βγ (t*u) (deg_add i j) = (mkOf β t i) * (mkOf γ u j) * (mkOf β (-t) i) * (mkOf γ (-u) j) := by
  rw [Inverse h β t i]
  rw [Inverse h γ u j]
  rw [← commutatorElement_def]
  rw [← h.h_β_γ t u i j]
  done

-- rewrites for products of noncommuting elements
@[simp]
theorem expr_α_β_as_αβ_β_α (h : WeakA3 R) (t u : R) (i : Deg α.height) (j : Deg β.height) :
    (mkOf α t i) * (mkOf β u j) = (mkOf αβ (t*u) (deg_add i j)) * (mkOf β u j) * (mkOf α t i) := by
  rw [← h.h_α_β t u i j]
  rw [comm_left_str (mkOf α t i) (mkOf β u j)]
  done

@[simp]
theorem expr_β_γ_as_βγ_γ_β (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg γ.height) :
    (mkOf β t i) * (mkOf γ u j) = (mkOf βγ (t*u) (deg_add i j)) * (mkOf γ u j) * (mkOf β t i) := by
  rw [← h.h_β_γ t u i j]
  rw [comm_left_str (mkOf β t i) (mkOf γ u j)]
  done

-- rewrites for products of commuting elements
@[simp]
theorem expr_α_γ_as_γ_α (h : WeakA3 R) (t u : R) (i : Deg α.height) (j : Deg γ.height) :
    (mkOf α t i) * (mkOf γ u j) = (mkOf γ u j) * (mkOf α t i) := by
  apply comm_to_comm
  rw [h.h_α_γ]
  done

@[simp]
theorem expr_β_αβ_as_αβ_β (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg αβ.height) :
    (mkOf β t i) * (mkOf αβ u j) = (mkOf αβ u j) * (mkOf β t i) := by
  apply comm_to_comm
  rw [h.h_β_αβ]
  done

@[simp]
theorem expr_γ_βγ_as_βγ_γ (h : WeakA3 R) (t u : R) (i : Deg γ.height) (j : Deg βγ.height) :
    (mkOf γ t i) * (mkOf βγ u j) = (mkOf βγ u j) * (mkOf γ t i) := by
  apply comm_to_comm
  rw [h.h_γ_βγ]
  done

@[simp]
theorem expr_αβ_βγ_as_βγ_αβ (h : WeakA3 R) (t u : R) (i : Deg αβ.height) (j : Deg βγ.height) :
    (mkOf αβ t i) * (mkOf βγ u j) = (mkOf βγ u j) * (mkOf αβ t i) := by
  apply comm_to_comm
  rw [h.h_αβ_βγ]
  done

-- interchange theorem, ⁅α, βγ⁆ = ⁅αβ, γ⁆
theorem Interchange (h : WeakA3 R) (t u v : R) (i : Deg α.height) (j : Deg β.height) (k : Deg γ.height) :
    ⁅ mkOf α t i, mkOf βγ (u*v) (deg_add j k) ⁆ =
    ⁅ mkOf αβ (t*u) (deg_add i j), mkOf γ v k ⁆:= by
  apply comm_on_left
  conv => lhs;
  -- phase I: push α to right
  rw [expr_βγ_as_β_comm_γ h u v j k]
  simp_rw [← mul_assoc]
  rw [expr_α_β_as_αβ_β_α h t u i j]
  rw [mul_assoc _ (mkOf α t i) _]
  rw [expr_α_γ_as_γ_α h t v i k]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (mkOf α t i) _]
  rw [expr_α_β_as_αβ_β_α h t (-u) i j]
  rw [mul_neg] -- rewrite t*(-u) as -(t*u)
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (mkOf α t i) _]
  rw [expr_α_γ_as_γ_α h t (-v) i k]
  simp_rw [← mul_assoc]
  -- phase II: move β's together
  rw [mul_assoc _ (mkOf β u j) _]
  rw [expr_β_γ_as_βγ_γ_β h u v j k]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (mkOf β u j) _]
  rw [expr_β_αβ_as_αβ_β h u (-(t*u)) j]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (mkOf β u j) _]
  rw [Inverse h β]
  group
  -- phase III: push βγ to the right
  rw [mul_assoc _ (@mkOf _ _ βγ (u*v) (deg_add j k)) _]
  rw [← expr_γ_βγ_as_βγ_γ]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (@mkOf _ _ βγ (u*v) (deg_add j k)) _]
  rw [← expr_αβ_βγ_as_βγ_αβ]
  simp_rw [← mul_assoc]
  rw [mul_assoc _ (@mkOf _ _ βγ (u*v) (deg_add j k)) _]
  rw [← expr_γ_βγ_as_βγ_γ]
  simp_rw [← mul_assoc]
  repeat rw [Inverse]
  rw [← commutatorElement_def]
  sorry

theorem InterchangeEmpty (h : WeakA3 R) (t v : R) (i : Deg α.height) (j : Deg β.height) (k : Deg γ.height) :
    ⁅ mkOf α t i, mkOf βγ v (deg_add j k) ⁆ =
    ⁅ mkOf αβ t (deg_add i j), mkOf γ v k ⁆ := by
    nth_rewrite 1 [← one_mul v]
    nth_rewrite 2 [← mul_one t]
    rw [Interchange h]
    done

def mkαβγ {R : Type Tv} [Ring R] (t : R) (i : Deg 3) :=
⁅ (mkOf α t (0 : Fin 2)), (mkOf βγ (1 : R) (0 : Fin 3)) ⁆
-- ⁅ (mkOf α t (0 : Deg 1)), (mkOf βγ (1 : R) (0 : Deg 2)) ⁆
-- match i.val with
--   | 0 => ⁅ (mkOf 0 (by simp [height] at *)), (@mkOf _ _ βγ (1 : R) 0 (by simp [height] at *)) ⁆
--   | 1 => ⁅ (@mkOf _ _ α t 0 (by simp [height] at *)), (@mkOf _ _ βγ (1 : R) 1 (by simp [height] at *)) ⁆
--   | 2 => ⁅ (@mkOf _ _ α t 0 (by simp [height] at *)), (@mkOf _ _ βγ (1 : R) 2 (by simp [height] at *)) ⁆
--   | 3 => ⁅ (@mkOf _ _ α t 1 (by simp [height] at *)), (@mkOf _ _ βγ (1 : R) 2 (by simp [height] at *)) ⁆

-- theorem comm_α_βγ_0 (h : WeakA3 R) (t u : R) :
--   ⁅@mkOf _ _ α t 0 (by simp [height] at *), @mkOf _ _ βγ u 0 (by simp [height] at *)⁆ =
--   @mkαβγ _ _ (t * u) 0 := by
--   -- rw [mkαβγ (t*u) 0]
--   nth_rewrite 1 [← one_mul u]
--   rw [Interchange h t 1 u]
--   sorry


-- theorem comm_α_βγ [Ring R] (t u : R) {i j : Nat} (hi : i ≤ α.height) (hj : j ≤ βγ.height) :
--   ⁅mkOf α t hi, mkOf βγ u hj⁆ = @mkαβγ _ _ (t * u) (i+j) (by simp [height] at *; omega) := by
--   simp_rw [Interchange, mul_one]
--   sorry

end A3UnipGen

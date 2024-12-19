import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Ring.Defs

import Steinberg.Defs.Root
import Steinberg.Defs.Chevalley
import Steinberg.Defs.Deg
import Steinberg.Defs.Commutator
import Steinberg.Macro.Group


namespace Steinberg

open Steinberg.Macro

/-!
A formalization of a certain presentation of a variant of the group of 4x4 unipotent matrices.
A unipotent matrix has 1's on the diagonal, 0's below the diagonal, and arbitrary entries from some ring above the diagonal.

In our group, the entries are *polynomials* with `R` coefficients, i.e., the ring `R[x]` where `R` is a ring and
`x` is an indeterminate. Specifically, we consider the group where every matrix position of "height" `i` has an
entry of degree at most `i`, where the "height" of a position is the taxicab distance to the diagonal.

We label the entries thusly:

(1   α   αβ  αβγ )
(0   1   β   βγ  )
(0   0   1   γ   )
(0   0   0   1   )

Note that α, β, and γ have height 1, αβ and βγ have height 2, and αβγ has height 3. Thus, the α, β, and γ entries are linear
polynomials with `R` coefficients; αβ and βγ are quadratic; and αβγ is cubic. The positions α, β, etc. are also called "roots".

In our group presentation, the generators are of the form {`r` `t` `i`}, where `r` is one of α, β, γ, αβ, or βγ; `t` is in `R`
(an arbitrary ring); and `i` is between 0 and height(`r`) inclusive. Such a generator corresponds to a unipotent matrix with a single homogeneous
entry, `tx^i`, in the `r` position. We consider a certain set of relations which these generators satisfy, and prove from these
all relations characterizing interactions of single-homogeneous-entry-above-diagonal unipotent matrices. (These, in turn,
form a canonical presentation of the entire group.)

The important theorem in this file is `StrongGradedA3_of_WeakGradedA3` below, which states that if a group on
`A3GradedGen` elements satisfies the relations listed in the `WeakGradedA3` structure below, then it also
satisfies the relations listed in `StrongGradedA3` below.
-/

variable {G : Type Tu} [Group G]
         {R : Type Tv} [Ring R]

/-! ### Defining the A3 positive root system -/

inductive A3PosRoot
  | α | β | γ | αβ | βγ | αβγ

namespace A3PosRoot

@[reducible]
def height : A3PosRoot → Nat
  | α => 1
  | β => 1
  | γ => 1
  | αβ => 2
  | βγ => 2
  | αβγ => 3

def toString : A3PosRoot → String
  | α => "α"
  | β => "β"
  | γ => "γ"
  | αβ => "α+β"
  | βγ => "β+γ"
  | αβγ => "α+β+γ"

@[reducible]
def isPresent : A3PosRoot → Bool
  | αβγ => false
  | _ => true

def add : A3PosRoot → A3PosRoot → Option A3PosRoot
  | α, β => some αβ
  | β, γ => some βγ
  | α, βγ => some αβγ
  | αβ, γ => some αβγ
  | _, _ => none

def mul : PNat → A3PosRoot → Option A3PosRoot := fun _ _ => none

def maker (ζ : A3PosRoot) (i : ℕ) : A3PosRoot × ℕ × A3PosRoot × ℕ :=
  match (ζ, i) with
  | (αβγ, 0) => (α, 0, βγ, 0)
  | (αβγ, 1) => (α, 0, βγ, 1)
  | (αβγ, 2) => (α, 0, βγ, 2)
  | (αβγ, 3) => (α, 1, βγ, 2)
  | (_, _) => (αβγ, 1000000, αβγ, 10000000) -- NS: junk. We should really tweak this...

theorem h_add {r₁ r₂ r₃ : A3PosRoot} :
  (add r₁ r₂ = some r₃) → height r₃ = height r₁ + height r₂ := by
  sorry

theorem h_mul {c : PNat} {r r' : A3PosRoot} :
  (mul c r = r') → height r' = c * height r := by sorry

theorem h_maker {r : A3PosRoot} (hζ : ¬isPresent r) {i : Nat} (hi : i ≤ height r) :
  isPresent (maker r i).1
    ∧ isPresent (maker r i).2.2.1
    ∧ (maker r i).2.1 ≤ height (maker r i).1
    ∧ (maker r i).2.2.2 ≤ height (maker r i).2.2.1
    ∧ (maker r i).2.1 + (maker r i).2.2.2 = i
    ∧ add (maker r i).1 (maker r i).2.2.1 = r := by
  sorry

instance : PosRootSys A3PosRoot where
  height := height
  isPresent := isPresent
  add := add
  mul := mul
  toString := toString
  h_add := h_add
  h_mul := h_mul
  maker := maker
  h_maker := h_maker

end A3PosRoot

namespace A3GradedGen

open A3PosRoot WeakGradedGen

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" => mkOf ζ i (by (try simp [PosRootSys.height] at *; try simp [A3PosRoot.height] at *; first | trivial | omega)) t

-- #eval { α, 0, (1 : R) }

--scoped notation "|" ζ ", " i ", " hi ", " t "|" => A3GradedGen.mkOf ζ i hi t
/-
open Lean in
set_option hygiene false in
macro "declare_trivial_commutator" rootOne:ident rootTwo:ident : command => do
  let thmName := ($rootOne : A3PosRoot).toString ++ "_comm_" ++ ($rootTwo : A3PosRoot).toString
  let mut cmds ← Syntax.getArgs <$> `(
    def $thmName (R : Type Tv) [Ring R] :=
      ∀ (t u : R) (i : Deg $rootOne.height) (j : Deg $rootTwo.height),
        ⁅ { $rootOne, i, t }, { $rootTwo, j, u } ⁆ = 1
  )
  return (mkNullNode cmds) -/

/-! ### Bundle together assumptions about the A3 generators -/

/-
The specific relation arises from "nonhomogeneously lifting" the commutator of αβ and βγ elements. (There is no analogue
of this relation for other root-pairs, since all other present pairs lie in a common two-dimensional subspace.)
-/
def comm_of_αβ_βγ_nonhomog_lift (R : Type Tv) [Ring R] : Prop :=
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : R),
    ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀}, {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} ⁆ = 1

structure WeakGradedA3 (R : Type Tv) [Ring R] where
  h_lin_of_present : lin_of_present R A3PosRoot
  h_mixed_commutes_of_present : mixed_commutes_of_present R A3PosRoot
  h_comm_of_α_β : single_commutator_of_root_pair α β αβ (1 : R) (by rfl)
  h_comm_of_β_γ : single_commutator_of_root_pair β γ βγ (1 : R) (by rfl)
  h_comm_of_α_γ : trivial_commutator_of_root_pair R α γ
  h_comm_of_α_αβ : trivial_commutator_of_root_pair R α αβ
  h_comm_of_β_αβ : trivial_commutator_of_root_pair R β αβ
  h_comm_of_β_βγ : trivial_commutator_of_root_pair R β βγ
  h_comm_of_γ_βγ : trivial_commutator_of_root_pair R γ βγ
  h_nonhomog_lift_of_comm_of_αβ_βγ : comm_of_αβ_βγ_nonhomog_lift R

structure StrongGradedA3 (R : Type Tv) [Ring R] extends WeakGradedA3 R where
  h_comm_of_αβ_βγ : trivial_commutator_of_root_pair R αβ βγ
  h_comm_of_αβ_γ : single_commutator_of_root_pair αβ γ αβγ (1 : R) (by rfl)
  h_comm_of_α_βγ : single_commutator_of_root_pair α βγ αβγ (1 : R) (by rfl)
  h_comm_of_α_αβγ : trivial_commutator_of_root_pair R α αβγ
  h_comm_of_β_αβγ : trivial_commutator_of_root_pair R β αβγ
  h_comm_of_γ_αβγ : trivial_commutator_of_root_pair R γ αβγ
  h_comm_of_αβ_αβγ : trivial_commutator_of_root_pair R αβ αβγ
  h_comm_of_βγ_αβγ : trivial_commutator_of_root_pair R βγ αβγ
  h_mixed_commutes_of_αβγ : mixed_commutes_of_root R αβγ
  h_lin_of_αβγ : lin_of_root R αβγ

/-! ## Analysis of the group -/

/-! ### General deduction rules for relations  (GENERIC) -/

/- Deduce identity relations from linearity relations (for present roots) -/
theorem id_of_present (h : WeakGradedA3 R) (ζ : A3PosRoot) :
    ζ.isPresent → id_of_root R ζ := by
  intro h_pres i hi
  apply @mul_left_cancel _ _ _ {ζ, i, 0}
  rw [mul_one, h.h_lin_of_present, add_zero]
  exact h_pres

/- Deduce inverse relations from linearity relations (for present roots) -/
theorem inv_of_present (h : WeakGradedA3 R) (ζ : A3PosRoot):
    ζ.isPresent → inv_of_root R ζ := by
  intro h_pres i hi t
  apply @mul_left_cancel _ _ _ {ζ, i, t}
  group
  rw [h.h_lin_of_present]
  rw [add_neg_cancel]
  apply id_of_present h
  exact h_pres
  exact h_pres

/-! ### Linearity theorems for specific roots -/

section SpecificRoots

theorem lin_of_α (h : WeakGradedA3 R) : lin_of_root R α :=
  h.h_lin_of_present α rfl

/-! ### Identity theorems for specific roots -/

theorem id_of_αβ (h : WeakGradedA3 R) : id_of_root R αβ :=
  id_of_present h αβ rfl

theorem id_of_βγ (h : WeakGradedA3 R) : id_of_root R βγ :=
  id_of_present h βγ rfl

/-! ### Inverse theorems for specific roots -/

theorem inv_of_α (h : WeakGradedA3 R) : inv_of_root R α :=
  inv_of_present h α rfl

theorem inv_of_β (h : WeakGradedA3 R) : inv_of_root R β :=
  inv_of_present h β rfl

theorem inv_of_γ (h : WeakGradedA3 R) : inv_of_root R γ :=
  inv_of_present h γ rfl

theorem inv_of_αβ (h : WeakGradedA3 R) : inv_of_root R αβ :=
  inv_of_present h αβ rfl

theorem inv_of_βγ (h : WeakGradedA3 R) : inv_of_root R βγ :=
  inv_of_present h βγ rfl

end SpecificRoots

/-! ### Mixed-degree theorem for specific roots -/
theorem mixed_commutes_of_βγ (h : WeakGradedA3 R) : mixed_commutes_of_root R βγ := by
  apply h.h_mixed_commutes_of_present βγ
  rfl

/-! ### Derive full commutator for αβ and βγ from nonhomogeneous lift -/

-- NS: this section should probably be abstracted for reuse

/- Commutator relation in the case (i,j) is not (0,2) or (2,0) (via the previous theorem). -/
theorem homog_lift_of_comm_of_αβ_βγ (h : WeakGradedA3 R) (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
  ∀ (t u : R), ⁅ { αβ, i + j, t}, {βγ, j + k, u} ⁆ = 1 := by
    intro t u
    let t₁ : R := match i with
      | 1 => t
      | 0 => 0
    let t₀ : R := match i with
      | 1 => 0
      | 0 => t
    let u₁ : R := match j with
      | 1 => 1
      | 0 => 0
    let u₀ : R := match j with
      | 1 => 0
      | 0 => 1
    let v₁ : R := match k with
      | 1 => u
      | 0 => 0
    let v₀ : R := match k with
      | 1 => 0
      | 0 => u
    have hf_i : i ∈ [0,1] := by simp; omega
    have hf_j : j ∈ [0,1] := by simp; omega
    have hf_k : k ∈ [0,1] := by simp; omega
    have id₁ : {αβ, i + j, t} = {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp [t₀, t₁, u₀, u₁, v₀, v₁]
        repeat rw [id_of_αβ h]
        simp
      )
    )
    have id₂ : {βγ, j + k, u} = {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp [t₀, t₁, u₀, u₁, v₀, v₁]
        repeat rw [id_of_βγ h]
        simp
      )
    )
    rw [id₁]
    rw [id₂]
    rw [h.h_nonhomog_lift_of_comm_of_αβ_βγ]

/- Every (i, j) ∈ (Deg 2 × Deg 2) can be written as (i' + j', j' + k') for i', j', k' ∈ Deg 1, except (0, 2) and (2, 0) -/
def cube : Finset (ℕ × ℕ × ℕ) := {0, 1} ×ˢ {0, 1} ×ˢ {0, 1}
theorem bound_of_cube (ijk : ℕ × ℕ × ℕ) (hi : ijk ∈ cube) :
  let ⟨ i, j, k ⟩ := ijk; i ≤ 1 ∧ j ≤ 1 ∧ k ≤ 1 := by
  fin_cases hi
  all_goals (simp)

def f_ij_jk : ℕ × ℕ × ℕ → ℕ × ℕ := (fun ijk' : ℕ × ℕ × ℕ => let ( i', j', k' ) := ijk'; (i' + j', j' + k'))
def ij_jk_image : Finset (ℕ × ℕ) := {(0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2)}

theorem correct_of_ij_jk_image : (Finset.image f_ij_jk cube) = ij_jk_image := by decide

theorem image_of_homog_lift_of_comm_of_αβ_βγ (h : WeakGradedA3 R) (i j : ℕ) (hi : i ≤ αβ.height) (hj : j ≤ βγ.height) :
  ((i, j) ∈ ij_jk_image) → ∀ (t u : R), ⁅ {αβ, i, t}, {βγ, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  have ⟨ ijk', ⟨ h_in_cube, h_f ⟩ ⟩ := this
  have ⟨ hi', hj', hk' ⟩ := bound_of_cube ijk' h_in_cube
  let ⟨ i', j', k' ⟩ := ijk'
  have h_f' : i = i' + j' ∧ j = j' + k' := by (
    rw [← Prod.mk.injEq]
    rw [← h_f]
    rw [f_ij_jk]
  )
  rw [← homog_lift_of_comm_of_αβ_βγ h i' j' k' hi' hj' hk' t u]
  simp [h_f']

theorem comm_of_αβ_βγ_20 (h : WeakGradedA3 R) : ∀ (t u : R), ⁅ {αβ, 2, t}, {βγ, 0, u} ⁆ = 1 := by
  intro t u
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {βγ, 1, u} _ ({αβ, 1, t + 1} * {αβ, 0, 1})
  mul_assoc_l
  rw [← h.h_nonhomog_lift_of_comm_of_αβ_βγ t 1 1 1 0 u]
  simp
  rw [id_of_βγ h] -- NS: maybe should be a simp lemma? we can decide...
  simp
  rw [← homog_lift_of_comm_of_αβ_βγ h 1 1 0 (by trivial) (by trivial) (by trivial) t u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_αβ_βγ h 0 1 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_αβ_βγ h 0 0 1 (by trivial) (by trivial) (by trivial) 1 u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_αβ_βγ h 1 0 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_αβ_βγ h 0 0 0 (by trivial) (by trivial) (by trivial) 1 u]

-- symmetric to prior proof
theorem comm_of_αβ_βγ_02 (h : WeakGradedA3 R) :
  ∀ (t u : R),
    ⁅ {αβ, 0, t}, {βγ, 2, u} ⁆ = 1 := by sorry

theorem comm_of_αβ_βγ (h : WeakGradedA3 R) : trivial_commutator_of_root_pair R αβ βγ := by
  intro i j hi hj t u
  have : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ ((i, j) ∈ ij_jk_image) := by
    rw [ij_jk_image]
    simp [PosRootSys.height] at *
    simp [A3PosRoot.height] at *
    omega
  rcases this with hij | hij | hij
  ·
    let ⟨ hd_i, hd_j ⟩ := hij
    simp_rw [hd_i, hd_j]
    rw [← comm_of_αβ_βγ_02 h t u]
  ·
    let ⟨ hd_i, hd_j ⟩ := hij
    simp_rw [hd_i, hd_j]
    rw [← comm_of_αβ_βγ_20 h t u]
  ·
    apply image_of_homog_lift_of_comm_of_αβ_βγ h i j hi hj
    exact hij

/-! ### Further useful identities (roughly GENERIC) -/

/- Expand βγ as β⬝γ⬝β⬝γ. -/
theorem expand_βγ_as_β_γ_β_γ (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R),
      {βγ, i + j, (t * u)} = {β, i, t} * {γ, j, u} * {β, i, (-t)} * {γ, j, (-u)} := by
  intro i j hi hj t u
  rw [inv_of_β h]
  rw [inv_of_γ h]
  rw [← commutatorElement_def]
  rw [← one_mul (t * u)]
  rw [← h.h_comm_of_β_γ]

/- Rewrite α⬝β as αβ⬝β⬝α. -/
theorem expr_α_β_as_αβ_β_α (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (t u : R),
      reorder_left({α, i, t}, {β, j, u}, {αβ, (i + j), (t*u)}) := by
  intro i j hi hj t u
  rw [← one_mul (t * u)]
  rw [← h.h_comm_of_α_β]
  rw [comm_left]

/- Rewrite β⬝γ as βγ⬝γ⬝β. -/
theorem expr_β_γ_as_βγ_γ_β (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R), reorder_left({β, i, t}, {γ, j, u}, {βγ, (i + j), (t*u)}) := by
  intro i j hi hj t u
  rw [← one_mul (t * u)]
  rw [← h.h_comm_of_β_γ]
  rw [comm_left]

/- Rewrite β⬝γ as γ⬝βγ⬝β. -/
theorem expr_β_γ_as_γ_βγ_β (h : WeakGradedA3 R) :
  ∀ (i j : ℕ) (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R), reorder_mid({β, i, t}, {γ, j, u}, {βγ, (i + j), (t*u)}) := by
  intro i j hi hj t u
  rw [← one_mul (t * u)]
  rw [← h.h_comm_of_β_γ i j hi hj]
  rw [comm_mid]
  rw [← inv_of_γ h]
  rw [h.h_comm_of_β_γ]
  rw [← inv_of_βγ h]
  simp
  rw [h.h_comm_of_β_γ]
  simp

/- Rewrite α⬝γ as γ⬝α. -/
theorem expr_α_γ_as_γ_α (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ α.height) (hj : j ≤ γ.height) (t u : R), commutes({α, i, t}, {γ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [h.h_comm_of_α_γ]

/- Rewrite α⬝αβ as αβ⬝α. -/
theorem expr_α_αβ_as_αβ_α (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ α.height) (hj : j ≤ αβ.height) (t u : R), commutes({α, i, t}, {αβ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [h.h_comm_of_α_αβ]

/- Rewrite β⬝αβ as αβ⬝β. -/
theorem expr_β_αβ_as_αβ_β (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ β.height) (hj : j ≤ αβ.height) (t u : R), commutes({β, i, t}, {αβ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [h.h_comm_of_β_αβ]

/- Rewrite γ⬝βγ as βγ⬝γ. -/
theorem expr_γ_βγ_as_βγ_γ (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ γ.height) (hj : j ≤ βγ.height) (t u : R), commutes({γ, i, t}, {βγ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [h.h_comm_of_γ_βγ]

/- Rewrite αβ⬝βγ as βγ⬝αβ. -/
theorem expr_αβ_βγ_as_βγ_αβ (h : WeakGradedA3 R) :
  ∀ (i j : ℕ) (hi : i ≤ αβ.height) (hj : j ≤ βγ.height) (t u : R), commutes({αβ, i, t}, {βγ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [comm_of_αβ_βγ h]

/-! ### Interchange theorems between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms -/

/- Interchange between ⁅α, βγ⁆ and ⁅αβ, γ⁆, "trading" a single degree j : Deg 1 and scalar u : R. -/
theorem Interchange (h : WeakGradedA3 R) (i j k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
    ∀ (t u v : R), ⁅ {α, i, t}, {βγ, j + k, u * v} ⁆ = ⁅ {αβ, i + j, t * u}, {γ, k, v} ⁆ := by
  intro t u v
  apply eq_comm_of_reorder_left
  have hij : i + j ≤ αβ.height := by simp [height] at *; omega
  have hjk : j + k ≤ βγ.height := by simp [height] at *; omega
  -- phase I: push α to right
  conv =>
    lhs
    rw [expand_βγ_as_β_γ_β_γ h j k hj hk]
    simp [← mul_assoc]
    rw [expr_α_β_as_αβ_β_α h i j hi hj]
    rw [mul_assoc _ {α, i, t}]
    rw [expr_α_γ_as_γ_α h i k hi hk]
    simp [← mul_assoc]
    rw [mul_assoc _ {α, i, t}]
    rw [expr_α_β_as_αβ_β_α h i j hi hj]
    rw [mul_neg] -- rewrite t*(-u) as -(t*u)
    simp [← mul_assoc]
    rw [mul_assoc _ {α, i, t}]
    rw [expr_α_γ_as_γ_α h i k hi hk]
    simp [← mul_assoc]
    -- phase II: move β's together
    rw [mul_assoc _ {β, j, u}]
    rw [expr_β_γ_as_βγ_γ_β h j k hj hk]
    simp [← mul_assoc]
    rw [mul_assoc _ {β, j, u}]
    rw [expr_β_αβ_as_αβ_β h j (i + j) hj hij]
    simp [← mul_assoc]
    rw [mul_assoc _ {β, j, u}]
  rw [inv_of_β h]
  group
  conv =>
    lhs
    -- phase III: push βγ to the right
    rw [mul_assoc _ {βγ, (j + k), u * v}]
    rw [← expr_γ_βγ_as_βγ_γ h k (j + k) hk hjk]
    simp [← mul_assoc]
    rw [mul_assoc _ {βγ, (j + k), u * v}]
    rw [← expr_αβ_βγ_as_βγ_αβ h (i + j) (j + k) hij hjk]
    simp [← mul_assoc]
    rw [mul_assoc _ {βγ, (j + k), u * v}]
    rw [← expr_γ_βγ_as_βγ_γ h k (j + k) hk hjk]
    simp [← mul_assoc]
    repeat rw [inv_of_present h]
  group

/- Pass between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms (specializes `Interchange` to the case `u=1`). -/
theorem InterchangeTrans (h : WeakGradedA3 R) (i j k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
    ∀ (t u : R), ⁅ {α, i, t}, {βγ, (j + k), u} ⁆ = ⁅ {αβ, (i + j), t}, {γ, k, u} ⁆ := by
  intro t u
  nth_rewrite 1 [← one_mul u]
  nth_rewrite 2 [← mul_one t]
  rw [Interchange h i j k hi hj hk]

/- ⁅α,βγ⁆ forms depend only on product of coefficients. Applies `Interchange` twice. -/
theorem InterchangeRefl (h : WeakGradedA3 R) (i j k : ℕ) (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
    ∀ (t u : R), ⁅ {α, i, 1 * (t * u)}, {βγ, (j + k), 1} ⁆ = ⁅ {α, i, t}, {βγ, (j + k), u} ⁆ := by
  intro t u
  nth_rewrite 2 [← mul_one u]
  rw [Interchange h i j k hi hj hk]
  rw [InterchangeTrans h i j k hi hj hk]
  rw [one_mul]

/-! ### Commutator relations for (α,βγ) and (αβ,γ) via interchange relations -/

-- NS: Really need to figure out a more sane way to write this section.

-- height 0
theorem comm_of_α_βγ_00 (h : WeakGradedA3 R) (t u : R) : ⁅ {α, 0, t}, {βγ, 0, u} ⁆ = {αβγ, 0 + 0, 1*(t*u)} := by
  rw [← InterchangeRefl h 0 0 0 (by trivial) (by trivial) (by trivial)]
  simp only [mkOf, PosRootSys.isPresent, PosRootSys.height, A3PosRoot.height, A3PosRoot.isPresent, A3PosRoot.maker, A3PosRoot.h_maker]
  simp_all
  split
  simp_all

theorem comm_of_αβ_γ_00 (h : WeakGradedA3 R) (t u : R) : ⁅ {αβ, 0, t}, {γ, 0, u} ⁆ = {αβγ, 0 + 0, 1*(t*u)} := by
  rw [← InterchangeTrans h 0 0 0]
  rw [comm_of_α_βγ_00 h]
  simp

-- height 1
theorem comm_of_α_βγ_01 (h : WeakGradedA3 R) (t u : R) : ⁅ {α, 0, t}, {βγ, 1, u} ⁆ = {αβγ, 0 + 1, 1*(t*u)} := by
  rw [← InterchangeRefl h 0 0 1]
  simp [mkOf]
  repeat simp [*] at *
theorem comm_of_αβ_γ_10 (h : WeakGradedA3 R) (t u : R) : ⁅ {αβ, 1, t}, {γ, 0, u} ⁆ = {αβγ, 1 + 0, 1*(t*u)} := by
  rw [← InterchangeTrans h 0 1 0]
  rw [comm_of_α_βγ_01 h]
  simp
theorem comm_of_α_βγ_10 (h : WeakGradedA3 R) (t u : R) : ⁅ {α, 1, t}, {βγ, 0, u} ⁆ = {αβγ, 1 + 0, 1*(t*u)} := by
  rw [InterchangeTrans h 1 0 0]
  rw [comm_of_αβ_γ_10 h]
  simp
theorem comm_of_αβ_γ_01 (h : WeakGradedA3 R) (t u : R) : ⁅ {αβ, 0, t}, {γ, 1, u} ⁆ = {αβγ, 0 + 1, 1*(t*u)} := by
  rw [← InterchangeTrans h 0 0 1]
  rw [comm_of_α_βγ_01 h]
  simp

-- height 2
theorem comm_of_α_βγ_11 (h : WeakGradedA3 R) (t u : R) : ⁅ {α, 1, t}, {βγ, 1, u} ⁆ = {αβγ, 1 + 1, 1*(t*u)} := by
  rw [← InterchangeRefl h 1 0 1]
  simp [mkOf]
  repeat simp [*] at *
theorem comm_of_αβ_γ_11 (h : WeakGradedA3 R) (t u : R) : ⁅ {αβ, 1, t}, {γ, 1, u} ⁆ = {αβγ, 1 + 1, 1*(t*u)} := by
  rw [← InterchangeTrans h 1 0 1]
  rw [comm_of_α_βγ_11 h]
  simp
theorem comm_of_α_βγ_02 (h : WeakGradedA3 R) (t u : R) : ⁅ {α, 0, t}, {βγ, 2, u} ⁆ = {αβγ, 0 + 2, 1*(t*u)} := by
  rw [InterchangeTrans h 0 1 1]
  rw [comm_of_αβ_γ_11 h]
  simp
theorem comm_of_αβ_γ_20 (h : WeakGradedA3 R) (t u : R) : ⁅ {αβ, 2, t}, {γ, 0, u} ⁆ = {αβγ, 2 + 0, 1*(t*u)} := by
  rw [← InterchangeTrans h 1 1 0]
  rw [comm_of_α_βγ_11 h]
  simp

-- height 3
theorem comm_of_α_βγ_12 (h : WeakGradedA3 R) (t u : R) : ⁅ {α, 1, t}, {βγ, 2, u} ⁆ = {αβγ, 1 + 2, 1*(t*u)} := by
  rw [← InterchangeRefl h 1 1 1]
  simp [mkOf]
  repeat simp [*] at *
theorem comm_of_αβ_γ_21 (h : WeakGradedA3 R) (t u : R) : ⁅ {αβ, 2, t}, {γ, 1, u} ⁆ = {αβγ, 2 + 1, 1*(t*u)} := by
  rw [← InterchangeTrans h 1 1 1]
  rw [comm_of_α_βγ_12 h]
  simp

/- Commutator relation for α and βγ. -/
theorem comm_of_α_βγ (h : WeakGradedA3 R) : single_commutator_of_root_pair α βγ αβγ (1 : R) (by simp [PosRootSys.height] at *; simp [A3PosRoot.height] at *) := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => exact comm_of_α_βγ_00 h t u
  | 0, 1 => exact comm_of_α_βγ_01 h t u
  | 0, 2 => exact comm_of_α_βγ_02 h t u
  | 1, 0 => exact comm_of_α_βγ_10 h t u
  | 1, 1 => exact comm_of_α_βγ_11 h t u
  | 1, 2 => exact comm_of_α_βγ_12 h t u

/- Commutator relation for αβ and γ. -/
theorem comm_of_αβ_γ (h : WeakGradedA3 R) : single_commutator_of_root_pair αβ γ αβγ (1 : R) (by simp [PosRootSys.height] at *; simp [A3PosRoot.height] at *) := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => exact comm_of_αβ_γ_00 h t u
  | 1, 0 => exact comm_of_αβ_γ_10 h t u
  | 2, 0 => exact comm_of_αβ_γ_20 h t u
  | 0, 1 => exact comm_of_αβ_γ_01 h t u
  | 1, 1 => exact comm_of_αβ_γ_11 h t u
  | 2, 1 => exact comm_of_αβ_γ_21 h t u

/-! ### More rewriting theorems -/

/- Expand αβγ as α⬝βγ⬝α⬝βγ. -/
theorem expand_αβγ_as_α_βγ_α_βγ (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ α.height) (hj : j ≤ βγ.height) (t u : R),
      {αβγ, (i + j), (t * u)} = {α, i, t} * {βγ, j, u} * {α, i, (-t)} * {βγ, j, (-u)} := by
  intro i j hi hj t u
  rw [inv_of_α h]
  rw [inv_of_βγ h]
  rw [← commutatorElement_def]
  rw [← one_mul (t * u)]
  rw [← comm_of_α_βγ h]

/- Expand αβγ as αβ⬝γ⬝αβ⬝γ. -/
theorem expand_αβγ_as_αβ_γ_αβ_γ (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ αβ.height) (hj : j ≤ γ.height) (t u : R),
      {αβγ, (i + j), (t * u)} = {αβ, i, t} * {γ, j, u} * {αβ, i, (-t)} * {γ, j, (-u)} := by
  intro i j hi hj t u
  rw [inv_of_αβ h]
  rw [inv_of_γ h]
  rw [← commutatorElement_def]
  rw [← one_mul (t * u)]
  rw [← comm_of_αβ_γ h]

/-! ### Commutators of αβγ with other roots -/

/- α and αβγ commute. -/
/- NS: One should be able to prove this quite simply:  simple proof: we know αβγ is expressible as a product of αβ's and γ's (expand_αβγ_as_αβ_γ_αβ_γ), and we know that α's
   commute with αβ's (expr_α_αβ_as_αβ_α) and γ's (expr_α_γ_as_γ_α) -/
theorem comm_of_α_αβγ (h : WeakGradedA3 R) : trivial_commutator_of_root_pair R α αβγ := by
  intro i j hi hj t u
  apply triv_comm_of_commutes
  let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose αβ.height γ.height j (by trivial)
  simp_rw [h_eq]
  rw [← one_mul u]
  rw [expand_αβγ_as_αβ_γ_αβ_γ h j₁ j₂ hj₁ hj₂]
  mul_assoc_l
  rw [expr_α_αβ_as_αβ_α h i j₁ hi hj₁]
  rw [mul_assoc _ {α, i, t}]
  rw [expr_α_γ_as_γ_α h i j₂ hi hj₂]
  mul_assoc_l
  rw [mul_assoc _ {α, i, t}]
  rw [expr_α_αβ_as_αβ_α h i j₁ hi hj₁]
  mul_assoc_l
  rw [mul_assoc _ {α, i, t}]
  rw [expr_α_γ_as_γ_α h i j₂ hi hj₂]
  mul_assoc_l

/- γ and αβγ commute. -/
theorem comm_of_γ_αβγ (h : WeakGradedA3 R) : trivial_commutator_of_root_pair R γ αβγ := by
  intro i j hi hj t u
  apply triv_comm_of_commutes
  let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose α.height βγ.height j (by trivial)
  simp_rw [h_eq]
  rw [← one_mul u]
  rw [expand_αβγ_as_α_βγ_α_βγ h j₁ j₂ hj₁ hj₂]
  mul_assoc_l
  rw [← expr_α_γ_as_γ_α h j₁ i hj₁ hi]
  rw [mul_assoc _ {γ, i, t}]
  rw [expr_γ_βγ_as_βγ_γ h i j₂ hi hj₂]
  mul_assoc_l
  rw [mul_assoc _ {γ, i, t}]
  rw [← expr_α_γ_as_γ_α h j₁ i hj₁ hi]
  mul_assoc_l
  rw [mul_assoc _ {γ, i, t}]
  rw [expr_γ_βγ_as_βγ_γ h i j₂ hi hj₂]
  mul_assoc_l

/- β and αβγ commute. -/
-- the only commutator proof where we have to do something 'interesting'
theorem comm_of_β_αβγ (h : WeakGradedA3 R) : trivial_commutator_of_root_pair R β αβγ := by
  intro i j hi hj t u
  apply triv_comm_of_commutes
  let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose αβ.height γ.height j (by trivial)
  simp_rw [h_eq]
  rw [← one_mul u]
  rw [expand_αβγ_as_αβ_γ_αβ_γ h j₁ j₂ hj₁ hj₂]
  mul_assoc_l
  rw [expr_β_αβ_as_αβ_β h]
  rw [mul_assoc _ {β, i, t}]
  rw [expr_β_γ_as_γ_βγ_β h]
  mul_assoc_l
  rw [mul_assoc _ {β, i, t}]
  rw [expr_β_αβ_as_αβ_β h]
  mul_assoc_l
  rw [mul_assoc _ {β, i, t}]
  rw [expr_β_γ_as_βγ_γ_β h]
  rw [mul_assoc _ _ {αβ, j₁, -1}]
  rw [← expr_αβ_βγ_as_βγ_αβ h]
  mul_assoc_l
  rw [mul_assoc _ _ {βγ, i + j₂, t * u}]
  mul_assoc_l
  rw [mul_assoc _ {βγ, i + j₂, t * u}]
  rw [mul_neg]
  rw [inv_of_βγ h]
  group

/- αβ and αβγ commute. -/
theorem comm_of_αβ_αβγ (h : WeakGradedA3 R) : trivial_commutator_of_root_pair R αβ αβγ := by
  intro i j hi hj t u
  apply triv_comm_of_commutes
  let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose α.height βγ.height j (by trivial)
  simp_rw [h_eq]
  rw [← one_mul u]
  rw [expand_αβγ_as_α_βγ_α_βγ h j₁ j₂ hj₁ hj₂]
  mul_assoc_l
  rw [← expr_α_αβ_as_αβ_α h]
  rw [mul_assoc _ {αβ, i, t}]
  rw [expr_αβ_βγ_as_βγ_αβ h]
  mul_assoc_l
  rw [mul_assoc _ {αβ, i, t}]
  rw [← expr_α_αβ_as_αβ_α h]
  mul_assoc_l
  rw [mul_assoc _ {αβ, i, t}]
  rw [expr_αβ_βγ_as_βγ_αβ h]
  mul_assoc_l

/- βγ and αβγ commute. -/
theorem comm_of_βγ_αβγ (h : WeakGradedA3 R) : trivial_commutator_of_root_pair R βγ αβγ := by
  intro i j hi hj t u
  apply triv_comm_of_commutes
  let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose αβ.height γ.height j (by trivial)
  simp_rw [h_eq]
  rw [← one_mul u]
  rw [expand_αβγ_as_αβ_γ_αβ_γ h j₁ j₂ hj₁ hj₂]
  mul_assoc_l
  rw [← expr_αβ_βγ_as_βγ_αβ h]
  rw [mul_assoc _ {βγ, i, t}]
  rw [← expr_γ_βγ_as_βγ_γ h]
  mul_assoc_l
  rw [mul_assoc _ {βγ, i, t}]
  rw [← expr_αβ_βγ_as_βγ_αβ h]
  mul_assoc_l
  rw [mul_assoc _ {βγ, i, t}]
  rw [← expr_γ_βγ_as_βγ_γ h]
  mul_assoc_l

/- Rewrite α⬝αβγ as αβγ⬝α. -/
theorem expr_α_αβγ_as_αβγ_α (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ α.height) (hj : j ≤ αβγ.height) (t u : R), commutes({α, i, t}, {αβγ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [comm_of_α_αβγ h]

/- Rewrite βγ⬝αβγ as αβγ⬝βγ. -/
theorem expr_βγ_αβγ_as_αβγ_βγ (h : WeakGradedA3 R) :
    ∀ (i j : ℕ) (hi : i ≤ βγ.height) (hj : j ≤ αβγ.height) (t u : R), commutes({βγ, i, t}, {αβγ, j, u}) := by
  intro i j hi hj t u
  apply commutes_of_triv_comm
  rw [comm_of_βγ_αβγ h]

/- αβγ commutes with itself. -/
theorem mixed_commutes_of_αβγ (h : WeakGradedA3 R) : trivial_commutator_of_root_pair R αβγ αβγ := by
  intro i j hi hj t u
  apply triv_comm_of_commutes
  let ⟨ j₁, j₂, ⟨ h_eq, hj₁, hj₂ ⟩ ⟩ := decompose α.height βγ.height j (by trivial)
  simp_rw [h_eq]
  rw [← one_mul u]
  rw [expand_αβγ_as_α_βγ_α_βγ h j₁ j₂ hj₁ hj₂]
  mul_assoc_l
  rw [← expr_α_αβγ_as_αβγ_α h]
  rw [mul_assoc _ {αβγ, i, t}]
  rw [← expr_βγ_αβγ_as_αβγ_βγ h]
  mul_assoc_l
  rw [mul_assoc _ {αβγ, i, t}]
  rw [← expr_α_αβγ_as_αβγ_α h]
  mul_assoc_l
  rw [mul_assoc _ {αβγ, i, t}]
  rw [← expr_βγ_αβγ_as_αβγ_βγ h]
  mul_assoc_l

/- Linearity for αβγ. -/
theorem lin_of_αβγ (h : WeakGradedA3 R) : lin_of_root R αβγ := by
  intro i hi t u
  let ⟨ i₁, i₂, ⟨ h_eq, hi₁, hi₂ ⟩ ⟩ := decompose α.height βγ.height i (by trivial)
  simp_rw [h_eq]
  nth_rewrite 1 [← mul_one t]
  rw [expand_αβγ_as_α_βγ_α_βγ h i₁ i₂ hi₁ hi₂]
  rw [mul_assoc _ _ {αβγ, i₁ + i₂, u}]
  rw [expr_βγ_αβγ_as_αβγ_βγ h i₂ i hi₂ hi]
  mul_assoc_l
  rw [mul_assoc _ _ {αβγ, i₁ + i₂, u}]
  rw [expr_α_αβγ_as_αβγ_α h]
  mul_assoc_l
  rw [mul_assoc _ _ {αβγ, i₁ + i₂, u}]
  rw [expr_βγ_αβγ_as_αβγ_βγ h]
  mul_assoc_l
  nth_rewrite 1 [← mul_one u]
  rw [expand_αβγ_as_α_βγ_α_βγ h]
  mul_assoc_l
  rw [lin_of_α h]
  nth_rewrite 1 [inv_of_βγ h]
  group
  rw [mul_assoc _ {α, i₁, -u}]
  rw [lin_of_α h]
  have rid : -u + -t = -(t+u) := by simp
  rw [rid]
  rw [← expand_αβγ_as_α_βγ_α_βγ h]
  simp [height] at *

theorem StrongGradedA3_of_WeakGradedA3 (h : WeakGradedA3 R) : StrongGradedA3 R := by
  constructor
  · exact h
  · exact comm_of_αβ_βγ h
  · exact comm_of_αβ_γ h
  · exact comm_of_α_βγ h
  · exact comm_of_α_αβγ h
  · exact comm_of_β_αβγ h
  · exact comm_of_γ_αβγ h
  · exact comm_of_αβ_αβγ h
  · exact comm_of_βγ_αβγ h
  · exact mixed_commutes_of_αβγ h
  · exact lin_of_αβγ h

end A3GradedGen

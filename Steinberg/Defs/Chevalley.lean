import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FreeGroup.Basic

import Steinberg.Defs.Root

namespace Steinberg

open PosRootSys

variable {G : Type TG} [Group G]
         {Φ : Type TΦ} [PosRootSys Φ]
         {R : Type TR} [Ring R]

theorem helper (G : Type TG) [Group G] (x y z : G) : x * y * z⁻¹ = 1 → x * y = z := by
  intro h
  apply @mul_right_cancel _ _ _ _ z⁻¹
  rw [mul_inv_cancel]
  exact h

abbrev SingleSpanRootPair (R : Type TR) [Ring R] (Φ : Type TΦ) [PosRootSys Φ]
  := (ζ : Φ) × (η : Φ) × (θ : Φ) × R ×' (PosRootSys.height θ = PosRootSys.height ζ + PosRootSys.height η)

/- Generators of the Chevalley subgroup corresponding to a positive root system over a ring with monomial entries. -/
structure GradedGen (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] where
  mk ::
  ζ : Φ
  i : ℕ
  hi :  i ≤ height ζ
  t : R

namespace GradedGen

/-- The free group generatored by `GradedGen` elements. -/
abbrev FreeGroupOnGradedGens (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] := FreeGroup (GradedGen Φ R)

/-- Inject a `GradedGen` into `FreeGroupOnGradedGens`. -/
def free_mk : GradedGen Φ R → FreeGroupOnGradedGens Φ R :=
  FreeGroup.of

/-- Helper function to construct and inject a `GradedGen`. -/
def free_mk_mk (ζ : Φ) (i : ℕ) (hi : i ≤ height ζ) (t : R) : FreeGroupOnGradedGens Φ R :=
  FreeGroup.of <| (mk ζ i hi t)

/-- "Degree-reflection" map of `GradedGen`s corresponding to swapping degree `i` with `height ζ - i`. (An involution.) -/
def refl_deg_of_gen (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] (g : GradedGen Φ R) : GradedGen Φ R :=
  mk g.ζ (height g.ζ - g.i) (by omega) g.t

end GradedGen

open GradedGen

/-! ### Statements about generators which we assume and/or prove -/

/-! #### Commutator for generators from two roots which span no additional roots -/
/- Theorem stating that commutator of generators for two roots vanishes. -/
def trivial_commutator_of_root_pair (R : Type TR) [Ring R] (f : FreeGroupOnGradedGens Φ R →* G) (ζ η : Φ) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f (free_mk_mk ζ i hi t), f (free_mk_mk η j hj u) ⁆ = 1

/-
The set of elements which must vanish according to the theorem that the commutator of generators
for two roots vanishes. (Used to construct a `PresentedGroup`.)
-/
def rels_of_trivial_commutator_of_root_pair (R : Type TR) [Ring R]
  (ζη : Φ × Φ) : Set (FreeGroupOnGradedGens Φ R) :=
  let (ζ, η) := ζη;
  { ⁅ free_mk_mk ζ i hi t, free_mk_mk η j hj u ⁆
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
theorem refl_deg_of_rels_of_trivial_commutator_of_root_pair (ζ η : Φ) :
  ∀ r ∈ rels_of_trivial_commutator_of_root_pair R (ζ, η), FreeGroup.map (refl_deg_of_gen Φ R) r ∈ rels_of_trivial_commutator_of_root_pair R (ζ, η) := by
  intro r h
  simp only [rels_of_trivial_commutator_of_root_pair, Set.mem_setOf_eq] at h
  let ⟨ i, j, hi, hj, t, u, h' ⟩ := h
  simp only [← h', map_commutatorElement, refl_deg_of_gen, rels_of_trivial_commutator_of_root_pair]
  exists (PosRootSys.height ζ - i), (PosRootSys.height η - j), (by omega), (by omega), t, u

/-! #### Commutator for two generators from two roots which span one additional root -/

/- Commutator for generators corresponding to two roots which span a single additional root. C is a constant (always 1 in A3). -/
def rels_of_single_commutator_of_root_pair (R : Type TR) [Ring R]
  (p : SingleSpanRootPair R Φ) : Set (FreeGroupOnGradedGens Φ R) :=
  let ⟨ ζ, η, θ, C, h_height ⟩ := p;
  { ⁅ free_mk_mk ζ i hi t, free_mk_mk η j hj u ⁆ * (free_mk_mk θ (i + j) (by omega) (C * (t * u)))⁻¹
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

def single_commutator_of_root_pair (f : FreeGroupOnGradedGens Φ R →* G) (ζ η θ : Φ)
  (C : R) (h_height : height θ = height ζ + height η) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f (free_mk_mk ζ i hi t), f (free_mk_mk η j hj u) ⁆ = f (free_mk_mk θ (i + j) (by omega) (C * (t * u)))

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
theorem refl_deg_of_rels_of_single_commutator_of_root_pair (ζ η : Φ) (C : R) (h_height : height θ = height ζ + height η) :
  ∀ r ∈ rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩, FreeGroup.map (refl_deg_of_gen Φ R) r ∈ rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩ := by
  intro r h
  simp only [rels_of_single_commutator_of_root_pair, Set.mem_setOf_eq] at h
  let ⟨ i, j, hi, hj, t, u, h' ⟩ := h
  simp only [← h', map_mul, map_commutatorElement, map_inv, refl_deg_of_gen, rels_of_single_commutator_of_root_pair]
  exists (PosRootSys.height ζ - i), (PosRootSys.height η - j), (by omega), (by omega), t, u
  congr
  simp only
  omega

/-! #### Commutator relation for two generators from the same root -/

/-
Commutator for generators corresponding to the same root, of two degrees `i` and `j`. This is implied in the case `i=j`
by `lin_of_root` and the commutativity of addition.
-/
def rels_of_mixed_commutes_of_root (R : Type TR) [Ring R]
  (ζ : Φ) : Set (FreeGroupOnGradedGens Φ R) :=
  rels_of_trivial_commutator_of_root_pair R (ζ, ζ)

def mixed_commutes_of_root (R : Type TR) [Ring R] (f : FreeGroupOnGradedGens Φ R →* G) (ζ : Φ) : Prop :=
  @trivial_commutator_of_root_pair _ _ _ _ _ _ f ζ ζ

/-- Degree-reflection preserves the set of mixed-degree commutator relations for any root. -/
theorem refl_deg_of_rels_of_mixed_commutes_of_root (ζ : Φ) :
  ∀ r ∈ rels_of_mixed_commutes_of_root R ζ, FreeGroup.map (refl_deg_of_gen Φ R) r ∈ rels_of_mixed_commutes_of_root R ζ := by
  intro r h
  simp only [rels_of_mixed_commutes_of_root, Set.mem_setOf_eq] at h
  let ⟨ i, j, hi, hj, t, u, h' ⟩ := h
  simp only [← h', map_commutatorElement, refl_deg_of_gen, rels_of_mixed_commutes_of_root]
  exists (PosRootSys.height ζ - i), (PosRootSys.height ζ - j), (by omega), (by omega), t, u

/-! #### Linearity relation for products of generators from a single root -/

/- Linearity of coefficients for products of generators of a single root (with the same degree). -/
def rels_of_lin_of_root (R : Type TR) [Ring R]
  (ζ : Φ) : Set (FreeGroupOnGradedGens Φ R) :=
  { (free_mk_mk ζ i hi t) * (free_mk_mk ζ i hi u) * (free_mk_mk ζ i hi (t + u))⁻¹
    | (i : ℕ) (hi : i ≤ height ζ) (t : R) (u : R) }

def lin_of_root (R : Type TR) [Ring R] (f : FreeGroupOnGradedGens Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t u : R), (f (free_mk_mk ζ i hi t)) * (f (free_mk_mk ζ i hi u)) = f (free_mk_mk ζ i hi (t + u))

/-
Helper theorem to prove `lin_of_root` in a `PresentedGroup` where the relations
include `rels_of_lin_of_root`.
-/


/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
theorem refl_deg_of_rels_of_lin_of_root (ζ : Φ) :
  ∀ r ∈ rels_of_lin_of_root R ζ, FreeGroup.map (refl_deg_of_gen Φ R) r ∈ rels_of_lin_of_root R ζ := by
  intro r h
  simp only [rels_of_lin_of_root, Set.mem_setOf_eq] at h
  let ⟨ i, hi, t, u, h' ⟩ := h
  simp only [← h', refl_deg_of_gen, rels_of_lin_of_root]
  exists (PosRootSys.height ζ - i), (by omega), t, u

/-! ### Additional properties implied by linearity and implications therein -/

/- Coefficient 0 gives an identity element. -/
def id_of_root (R : Type TR) [Ring R] (f : FreeGroupOnGradedGens Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ), f (free_mk_mk ζ i hi (0 : R)) = 1

-- /- Negating the coefficient inverts the generator. -/
def inv_of_root (R : Type TR) [Ring R] (f : FreeGroupOnGradedGens Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t : R), f (free_mk_mk ζ i hi (-t)) = (f (free_mk_mk ζ i hi t))⁻¹

/- Linearity implies identity (essentially a standard fact about group homomorphisms). -/
theorem id_of_lin_of_root (R : Type TR) [Ring R] {f : FreeGroupOnGradedGens Φ R →* G} {ζ : Φ} :
  lin_of_root R f ζ → id_of_root R f ζ := by
  intro h_lin
  simp only [lin_of_root] at h_lin
  simp only [id_of_root]
  intro i hi
  apply @mul_left_cancel _ _ _ (f (free_mk_mk ζ i hi 0))
  rw [mul_one, h_lin, add_zero]

/- Linearity implies inverse-ness (essentially a standard fact about group homomorphisms). -/
theorem inv_of_lin_of_root (R : Type TR) [Ring R] {f : FreeGroupOnGradedGens Φ R →* G} {ζ : Φ} :
  lin_of_root R f ζ → inv_of_root R f ζ := by
  intro h_lin
  simp only [lin_of_root] at h_lin
  simp only [inv_of_root]
  intro i hi t
  apply @mul_left_cancel _ _ _ (f (free_mk_mk ζ i hi t))
  rw [mul_inv_cancel, h_lin, add_neg_cancel, id_of_lin_of_root R h_lin]

end Steinberg

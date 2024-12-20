import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.PresentedGroup

import Steinberg.Defs.Root
import Steinberg.Upstream.PresentedGroup

namespace Steinberg

open PosRootSys

variable {G : Type TG} [Group G]

/- Generators of the (weak) group correspond to matrices with a single *monomial* entry above the diagonal. -/
structure WeakGradedGen (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] where
  mk ::
  ζ : Φ
  hζ : isPresent ζ
  i : ℕ
  hi :  i ≤ height ζ
  t : R

namespace WeakGradedGen

variable {Φ : Type TΦ} [PosRootSys Φ]
         {R : Type TR} [Ring R]


abbrev WeakFreeGroup (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] := FreeGroup (WeakGradedGen Φ R)

def free_mk_of (ζ : Φ) (i : ℕ) (hi : i ≤ height ζ) (t : R) : WeakFreeGroup Φ R :=
  if hζ : isPresent ζ then
    FreeGroup.of <| WeakGradedGen.mk ζ hζ i hi t
  else
    match h_mk : maker ζ i with
    | (ζ₁, i₁, ζ₂, i₂) =>
      have ⟨_, _, _, _, _, _⟩ := @h_maker Φ _ ζ hζ i hi
      ⁅ FreeGroup.of <| WeakGradedGen.mk ζ₁ (by simp [h_mk] at *; assumption) i₁ (by simp [h_mk] at *; assumption) t,
        FreeGroup.of <| WeakGradedGen.mk ζ₂ (by simp [h_mk] at *; assumption) i₂ (by simp [h_mk] at *; assumption) (1 : R) ⁆

-- def reflect_degree_of_gen (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] (g : WeakGradedGen Φ R) : WeakGradedGen Φ R :=
--   mk g.ζ g.hζ (height g.ζ - g.i) (by omega) g.t
-- def refl_deg (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] :=
--   FreeGroup.map (reflect_degree_of_gen Φ R)

-- def reflect_degree_of_free_group_eq (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] :=

/-! ### Statements about generators which we assume and/or prove -/

/-! #### Commutator for generators corresponding to two roots which span no additional roots -/
/- Theorem stating that commutator of generators for two roots vanishes. -/
def trivial_commutator_of_root_pair (R : Type TR) [Ring R] (f : WeakFreeGroup Φ R →* G) (ζ η : Φ) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f (free_mk_of ζ i hi t), f (free_mk_of η j hj u) ⁆ = 1

/-
The set of elements which must vanish according to the theorem that the commutator of generators
for two roots vanishes. (Used to construct a `PresentedGroup`.)
-/
def rels_of_trivial_commutator_of_root_pair (R : Type TR) [Ring R]
  (ζ η : Φ) : Set (WeakFreeGroup Φ R) :=
  { ⁅ free_mk_of ζ i hi t, free_mk_of η j hj u ⁆
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

/-
Helper theorem to prove `trivial_commutator_of_root_pair` in a `PresentedGroup` where the relations
include `rels_of_trivial_commutator_of_root_pair`.
-/
theorem pres_helper_of_trivial_commutator_of_root_pair (R : Type TR) [Ring R]
  (ζ η : Φ) (S : Set (Set (WeakFreeGroup Φ R)))
  (h_S : (rels_of_trivial_commutator_of_root_pair R ζ η) ∈ S) :
  trivial_commutator_of_root_pair R (PresentedGroup.mk (⋃₀ S)) ζ η := by
  intro i j hi hj t u
  apply eq_one_of_mem_rels
  simp only
  apply Set.mem_sUnion.mpr
  use (rels_of_trivial_commutator_of_root_pair R ζ η)
  constructor
  · exact h_S
  · rw [rels_of_trivial_commutator_of_root_pair]
    exists i, j, hi, hj, t, u

private theorem helper (G : Type TG) [Group G] (x y z : G) : x * y * z⁻¹ = 1 → x * y = z := by
  intro h
  apply @mul_right_cancel _ _ _ _ z⁻¹
  rw [mul_inv_cancel]
  exact h

-- /- Commutator for generators corresponding to two roots which span a single additional root. C is a constant (always 1 in A3). -/
def rels_of_single_commutator_of_root_pair (R : Type TR) [Ring R]
  (ζ η θ : Φ) (C : R) (h_height : height θ = height ζ + height η) : Set (WeakFreeGroup Φ R) :=
  { ⁅ free_mk_of ζ i hi t, free_mk_of η j hj u ⁆ * (free_mk_of θ (i + j) (by omega) (C * (t * u)))⁻¹
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

def single_commutator_of_root_pair (f : WeakFreeGroup Φ R →* G) (ζ η θ : Φ)
  (C : R) (h_height : height θ = height ζ + height η) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f (free_mk_of ζ i hi t), f (free_mk_of η j hj u) ⁆ = f (free_mk_of θ (i + j) (by omega) (C * (t * u)))

theorem pres_helper_of_single_commutator_of_root_pair (R : Type TR) [Ring R]
  (ζ η θ : Φ) (C : R) (h_height : height θ = height ζ + height η)
  (S : Set (Set (WeakFreeGroup Φ R)))
  (h_S : (rels_of_single_commutator_of_root_pair R ζ η θ C h_height) ∈ S) :
  single_commutator_of_root_pair (PresentedGroup.mk (⋃₀ S)) ζ η θ C h_height := by
  intro i j hi hj t u
  apply helper
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use (rels_of_single_commutator_of_root_pair R ζ η θ C h_height)
  constructor
  · exact h_S
  · rw [rels_of_single_commutator_of_root_pair]
    exists i, j, hi, hj, t, u

/-
Commutator for generators corresponding to the same root, of two degrees `i` and `j`. This is implied in the case `i=j`
by `lin_of_root` and the commutativity of addition.
-/
def rels_of_mixed_commutes_of_root (R : Type TR) [Ring R]
  (ζ : Φ) : Set (WeakFreeGroup Φ R) :=
  rels_of_trivial_commutator_of_root_pair R ζ ζ

def mixed_commutes_of_root (R : Type TR) [Ring R] (f : WeakFreeGroup Φ R →* G) (ζ : Φ) : Prop :=
  @trivial_commutator_of_root_pair _ _ _ _ _ _ f ζ ζ

theorem pres_helper_of_mixed_commutes_of_root (R : Type TR) [Ring R]
  (ζ : Φ) (S : Set (Set (WeakFreeGroup Φ R)))
  (h_S : (rels_of_mixed_commutes_of_root R ζ) ∈ S) :
  mixed_commutes_of_root R (PresentedGroup.mk (⋃₀ S)) ζ :=
  pres_helper_of_trivial_commutator_of_root_pair R ζ ζ S h_S

/- Linearity of coefficients for products of generators of a single root (with the same degree). -/
def rels_of_lin_of_root (R : Type TR) [Ring R]
  (ζ : Φ) : Set (WeakFreeGroup Φ R) :=
  { (free_mk_of ζ i hi t) * (free_mk_of ζ i hi u) * (free_mk_of ζ i hi (t + u))⁻¹
    | (i : ℕ) (hi : i ≤ height ζ) (t : R) (u : R) }

def lin_of_root (R : Type TR) [Ring R] (f : WeakFreeGroup Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t u : R), (f (free_mk_of ζ i hi t)) * (f (free_mk_of ζ i hi u)) = f (free_mk_of ζ i hi (t + u))

/-
Helper theorem to prove `lin_of_root` in a `PresentedGroup` where the relations
include `rels_of_lin_of_root`.
-/
theorem pres_helper_of_lin_of_root (R : Type TR) [Ring R]
  (ζ : Φ) (S : Set (Set (WeakFreeGroup Φ R)))
  (h_S : (rels_of_lin_of_root R ζ) ∈ S) :
  lin_of_root R (PresentedGroup.mk (⋃₀ S)) ζ := by
  intro i hi t u
  apply helper
  apply eq_one_of_mem_rels
  simp only
  apply Set.mem_sUnion.mpr
  use (rels_of_lin_of_root R ζ)
  constructor
  · exact h_S
  · rw [rels_of_lin_of_root]
    exists i, hi, t, u

/-! ### Additional properties implied by linearity and implications therein -/

/- Coefficient 0 gives an identity element. -/
def id_of_root (R : Type TR) [Ring R] (f : WeakFreeGroup Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ), f (free_mk_of ζ i hi (0 : R)) = 1

-- /- Negating the coefficient inverts the generator. -/
def inv_of_root (R : Type TR) [Ring R] (f : WeakFreeGroup Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t : R), f (free_mk_of ζ i hi (-t)) = (f (free_mk_of ζ i hi t))⁻¹

/- Linearity implies identity (essentially a standard fact about group homomorphisms). -/
theorem id_of_lin_of_root (R : Type TR) [Ring R] {f : WeakFreeGroup Φ R →* G} {ζ : Φ} :
  lin_of_root R f ζ → id_of_root R f ζ := by
  intro h_lin
  simp only [lin_of_root] at h_lin
  simp only [id_of_root]
  intro i hi
  apply @mul_left_cancel _ _ _ (f (free_mk_of ζ i hi 0))
  rw [mul_one, h_lin, add_zero]

/- Linearity implies inverse-ness (essentially a standard fact about group homomorphisms). -/
theorem inv_of_lin_of_root (R : Type TR) [Ring R] {f : WeakFreeGroup Φ R →* G} {ζ : Φ} :
  lin_of_root R f ζ → inv_of_root R f ζ := by
  intro h_lin
  simp only [lin_of_root] at h_lin
  simp only [inv_of_root]
  intro i hi t
  apply @mul_left_cancel _ _ _ (f (free_mk_of ζ i hi t))
  rw [mul_inv_cancel, h_lin, add_neg_cancel, id_of_lin_of_root R h_lin]

end WeakGradedGen

end Steinberg

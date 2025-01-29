/-

LICENSE goes here.

-/

import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.FreeGroup.Basic

import Steinberg.Defs.Root

/-!

  Chevalley stuff. TODO fill in docs.

-/

namespace Steinberg

open PosRootSys

variable {G : Type TG} [Group G]
         {Φ : Type TΦ} [PosRootSys Φ]
         {R : Type TR} [Ring R]

abbrev SingleSpanRootPair (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] :=
  (ζ : Φ) × (η : Φ) × (θ : Φ) × R ×' (height θ = height ζ + height η)

/--
  Generators of the Chevalley subgroup corresponding to a positive root system
  over a ring with monomial entries.
-/
structure GradedGen (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] where
  mk ::
  ζ : Φ
  i : ℕ
  hi :  i ≤ height ζ
  t : R

namespace GradedGen

/-- The free group generatored by `GradedGen` elements. -/
abbrev FreeGroupOnGradedGens (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] :=
  FreeGroup (GradedGen Φ R)

/-- Inject a `GradedGen` into `FreeGroupOnGradedGens`. -/
def free_mk : GradedGen Φ R → FreeGroupOnGradedGens Φ R :=
  FreeGroup.of

/-- Helper function to construct and inject a `GradedGen`. -/
def free_mk_mk (ζ : Φ) (i : ℕ) (hi : i ≤ height ζ) (t : R) : FreeGroupOnGradedGens Φ R :=
  FreeGroup.of <| (mk ζ i hi t)

end GradedGen

open GradedGen

/-! ### Statements about generators which we assume and/or prove -/

/-! #### Commutator for generators from two roots which span no additional roots -/
/- Theorem stating that commutator of generators for two roots vanishes. -/
def trivial_commutator_of_root_pair (f : FreeGroupOnGradedGens Φ R →* G) (ζ η : Φ) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f (free_mk_mk ζ i hi t), f (free_mk_mk η j hj u) ⁆ = 1

/-
The set of elements which must vanish according to the theorem that the commutator of generators
for two roots vanishes. (Used to construct a `PresentedGroup`.)
-/
def rels_of_trivial_commutator_of_root_pair (R : Type TR) [Ring R] (ζη : Φ × Φ)
    : Set (FreeGroupOnGradedGens Φ R) :=
  let (ζ, η) := ζη;
  { ⁅ free_mk_mk ζ i hi t, free_mk_mk η j hj u ⁆
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

/-! #### Commutator for two generators from two roots which span one additional root -/

/- Commutator for generators corresponding to two roots which span a single additional root. C is a constant (always 1 in A3). -/
def rels_of_single_commutator_of_root_pair (p : SingleSpanRootPair Φ R) : Set (FreeGroupOnGradedGens Φ R) :=
  let ⟨ ζ, η, θ, C, h_height ⟩ := p;
  { ⁅ free_mk_mk ζ i hi t, free_mk_mk η j hj u ⁆ * (free_mk_mk θ (i + j) (by omega) (C * (t * u)))⁻¹
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

def single_commutator_of_root_pair (f : FreeGroupOnGradedGens Φ R →* G) (ζ η θ : Φ)
    (C : R) (h_height : height θ = height ζ + height η) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f (free_mk_mk ζ i hi t), f (free_mk_mk η j hj u) ⁆ = f (free_mk_mk θ (i + j) (by omega) (C * (t * u)))

/-! #### Commutator relation for two generators from the same root -/

/-
Commutator for generators corresponding to the same root, of two degrees `i` and `j`. This is implied in the case `i=j`
by `lin_of_root` and the commutativity of addition.
-/
def rels_of_mixed_commutes_of_root (R : Type TR) [Ring R] (ζ : Φ) : Set (FreeGroupOnGradedGens Φ R) :=
  rels_of_trivial_commutator_of_root_pair R (ζ, ζ)

def mixed_commutes_of_root (f : FreeGroupOnGradedGens Φ R →* G) (ζ : Φ) : Prop :=
  @trivial_commutator_of_root_pair _ _ _ _ _ _ f ζ ζ

/-! #### Linearity relation for products of generators from a single root -/

/- Linearity of coefficients for products of generators of a single root (with the same degree). -/
def rels_of_lin_of_root (R : Type TR) [Ring R] (ζ : Φ) : Set (FreeGroupOnGradedGens Φ R) :=
  { (free_mk_mk ζ i hi t) * (free_mk_mk ζ i hi u) * (free_mk_mk ζ i hi (t + u))⁻¹
    | (i : ℕ) (hi : i ≤ height ζ) (t : R) (u : R) }

def lin_of_root (f : FreeGroupOnGradedGens Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t u : R),
    (f (free_mk_mk ζ i hi t)) * (f (free_mk_mk ζ i hi u)) = f (free_mk_mk ζ i hi (t + u))

/-
Helper theorem to prove `lin_of_root` in a `PresentedGroup` where the relations
include `rels_of_lin_of_root`.
-/

/-! ### Additional properties implied by linearity and implications therein -/

/- Coefficient 0 gives an identity element. -/
def id_of_root (f : FreeGroupOnGradedGens Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ), f (free_mk_mk ζ i hi (0 : R)) = 1

-- /- Negating the coefficient inverts the generator. -/
def inv_of_root (f : FreeGroupOnGradedGens Φ R →* G) (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t : R),
    f (free_mk_mk ζ i hi (-t)) = (f (free_mk_mk ζ i hi t))⁻¹

/- Linearity implies identity (essentially a standard fact about group homomorphisms). -/
theorem id_of_lin_of_root {f : FreeGroupOnGradedGens Φ R →* G} {ζ : Φ}
    : lin_of_root f ζ → id_of_root f ζ := by
  intro h_lin i hi
  apply @mul_left_cancel _ _ _ (f (free_mk_mk ζ i hi 0))
  rw [mul_one, h_lin, add_zero]

/- Linearity implies inverse-ness (essentially a standard fact about group homomorphisms). -/
theorem inv_of_lin_of_root {f : FreeGroupOnGradedGens Φ R →* G} {ζ : Φ}
    : lin_of_root f ζ → inv_of_root f ζ := by
  intro h_lin i hi t
  apply @mul_left_cancel _ _ _ (f (free_mk_mk ζ i hi t))
  rw [mul_inv_cancel, h_lin, add_neg_cancel, id_of_lin_of_root h_lin]

end Steinberg

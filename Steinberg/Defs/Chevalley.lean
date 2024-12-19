import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.FreeGroup.Basic

import Steinberg.Defs.Root

namespace Steinberg

open PosRootSys

/- Generators of the (weak) group correspond to matrices with a single *monomial* entry above the diagonal. -/
structure WeakGradedGen (Φ : Type u) [PosRootSys Φ] (R : Type Tv) [Ring R] where
  mk ::
  ζ : Φ
  hζ : isPresent ζ
  i : ℕ
  hi :  i ≤ height ζ
  t : R

namespace WeakGradedGen

variable {Φ : Type u} [PosRootSys Φ]
         {R : Type Tv} [Ring R]

def mkOf (ζ : Φ) (i : ℕ) (hi : i ≤ height ζ) (t : R) : FreeGroup (WeakGradedGen Φ R) :=
  if hζ : isPresent ζ then
    FreeGroup.of <| WeakGradedGen.mk ζ hζ i hi t
  else
    match h_mk : maker ζ i with
    | (ζ₁, i₁, ζ₂, i₂) =>
      have ⟨_, _, _, _, _, _⟩ := @h_maker Φ _ ζ hζ i hi
      ⁅ FreeGroup.of <| WeakGradedGen.mk ζ₁ (by simp [h_mk] at *; assumption) i₁ (by simp [h_mk] at *; assumption) t,
        FreeGroup.of <| WeakGradedGen.mk ζ₂ (by simp [h_mk] at *; assumption) i₂ (by simp [h_mk] at *; assumption) (1 : R) ⁆

/-! ### Statements about generators which we assume and/or prove -/

/- Commutator for generators corresponding to two roots which span no additional roots. -/
def trivial_commutator_of_root_pair (R : Type Tv) [Ring R] (ζ η : Φ) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ mkOf ζ i hi t, mkOf η j hj u ⁆ = 1

/- Commutator for generators corresponding to two roots which span a single additional root. C is a constant (always 1 in A3). -/
def single_commutator_of_root_pair (ζ η θ : Φ)
  (C : R) (h_height : height θ = height ζ + height η) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ mkOf ζ i hi t, mkOf η j hj u ⁆ = mkOf θ (i + j) (by omega) (C * (t * u))

/-
Commutator for generators corresponding to the same root, of two degrees `i` and `j`. This is implied in the case `i=j`
by `lin_of_root` and the commutativity of addition.
-/
def mixed_commutes_of_root (R : Type Tv) [Ring R] (ζ : Φ) : Prop :=
  @trivial_commutator_of_root_pair _ _ R _ ζ ζ

/- Linearity of coefficients for products of generators of a single root (with the same degree). -/
def lin_of_root (R : Type Tv) [Ring R] (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t u : R), (mkOf ζ i hi t) * (mkOf ζ i hi u) = mkOf ζ i hi (t + u)

/- Coefficient 0 gives an identity element. -/
def id_of_root (R : Type Tv) [Ring R] (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ), mkOf ζ i hi (0 : R) = 1

/- Negating the coefficient inverts the generator. -/
def inv_of_root (R : Type Tv) [Ring R] (ζ : Φ) : Prop :=
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t : R), mkOf ζ i hi (-t) = (mkOf ζ i hi t)⁻¹

/-! ### Implications -/

/- Linearity implies identity (essentially a standard fact about group homomorphisms). -/
theorem id_of_lin_of_root (R : Type Tv) [Ring R] {ζ : Φ} :
  lin_of_root R ζ → id_of_root R ζ := by
  intro h_lin
  simp only [lin_of_root] at h_lin
  simp only [id_of_root]
  intro i hi
  apply @mul_left_cancel _ _ _ (mkOf ζ i hi 0)
  rw [mul_one, h_lin, add_zero]

/- Linearity implies inverse-ness (essentially a standard fact about group homomorphisms). -/
theorem inv_of_lin_of_root (R : Type Tv) [Ring R] {ζ : Φ} :
  lin_of_root R ζ → inv_of_root R ζ := by
  intro h_lin
  simp only [lin_of_root] at h_lin
  simp only [inv_of_root]
  intro i hi t
  apply @mul_left_cancel _ _ _ (mkOf ζ i hi t)
  rw [mul_inv_cancel, h_lin, add_neg_cancel, id_of_lin_of_root R h_lin]

/-! ### Assumptions about present roots (typically in `Weak` structure) -/

/- Typically, we assume all present roots satisfy a linearity relation. -/
def lin_of_present (R : Type Tv) [Ring R] (Φ : Type u) [PosRootSys Φ] : Prop :=
  ∀ ⦃ζ : Φ⦄, isPresent ζ → lin_of_root R ζ

/- Typically, we assume all present roots satisfy a mixed-degree self-commutator relation. -/
def mixed_commutes_of_present (R : Type Tv) [Ring R] (Φ : Type u) [PosRootSys Φ] : Prop :=
  ∀ ⦃ζ : Φ⦄, isPresent ζ → mixed_commutes_of_root R ζ

/- Deduce identity relations from linearity relations (for present roots) -/
theorem id_of_present (R : Type Tv) [Ring R] :
    lin_of_present R Φ → ∀ ⦃ζ : Φ⦄, isPresent ζ → id_of_root R ζ := by
  intro h_pres_lin ζ h_ζ_pres
  apply id_of_lin_of_root
  exact h_pres_lin h_ζ_pres

/- Deduce inverse relations from linearity relations (for present roots) -/
theorem inv_of_present (R : Type Tv) [Ring R] :
    lin_of_present R Φ → ∀ ⦃ζ : Φ⦄, isPresent ζ → inv_of_root R ζ := by
  intro h_pres_lin ζ h_ζ_pres t
  apply inv_of_lin_of_root
  exact h_pres_lin h_ζ_pres

end WeakGradedGen

end Steinberg

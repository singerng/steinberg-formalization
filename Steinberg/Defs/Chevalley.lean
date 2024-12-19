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

/-! ### (Parameterizered) desiderata about generators -/

/- Commutator for generators corresponding to two roots which span no additional roots. -/
def trivial_commutator_of_root_pair (R : Type Tv) [Ring R] (ζ η : Φ) : Prop :=
  ∀ (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ mkOf ζ i hi t, mkOf η j hj u ⁆ = 1

/- Commutator for generators corresponding to two roots which span a single additional root. C is a constant (always 1 in A3). -/
def single_commutator_of_root_pair (ζ η θ : Φ)
  (C : R) (h_height : height θ = height ζ + height η) : Prop :=
  ∀ (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ mkOf ζ i hi t, mkOf η j hj u ⁆ = mkOf θ (i + j) (by omega) (C * (t * u))

/- Linearity of coefficients for products of generators of a single root (with the same degree). -/
def lin_of_root (R : Type Tv) [Ring R] (ζ : Φ) : Prop :=
  ∀ (i : ℕ) (hi : i ≤ height ζ) (t u : R), (mkOf ζ i hi t) * (mkOf ζ i hi u) = mkOf ζ i hi (t + u)

/-
Commutator for generators corresponding to the same root, of two degrees `i` and `j`. This is already implied in the case `i=j`
by `lin_of_root` and the commutativity of addition.
-/
def mixed_commutes_of_root (R : Type Tv) [Ring R] (ζ : Φ) : Prop :=
  @trivial_commutator_of_root_pair _ _ R _ ζ ζ

/- Coefficient 0 gives an identity element. -/
def id_of_root (R : Type Tv) [Ring R] (ζ : Φ) : Prop :=
  ∀ (i : ℕ) (hi : i ≤ height ζ), mkOf ζ i hi (0 : R) = 1

/- Negating the coefficient inverts the generator. -/
def inv_of_root (R : Type Tv) [Ring R] (ζ : Φ) : Prop :=
  ∀ (i : ℕ) (hi : i ≤ height ζ) (t : R), mkOf ζ i hi (-t) = (mkOf ζ i hi t)⁻¹

/-! ### Assumptions -/

def lin_of_present (R : Type Tv) [Ring R] (Φ : Type u) [PosRootSys Φ] : Prop := ∀ (ζ : Φ),
  isPresent ζ → lin_of_root R ζ

def mixed_commutes_of_present (R : Type Tv) [Ring R] (Φ : Type u) [PosRootSys Φ] : Prop := ∀ (ζ : Φ),
  isPresent ζ → mixed_commutes_of_root R ζ

end WeakGradedGen

end Steinberg

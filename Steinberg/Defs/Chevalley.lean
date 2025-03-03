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

abbrev DoubleSpanRootPair (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] := (
  (ζ : Φ) × (η : Φ) × (θ₁ : Φ) × (θ₂ : Φ)
  × R × R ×' (height θ₁ = height ζ + height η) ×' (height θ₂ = height ζ + 2 * height η)
)

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


set_option hygiene false in
/--
  Shorthand for building free group elements from a root, degree, and ring element.

  Note: To re-use this notation for specific `Chevalley`-like groups,
  re-define it for that group and set the priority higher.

  Then implement delaboration to use the `free_mk_mk` delab here.
-/
scoped notation (priority:=1000) "{" ζ ", " i ", " t "}" =>
  free_mk_mk ζ i (by (first | trivial | assumption | omega)) t

/-- `free_mk_mk` but with an explicit proof term provided. -/
scoped notation (priority:=1000) "{" ζ ", " i ", " t "}'" h =>
  free_mk_mk ζ i h t


open Lean PrettyPrinter Delaborator SubExpr in
/--
  Delaborates `free_mk_mk` to use the `{ }` notation defined above.

  Delaboration makes it so that the infoview uses the nice notation.
-/
@[delab app.Steinberg.GradedGen.free_mk_mk]
def delab_free_mk_mk : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``free_mk_mk 8
  let ζ ← withNaryArg 4 delab
  let i ← withNaryArg 5 delab
  let t ← withNaryArg 7 delab
  `({ $(ζ):term, $(i):term, $(t):term })

/-- Injected group elements can commute on their root heights `i` and `j`.  -/
theorem h_add_comm (ζ : Φ) (i j : ℕ) (h : i + j ≤ height ζ) (t : R)
    : {ζ, i + j, t} = {ζ, j + i, t} := by
  congr 1
  exact add_comm i j

end GradedGen

open GradedGen

/-! ### Statements about generators which we assume and/or prove -/

/-! #### Commutator for generators from two roots which span no additional roots -/

/- Theorem stating that commutator of generators for two roots vanishes. -/
def trivial_commutator_of_root_pair (f : FreeGroupOnGradedGens Φ R →* G) (ζ η : Φ) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f {ζ, i, t}, f {η, j, u} ⁆ = 1

/-
The set of elements which must vanish according to the theorem that the commutator of generators
for two roots vanishes. (Used to construct a `PresentedGroup`.)
-/
def rels_of_trivial_commutator_of_root_pair (R : Type TR) [Ring R] (ζη : Φ × Φ)
    : Set (FreeGroupOnGradedGens Φ R) :=
  let (ζ, η) := ζη;
  { ⁅ {ζ, i, t}, {η, j, u} ⁆
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

/-! #### Commutator for two generators from two roots which span one additional root -/

def rels_of_single_commutator_of_root_pair (p : SingleSpanRootPair Φ R) : Set (FreeGroupOnGradedGens Φ R) :=
  let ⟨ ζ, η, θ, C, h_height ⟩ := p;
  { ⁅ {ζ, i, t}, {η, j, u} ⁆ * {θ, i + j, C * (t * u)}⁻¹
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

def single_commutator_of_root_pair (f : FreeGroupOnGradedGens Φ R →* G) (ζ η θ : Φ)
    (C : R) (h_height : height θ = height ζ + height η) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f {ζ, i, t}, f {η, j, u} ⁆ = f {θ, i + j, C * (t * u)}

/-! #### Commutator for two generators from two roots which span one additional root -/

def rels_of_double_commutator_of_root_pair (p : DoubleSpanRootPair Φ R) : Set (FreeGroupOnGradedGens Φ R) :=
  let ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ := p;
  { ⁅ {ζ, i, t}, {η, j, u} ⁆ *
    ({θ₁, i + j, C₁ * (t * u)} * {θ₂, i + 2 * j, C₂ * (t * (u * u))})⁻¹
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

def double_commutator_of_root_pair (f : FreeGroupOnGradedGens Φ R →* G) (ζ η θ₁ θ₂ : Φ)
    (C₁ C₂ : R) (h_height₁ : height θ₁ = height ζ + height η) (h_height₂ : height θ₂ = height ζ + 2 * height η) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f {ζ, i, t}, f {η, j, u} ⁆ = f {θ₁, i + j, C₁ * (t * u)} * f {θ₂, i + 2 * j, C₂ * (t * (u * u))}

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
  { {ζ, i, t} * {ζ, i, u} * {ζ, i, t + u}⁻¹
    | (i : ℕ) (hi : i ≤ height ζ) (t : R) (u : R) }


/-! ### Additional properties implied by linearity and implications therein -/

section ofRoot

set_option quotPrecheck false

/--
  Linearity of group elements on a particular root.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ) (t u), f {ζ, i, t} * f {ζ, i, u} = f {ζ, i, t + u}`.

  `(f : FreeGroupOnGradedGens Φ R →* G)`
  `(ζ : Φ)`
-/
scoped notation "lin_of_root" "(" f ", " ζ ")" =>
  ∀ (i : ℕ) (hi : i ≤ height ζ) (t u),
    f {ζ, i, t} * f {ζ, i, u} = f {ζ, i, t + u}

/--
  Ring coefficient 0 gives an identity element.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ), f {ζ, i, 0} = 1`.

  `(f : FreeGroupOnGradedGens Φ R →* G)`
  `(ζ : Φ)`
-/
scoped notation "id_of_root" "(" f ", " ζ ")" =>
  ∀ (i : ℕ) (hi : i ≤ height ζ),
    f {ζ, i, 0} = 1
/--
  Negating the coefficient inverts the generator.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ) (t : R), (f {ζ, i, t})⁻¹ = 1`.

  `(f : FreeGroupOnGradedGens Φ R →* G)`
  `(ζ : Φ)`
-/
scoped notation "inv_of_root" "(" f ", " ζ ")" =>
  ∀ (i : ℕ) (hi : i ≤ height ζ) (t),
    (f {ζ, i, t})⁻¹ = f {ζ, i, -t}

/- Linearity implies identity (essentially a standard fact about group homomorphisms). -/
theorem id_of_lin_of_root {f : FreeGroupOnGradedGens Φ R →* G} {ζ : Φ}
    : lin_of_root(f, ζ) → id_of_root(f, ζ) := by
  intro h_lin i hi
  apply @mul_left_cancel _ _ _ (f {ζ, i, 0})
  rw [mul_one, h_lin, add_zero]

/- Linearity implies inverse-ness (essentially a standard fact about group homomorphisms). -/
theorem inv_of_lin_of_root {f : FreeGroupOnGradedGens Φ R →* G} {ζ : Φ}
    : lin_of_root(f, ζ) → inv_of_root(f, ζ) := by
  intro h_lin i hi t
  apply @mul_left_cancel _ _ _ (f {ζ, i, t})
  rw [mul_inv_cancel, h_lin, add_neg_cancel, id_of_lin_of_root h_lin]

end ofRoot /- section -/

end Steinberg

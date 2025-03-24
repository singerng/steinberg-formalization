/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.Defs.PositiveRootSystem
import Steinberg.Defs.Commutator

import Steinberg.Upstream.PresentedGroup
import Steinberg.Upstream.Commutator

import Steinberg.Macro.Group
import Steinberg.Macro.Syntax

/-!

  File dox go here.

-/

namespace Steinberg

variable {G : Type TG} [Group G]
         {Φ : Type TΦ} [PositiveRootSystem Φ]
         {R : Type TR} [Ring R]

open PositiveRootSystem PartialChevalleySystem

namespace GradedPartialChevalley

/-! ## Generators of graded Chevalley group -/

/--
  Generators of the Chevalley subgroup corresponding to a positive root system
  over a ring with monomial entries.
-/
structure GradedChevalleyGenerator (Φ : Type TΦ) [PositiveRootSystem Φ] (R : Type TR) [Ring R] where
  mk ::
  ζ : Φ
  i : ℕ
  hi : i ≤ height ζ
  t : R

namespace GradedChevalleyGenerator

instance instCoeProd : Coe ((ζ : Φ) × (i : ℕ) × (i ≤ height ζ) ×' R) (GradedChevalleyGenerator Φ R) :=
  ⟨fun ⟨ζ, i, hi, t⟩ => mk ζ i hi t⟩

/--
  Shorthand for building free group elements from a root, degree, and ring element.

  Note: To re-use this notation for specific `Chevalley`-like groups,
  re-define it for that group and set the priority higher.
  Then implement delaboration to use the delab defined below.
-/
scoped notation (priority:=1000) "{" ζ ", " i ", " t "}" =>
  FreeGroup.of (GradedChevalleyGenerator.mk ζ i (by ht) t)

/-- Inject a generator but with an explicit proof term provided. -/
scoped notation (priority:=1000) "{" ζ ", " i ", " t "}'" h:max =>
  FreeGroup.of (GradedChevalleyGenerator.mk ζ i h t)

/-- Inject an already-created generator, rather than data. -/
scoped notation (priority:=999) "{{" g "}}" =>
  FreeGroup.of g

section DelabBraces

open Lean PrettyPrinter Delaborator SubExpr

/--
  Delaborates `GradedChevalleyGenerator.mk` to use the `{ }` notation.

  Delaboration makes it so that the infoview uses the nice notation.
-/
@[delab app.Steinberg.GradedPartialChevalley.GradedChevalleyGenerator.mk]
def delab_generator_mk : Delab := do
  let e ← getExpr

  -- Only delab a full application of `.mk`
  guard $ e.isAppOfArity' ``GradedChevalleyGenerator.mk 8

  let ζ ← withNaryArg 4 delab
  let i ← withNaryArg 5 delab
  let t ← withNaryArg 7 delab
  `({ $ζ:term, $i:term, $t:term })


/--
  Delaborates `FreeGroup.of` to use the `{ }` notation.

  Delaboration makes it so that the infoview uses the nice notation.
-/
@[delab app.FreeGroup.of]
def delab_of : Delab := do
  let e ← getExpr

  -- Only delab `FreeGroup.of` if its type and value are given to the app
  guard $ e.isAppOfArity' ``FreeGroup.of 2

  -- Only delab `FreeGroup.of` if the type is a Chevalley generator
  let ty := e.getAppArgs.get! 0
  guard $ ty.isAppOfArity' ``GradedChevalleyGenerator 4

  -- Use the delaboration of the generator
  -- Since this might be a more complicated term or calculation,
  -- we don't call `delab_generator_mk` directly
  let g ← withNaryArg 1 delab
  `($g)

end DelabBraces /- section -/

/-- Injected group elements can commute on their root heights `i` and `j`.  -/
theorem h_add_comm (ζ : Φ) (i j : ℕ) (h : i + j ≤ height ζ) (t : R)
    : {ζ, i + j, t} = {ζ, j + i, t} := by
  congr 2
  exact add_comm i j

theorem h_add_assoc (ζ : Φ) (i j k : ℕ) (h : i + j + k ≤ height ζ) (t : R)
    : {ζ, i + j + k, t} = {ζ, i + (j + k), t} := by
  congr 2
  exact add_assoc i j k

theorem eq_of_h_eq (ζ : Φ) {i : ℕ} (j : ℕ) (hij : i = j)
    : ∀ {_ : i ≤ height ζ} {t : R}, {ζ, i, t} = {ζ, j, t} := by
  intros; congr 2

theorem eq_of_R_eq (ζ : Φ) {t : R} (u : R) (h : t = u)
    : ∀ {i : ℕ} {_ : i ≤ height ζ}, {ζ, i, t} = {ζ, i, u} := by
  intros; congr 2

theorem eq_of_hR_eq (ζ : Φ) {i : ℕ} (j : ℕ) (hij : i = j) {t : R} (u : R) (htu : t = u)
    : ∀ {_ : i ≤ height ζ}, {ζ, i, t} = {ζ, j, u} := by
  intros; congr 2

end GradedChevalleyGenerator

/-! ### Statements about generators which we assume and/or prove -/

open GradedChevalleyGenerator

section Relations

/-! #### Commutator for generators from two roots which span no additional roots -/

/- Theorem stating that commutator of generators for two roots vanishes. -/
def trivialSpanPropOfRootPair (f : FreeGroup (GradedChevalleyGenerator Φ R) →* G) (p : Φ × Φ) : Prop :=
  let (ζ, η) := p;
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f {ζ, i, t}, f {η, j, u} ⁆ = 1

/-
The set of elements which must vanish according to the theorem that the commutator of generators
for two roots vanishes. (Used to construct a `PresentedGroup`.)
-/
def trivialSpanRelationsOfRootPair (R : Type TR) [Ring R] (p : Φ × Φ)
    : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  let (ζ, η) := p;
  { ⁅ {ζ, i, t}, {η, j, u} ⁆
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

/-! #### Commutator for two generators from two roots which span one additional root -/

def singleCommutatorPropOfRootPair (f : FreeGroup (GradedChevalleyGenerator Φ R) →* G) (p : SingleSpanRootPair Φ) : Prop :=
  let ⟨ ζ, η, θ, C, h_height ⟩ := p;
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f {ζ, i, t}, f {η, j, u} ⁆ = f {θ, i + j, ↑C * t * u}

def singleSpanRelationsOfRootPair (R : Type TR) [Ring R] (p : SingleSpanRootPair Φ) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  let ⟨ ζ, η, θ, C, h_height ⟩ := p;
  { ⁅ {ζ, i, t}, {η, j, u} ⁆ * {θ, i + j, C * t * u}⁻¹
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

/-! #### Commutator for two generators from two roots which span one additional root -/

def doubleSpanPropOfRootPair (f : FreeGroup (GradedChevalleyGenerator Φ R) →* G) (p : DoubleSpanRootPair Φ) : Prop :=
  let ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ := p;
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ height ζ) (hj : j ≤ height η) (t u : R),
    ⁅ f {ζ, i, t}, f {η, j, u} ⁆ = f {θ₁, i + j, ↑C₁ * t * u} * f {θ₂, i + 2 * j, ↑C₂ * t * u * u}

def doubleSpanRelationsOfRootPair (R : Type TR) [Ring R] (p : DoubleSpanRootPair Φ) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  let ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ := p;
  { ⁅ {ζ, i, t}, {η, j, u} ⁆ *
    ({θ₁, i + j, C₁ * t * u} * {θ₂, i + 2 * j, C₂ * t * u * u})⁻¹
    | (i : ℕ) (j : ℕ) (hi : i ≤ height ζ) (hj : j ≤ height η) (t : R) (u : R) }

/-! #### Commutator relation for two generators from the same root -/

/-
Commutator for generators corresponding to the same root, of two degrees `i` and `j`. This is implied in the case `i=j`
by `lin_of_root` and the commutativity of addition.
-/
def mixedDegreePropOfRoot (f : FreeGroup (GradedChevalleyGenerator Φ R) →* G) (ζ : Φ) : Prop :=
  @trivialSpanPropOfRootPair _ _ _ _ _ _ f (ζ, ζ)

def mixedDegreeRelationsOfRoot (R : Type TR) [Ring R] (ζ : Φ) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  trivialSpanRelationsOfRootPair R (ζ, ζ)

/-! #### Linearity relation for products of generators from a single root -/

/- Linearity of coefficients for products of generators of a single root (with the same degree). -/
def linearityRelationsOfRoot (R : Type TR) [Ring R] (ζ : Φ) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  { {ζ, i, t} * {ζ, i, u} * {ζ, i, t + u}⁻¹
    | (i : ℕ) (hi : i ≤ height ζ) (t : R) (u : R) }

end Relations

/-! ### Additional properties implied by linearity and implications therein -/

section ofRoot

set_option quotPrecheck false

/--
  Linearity of group elements on a particular root.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ) (t u), f {ζ, i, t} * f {ζ, i, u} = f {ζ, i, t + u}`.

  `(f : FreeGroup (GradedChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "lin_of_root" "(" f ", " ζ ")" =>
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t u),
    f {ζ, i, t} * f {ζ, i, u} = f {ζ, i, t + u}

/--
  Ring coefficient 0 gives an identity element.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ), f {ζ, i, 0} = 1`.

  `(f : FreeGroup (GradedChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "id_of_root" "(" f ", " ζ ")" =>
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ),
    f {ζ, i, 0} = 1

/--
  Negating the coefficient inverts the generator.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ) (t : R), (f {ζ, i, t})⁻¹ = 1`.

  `(f : FreeGroup (GradedChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "inv_of_root" "(" f ", " ζ ")" =>
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t),
    (f {ζ, i, t})⁻¹ = f {ζ, i, -t}

/- Linearity implies identity (essentially a standard fact about group homomorphisms). -/
-- TODO: Replace proof with map_one (use h_lin to show that t => f {ζ, i, t} is an instance of R →+ G)
theorem id_of_lin_of_root {f : FreeGroup (GradedChevalleyGenerator Φ R) →* G} {ζ : Φ}
    : lin_of_root(f, ζ) → id_of_root(f, ζ) := by
  intro h_lin i hi
  apply @mul_left_cancel _ _ _ (f {ζ, i, 0})
  rw [mul_one, h_lin, add_zero]

-- TODO: Replace proof with map_inv
/- Linearity implies inverse-ness (essentially a standard fact about group homomorphisms). -/
theorem inv_of_lin_of_root {f : FreeGroup (GradedChevalleyGenerator Φ R) →* G} {ζ : Φ}
    : lin_of_root(f, ζ) → inv_of_root(f, ζ) := by
  intro h_lin i hi t
  apply @mul_left_cancel _ _ _ (f {ζ, i, t})
  rw [mul_inv_cancel, h_lin, add_neg_cancel, id_of_lin_of_root h_lin]

end ofRoot

/-! ### Graded partial Chevalley groups -/

structure GradedPartialChevalleyGroup (Φ : Type TΦ) [PositiveRootSystem Φ] (R : Type TR) [Ring R] where
  mk ::
  sys : PartialChevalleySystem Φ
  lifted_rels_sets : Set (Set (FreeGroup (GradedChevalleyGenerator Φ R)))
  define : GradedChevalleyGenerator Φ R → FreeGroup (GradedChevalleyGenerator Φ R)
  h_define_of_present : ∀ {g : GradedChevalleyGenerator Φ R}, g.ζ ∈ sys.presentRoots → define g = FreeGroup.of g
  h_define_is_projection : ∀ {g : GradedChevalleyGenerator Φ R}, (FreeGroup.lift define) (define g) = define g

namespace GradedPartialChevalleyGroup

open GradedPartialChevalleyGroup

def fullMk (Φ : Type TΦ) [PositiveRootSystem Φ] (R : Type TR) [Ring R] (sys : PartialChevalleySystem Φ)
  : GradedPartialChevalleyGroup Φ R :=
  GradedPartialChevalleyGroup.mk sys ∅ FreeGroup.of (by tauto) (by tauto)

/-! ### Sets of relations -/
def trivialSpanRelations (w : GradedPartialChevalleyGroup Φ R) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  ⋃ (p ∈ w.sys.trivialSpanRootPairs), trivialSpanRelationsOfRootPair R p

def singleSpanRelations (w : GradedPartialChevalleyGroup Φ R) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  ⋃ (p ∈ w.sys.singleSpanRootPairs), singleSpanRelationsOfRootPair R p

def doubleSpanRelations (w : GradedPartialChevalleyGroup Φ R) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  ⋃ (p ∈ w.sys.doubleCommutatorRootPairs), doubleSpanRelationsOfRootPair R p

def mixedDegreeCommutatorRelations (w : GradedPartialChevalleyGroup Φ R) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  ⋃ (ζ ∈ w.sys.presentRoots), mixedDegreeRelationsOfRoot R ζ

def linearityRelations (w : GradedPartialChevalleyGroup Φ R) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  ⋃ (ζ ∈ w.sys.presentRoots), linearityRelationsOfRoot R ζ

def definitionRelations (w : GradedPartialChevalleyGroup Φ R) : Set (FreeGroup (GradedChevalleyGenerator Φ R)) :=
  ⋃ (ζ : Φ), {
      {ζ, i, t}⁻¹ * w.define (GradedChevalleyGenerator.mk ζ i hi t) | (i : ℕ) (hi : i ≤ height ζ) (t : R)
  }

def allRelations (w : GradedPartialChevalleyGroup Φ R) :=
  ⋃₀ {trivialSpanRelations w, singleSpanRelations w, doubleSpanRelations w, mixedDegreeCommutatorRelations w,
      linearityRelations w, ⋃₀ lifted_rels_sets w, definitionRelations w}

/-! ### The group and the embedding -/

abbrev group (w : GradedPartialChevalleyGroup Φ R) :=
  PresentedGroup (GradedPartialChevalleyGroup.allRelations w)

def project (w : GradedPartialChevalleyGroup Φ R) : FreeGroup (GradedChevalleyGenerator Φ R) →* group w :=
  PresentedGroup.mk (GradedPartialChevalleyGroup.allRelations w)

/-- Mapping between two GradedPartialChevalleyGroup graded groups -/
theorem graded_injection (w₁ w₂ : GradedPartialChevalleyGroup Φ R)
  (h_triv : ∀ p ∈ w₁.sys.trivialSpanRootPairs, p ∈ w₂.sys.trivialSpanRootPairs ∨
    (∀ r ∈ (trivialSpanRelationsOfRootPair R p), w₂.project r = 1))
  (h_single : ∀ p ∈ w₁.sys.singleSpanRootPairs, p ∈ w₂.sys.singleSpanRootPairs ∨
    (∀ r ∈ (singleSpanRelationsOfRootPair R p), w₂.project r = 1))
  (h_doub : ∀ p ∈ w₁.sys.doubleCommutatorRootPairs, p ∈ w₂.sys.doubleCommutatorRootPairs ∨
    (∀ r ∈ (doubleSpanRelationsOfRootPair R p), w₂.project r = 1))
  (h_mix : ∀ p ∈ w₁.sys.presentRoots, p ∈ w₂.sys.presentRoots ∨
    (∀ r ∈ (mixedDegreeRelationsOfRoot R p), w₂.project r = 1))
  (h_lin : ∀ p ∈ w₁.sys.presentRoots, p ∈ w₂.sys.presentRoots ∨
    (∀ r ∈ (linearityRelationsOfRoot R p), w₂.project r = 1))
  (h_lift : ∀ S ∈ w₁.lifted_rels_sets, ∀ p ∈ S, w₂.project p = 1)
  (h_def : ∀ p ∈ w₁.definitionRelations, w₂.project p = 1)
  : ∀ r ∈ w₁.allRelations, w₂.project r = 1 := by
  simp only [allRelations]
  intro r h
  simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion] at h
  rcases h with h|h|h|h|h|h|h
  · simp only [trivialSpanRelations, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_triv p
    simp_all only [forall_const]
    rcases h_triv with h|h
    · apply eq_one_of_mem_rels
      simp only [allRelations]
      have : r ∈ w₂.trivialSpanRelations := by
        simp only [trivialSpanRelations]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto
  · simp only [singleSpanRelations, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_single p
    simp_all only [forall_const]
    rcases h_single with h|h
    · apply eq_one_of_mem_rels
      simp only [allRelations]
      have : r ∈ w₂.singleSpanRelations := by
        simp only [singleSpanRelations]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto
  · simp only [doubleSpanRelations, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_doub p
    simp_all only [forall_const]
    rcases h_doub with h|h
    · apply eq_one_of_mem_rels
      simp only [allRelations]
      have : r ∈ w₂.doubleSpanRelations := by
        simp only [doubleSpanRelations]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto
  · simp only [mixedDegreeCommutatorRelations, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_mix p
    simp_all only [forall_const]
    rcases h_mix with h|h
    · apply eq_one_of_mem_rels
      simp only [allRelations]
      have : r ∈ w₂.mixedDegreeCommutatorRelations := by
        simp only [mixedDegreeCommutatorRelations]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto
  · simp only [linearityRelations, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_lin p
    simp_all only [forall_const]
    rcases h_lin with h|h
    · apply eq_one_of_mem_rels
      simp only [allRelations]
      have : r ∈ w₂.linearityRelations := by
        simp only [linearityRelations]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto
  · tauto
  · tauto

open Lean PrettyPrinter Delaborator SubExpr in
/--
  Delaborator for `project` when it's an application.

  Note that this will obscure the widgets on the infoview, such that
  hovering over the group elements won't bring you back to `project`.
-/
@[delab app.DFunLike.coe]
def delab_project' : Delab := do
  withOverApp 6 do
    let e ← getExpr
    let mkApp5 (.const ``project _) _ _ _ _ _ := e.appFn!.appArg!' | failure
    let f_mk_mk ← withNaryArg 5 delab
    `($f_mk_mk)

/-! ### Helpers -/

theorem trivialSpanProp_of_mem_trivialSpanRoot_pairs {w : GradedPartialChevalleyGroup Φ R} {p : Φ × Φ}
    (h : p ∈ w.sys.trivialSpanRootPairs)
      : trivialSpanPropOfRootPair w.project p := by
  intro i j hi hj t u
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.trivialSpanRelations
  constructor
  · tauto
  · simp only [trivialSpanRelations]
    simp only [Set.mem_iUnion]
    use p, h
    rw [trivialSpanRelationsOfRootPair]
    exists i, j, hi, hj, t, u

theorem singleSpanProp_of_mem_singleSpanRoot_pairs (w : GradedPartialChevalleyGroup Φ R) (p : SingleSpanRootPair Φ)
  (h : p ∈ w.sys.singleSpanRootPairs)
    : singleCommutatorPropOfRootPair w.project p := by
  intro i j hi hj t u
  apply eq_of_mul_inv_eq_one
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.singleSpanRelations
  constructor
  · tauto
  · simp only [singleSpanRelations]
    simp only [Set.mem_iUnion]
    use p, h
    rw [singleSpanRelationsOfRootPair]
    exists i, j, hi, hj, t, u

theorem doubleSpanProp_of_mem_doubleSpanRootPairs (w : GradedPartialChevalleyGroup Φ R) (p : DoubleSpanRootPair Φ)
  (h : p ∈ w.sys.doubleCommutatorRootPairs)
    : doubleSpanPropOfRootPair w.project p := by
  intro i j hi hj t u
  apply eq_of_mul_inv_eq_one
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.doubleSpanRelations
  constructor
  · tauto
  · simp only [doubleSpanRelations]
    simp only [Set.mem_iUnion]
    use p, h
    rw [doubleSpanRelationsOfRootPair]
    exists i, j, hi, hj, t, u

theorem mixedDegreeProp_of_mem_presentRoots (w : GradedPartialChevalleyGroup Φ R)
  {ζ : Φ} (h : ζ ∈ w.sys.presentRoots)
    : mixedDegreePropOfRoot w.project ζ := by
  intro i j hi hj t u
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.mixedDegreeCommutatorRelations
  constructor
  · tauto
  · simp only [mixedDegreeCommutatorRelations]
    simp only [Set.mem_iUnion]
    use ζ, h
    rw [mixedDegreeRelationsOfRoot]
    exists i, j, hi, hj, t, u

theorem lin_of_root_of_mem_presentRoots (w : GradedPartialChevalleyGroup Φ R) {ζ : Φ} (h : ζ ∈ w.sys.presentRoots)
    : lin_of_root(w.project, ζ) := by
  intro i hi t u
  apply eq_of_mul_inv_eq_one
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.linearityRelations
  constructor
  · tauto
  · simp only [linearityRelations]
    simp only [Set.mem_iUnion]
    use ζ, h
    rw [linearityRelationsOfRoot]
    exists i, hi, t, u

theorem liftedProp_of_mem_lifted (w : GradedPartialChevalleyGroup Φ R)
    : ∀ S ∈ w.lifted_rels_sets, ∀ r ∈ S, w.project r = 1 := by
  intro S _ _ _
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use ⋃₀ lifted_rels_sets w
  constructor
  · tauto
  · apply Set.mem_sUnion.mpr
    use S

theorem definitionProp_of_define (w : GradedPartialChevalleyGroup Φ R)
    : ∀ (ζ : Φ) (i : ℕ) (hi : i ≤ height ζ) (t : R), w.project {ζ, i, t} = w.project (w.define (GradedChevalleyGenerator.mk ζ i hi t))
      := by
  intro ζ i hi t
  apply eq_of_inv_mul_eq_one
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.definitionRelations
  constructor
  · tauto
  · simp only [definitionRelations]
    simp only [Set.mem_iUnion]
    use ζ
    simp only [Set.mem_setOf_eq]
    use i, hi, t

section declareThms

open Lean Parser.Tactic
set_option hygiene false

def makeCommands (m : MacroM Syntax) : MacroM (TSyntax `command) := do
  let cmds ← Syntax.getArgs <$> m
  return ⟨mkNullNode cmds⟩

macro "declare_trivial_span_expr_thm" w:ident R:term:arg r₁:term:arg r₂:term:arg : command => do
  let exprAs := TSyntax.mapIdent₂ r₁ r₂
    (fun s₁ s₂ => "expr_" ++ s₁ ++ "_" ++ s₂ ++ "_as_" ++ s₂ ++ "_" ++ s₁)
  let commName := TSyntax.mapIdent₂ r₁ r₂
    (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂)
  let commOf ← `(rwRule| $commName:term)
  makeCommands `(section
    @[group_reassoc] theorem $exprAs
      : ∀ ⦃i j : ℕ⦄ (hi : i ≤ height $r₁) (hj : j ≤ height $r₂) (t u : $R),
        commutes(($w $R).project {$r₁:term, i, t},
                ($w $R).project {$r₂:term, j, u}) := by
      intro i j hi hj t u
      apply triv_comm_iff_commutes.mp
      rw [$commOf]
      <;> try assumption
  end)

macro "declare_trivial_span_of_root_pair_thms" w:ident R:term:arg r₁:term:arg r₂:term:arg : command => do
  let commOf := TSyntax.mapIdent₂ r₁ r₂ (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂)
  makeCommands `(section
    theorem $commOf : trivialSpanPropOfRootPair ($w $R).project ($r₁, $r₂) :=
      ($w $R).trivialSpanProp_of_mem_trivialSpanRoot_pairs (by unfold $w; simp only; tauto)
    declare_trivial_span_expr_thm $w $R $r₁ $r₂
  end)

macro "declare_single_span_expr_thms" w:ident R:term:arg r₁:term:arg r₂:term:arg r₃:term:arg n:num : command => do
  let innerTerm ←
    if n.getNat = 1 then `(t * u)
    else                 `($n * t * u)
  let commOf := TSyntax.mapIdent₂ r₁ r₂ (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂)
  let exprAs := TSyntax.mapIdent₃ r₁ r₂ r₃
    (fun s₁ s₂ s₃ => "expr_" ++ s₃ ++ "_as_" ++ s₁ ++ "_" ++ s₂ ++ "_" ++ s₁ ++ "_" ++ s₂)
  let exprAsRev := TSyntax.mapIdent₃ r₁ r₂ r₃
    (fun s₁ s₂ s₃ => "expr_" ++ s₁ ++ "_" ++ s₂ ++ "_as_" ++ s₃ ++ "_" ++ s₂ ++ "_" ++ s₁)
  makeCommands `(section
    theorem $exprAs
      : ∀ ⦃i j : ℕ⦄ (hi : i ≤ height $r₁) (hj : j ≤ height $r₂) (t u : $R),
        (($w $R).project
          {$r₃:term, i + j, $innerTerm})
          = ($w $R).project {$r₁:term, i, t}
            * ($w $R).project {$r₂:term, j, u}
            * ($w $R).project {$r₁:term, i, -t}
            * ($w $R).project {$r₂:term, j, -u} := by
      intro i j hi hj t u
      have := $commOf hi hj t u
      chev_simp [commutatorElement_def, one_mul, mul_one] at this
      symm at this
      exact this

    @[group_reassoc]
    theorem $exprAsRev
      : ∀ ⦃i j : ℕ⦄ (hi : i ≤ height $r₁) (hj : j ≤ height $r₂) (t u : $R),
        reorder_left(
          ($w $R).project {$r₁:term, i, t},
          ($w $R).project {$r₂:term, j, u},
          (($w $R).project {$r₃:term, i + j, $innerTerm})
        ) := by
      intro i j hi hj t u
      have := $commOf hi hj t u
      chev_simp [commutatorElement_def, one_mul, mul_one] at this
      grw [← this]
  end)

macro "declare_single_span_of_root_pair_thms"
    w:ident R:term:arg
    r₁:term:arg r₂:term:arg r₃:term:arg n:num : command => do
  let commOf := TSyntax.mapIdent₂ r₁ r₂ (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂)
  makeCommands `(section
    theorem $commOf : singleCommutatorPropOfRootPair ($w $R).project ⟨$r₁, $r₂, $r₃, $n, rfl⟩ :=
      ($w $R).singleSpanProp_of_mem_singleSpanRoot_pairs ⟨$r₁, $r₂, $r₃, $n, rfl⟩ (by unfold $w; simp only; tauto)
    declare_single_span_expr_thms $w $R $r₁ $r₂ $r₃ $n
  end)

macro "declare_lin_id_inv_thms" w:ident R:term:arg root:term:arg : command => do
  let linOf := root.mapIdent ("lin_of_" ++ ·)
  let idOf := root.mapIdent ("id_of_" ++ ·)
  let invOf := root.mapIdent ("inv_of_" ++ ·)
  makeCommands `(section
    @[group_reassoc (attr := simp, chev_simps)]
    theorem $linOf : lin_of_root(($w $R).project, $root) :=
      lin_of_root_of_mem_presentRoots ($w $R) (by unfold $w; simp only; tauto)

    @[simp, chev_simps]
    theorem $idOf : id_of_root(($w $R).project, $root) :=
      id_of_lin_of_root $linOf

    @[simp, chev_simps]
    theorem $invOf : inv_of_root(($w $R).project, $root) :=
      inv_of_lin_of_root $linOf
  end)

macro "declare_mixed_degree_expr_thm" w:ident R:term:arg r:term:arg : command => do
  let mixedName := r.mapIdent ("comm_of_" ++ ·)
  let mixedRw ← `(rwRule| $mixedName:term)
  let exprName := r.mapIdent (fun s => "expr_" ++ s ++ "_" ++ s ++ "_as_" ++ s ++ "_" ++ s)
  makeCommands `(section
    @[group_reassoc]
    theorem $exprName :
        ∀ ⦃i j : ℕ⦄ (hi : i ≤ height $r) (hj : j ≤ height $r) (t u : $R),
          commutes(($w $R).project {$r:term, i, t},
                  ($w $R).project {$r:term, j, u}) := by
      intro i j hi hj t u
      apply triv_comm_iff_commutes.mp
      rw [$mixedRw]
      <;> try assumption
  end)

macro "declare_mixed_degree_thms" w:ident R:term:arg r:term:arg : command => do
  let mixedName := r.mapIdent ("comm_of_" ++ ·)
  makeCommands `(section
    theorem $mixedName : mixedDegreePropOfRoot ($w $R).project $r :=
      mixedDegreeProp_of_mem_presentRoots ($w $R)
        (by unfold $w; simp only; tauto)
    declare_mixed_degree_expr_thm $w $R $r
  end)

macro "declare_defineThenReflect_thm" w:ident R:term:arg RS:ident r:term:arg : command => do
  let thmName := r.mapIdent ("defineThenReflect_eq_reflect_of_" ++ ·)
  makeCommands `(section
    theorem $thmName
        (g : GradedChevalleyGenerator $RS $R) (h : g.ζ = $r)
        : ($w $R).project (defineThenReflect ($w $R) g)
            = ($w $R).project (FreeGroup.of (reflect g)) := by
      congr
      apply defineThenReflect_eq_reflect_of_mem_presentRoots
      unfold $w
      simp only [h]
      tauto
  end)

-- r₁ is the larger root, as opposed to the above macros
macro "declare_reflected_thm" w:ident R:term:arg v:term:arg
        r₁:term:arg r₂:term:arg r₃:term:arg isNeg:num C:num
        n₁:num n₂:num n₃:num n₄:num n₅:num n₆:num : command => do
  let innerTerm ←
    match isNeg.getNat, C.getNat with
    | 0, 1 => `(t * u)
    | 1, 1 => `(-t * u)
    | 1, _ => `(-$C * t * u)
    | _, _ => `($C * t * u)

  let thmName := TSyntax.mapIdent₃ r₁ r₂ r₃
    (fun s₁ s₂ s₃ => "expr_" ++ s₁ ++ "_as_comm_of_" ++ s₂ ++ "_" ++ s₃ ++ s!"_{n₂.getNat}{n₃.getNat}")

  let defineThenReflect₁ := r₁.mapIdent ("defineThenReflect_eq_reflect_of_" ++ ·)
  let defineThenReflect_thm₁ ← `(simpLemma| $defineThenReflect₁:term)

  let defineThenReflect₂ := r₂.mapIdent ("defineThenReflect_eq_reflect_of_" ++ ·)
  let defineThenReflect_thm₂ ← `(simpLemma| $defineThenReflect₂:term)
  let defineThenReflect_thm₂' ← `(simpLemma| $defineThenReflect₂:term (by assumption))

  let defineThenReflect₃ := r₃.mapIdent ("defineThenReflect_eq_reflect_of_" ++ ·)
  let defineThenReflect_thm₃ ← `(simpLemma| $defineThenReflect₃:term)
  let defineThenReflect_thm₃' ← `(simpLemma| $defineThenReflect₃:term (by assumption))

  let exprLemma := TSyntax.mapIdent₃ r₁ r₂ r₃
    (fun s₁ s₂ s₃ => "expr_" ++ s₁ ++ "_as_comm_of_" ++ s₂ ++ "_" ++ s₃ ++ s!"_{n₅.getNat}{n₆.getNat}")
  let exprLemmaRw ← `(rwRule| $exprLemma:term)

  makeCommands `(section
    lemma $thmName :
        ∀ (t u : $R),
          (($w $R).project {$r₁:term, $n₁, $innerTerm})
            = ⁅($w $R).project {$r₂:term, $n₂, t}, ($w $R).project {$r₃:term, $n₃, u}⁆ := by
      intro t u
      have : ($w $R).project {$r₁:term, $n₁, $innerTerm}
        = defineThenReflectOfPresentedGroup $v (($w $R).project {$r₁:term, $n₄, $innerTerm}) := by
          simp only [defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₁, reflect, PositiveRootSystem.height, height]
      rw [this]; clear this
      have : ⁅($w $R).project {$r₂:term, $n₂, t}, ($w $R).project {$r₃:term, $n₃, u}⁆
          = defineThenReflectOfPresentedGroup $v
              ⁅($w $R).project {$r₂:term, $n₅, t}, ($w $R).project {$r₃:term, $n₆, u}⁆ := by
        -- Sometimes, the `defineThenReflect_` lemmas require the `Fchar` assumption
        first
        | simp only [map_commutatorElement, defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₂, $defineThenReflect_thm₃, reflect, PositiveRootSystem.height, height]
          done
        | simp only [map_commutatorElement, defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₂', $defineThenReflect_thm₃, reflect, PositiveRootSystem.height, height]
          done
        | simp only [map_commutatorElement, defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₂, $defineThenReflect_thm₃', reflect, PositiveRootSystem.height, height]
          done
        | simp only [map_commutatorElement, defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₂', $defineThenReflect_thm₃', reflect, PositiveRootSystem.height, height]
      rw [this, $exprLemmaRw]
      <;> try assumption
  end)

macro "declare_triv_comm_reflected_thm" w:ident R:term:arg v:term:arg
        r₁:term:arg r₂:term:arg
        n₁:num n₂:num n₃:num n₄:num : command => do
  let commOf := TSyntax.mapIdent₂ r₁ r₂
    (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂ ++ s!"_{n₁.getNat}{n₂.getNat}")
  let commLemma := TSyntax.mapIdent₂ r₁ r₂
    (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂ ++ s!"_{n₃.getNat}{n₄.getNat}")
  let commLemmaRw ← `(rwRule| $commLemma:term)

  let defineThenReflect₁ := r₁.mapIdent ("defineThenReflect_eq_reflect_of_" ++ ·)
  let defineThenReflect_thm₁ ← `(simpLemma| $defineThenReflect₁:term)
  let defineThenReflect_thm₁' ← `(simpLemma| $defineThenReflect₁:term (by assumption))

  let defineThenReflect₂ := r₂.mapIdent ("defineThenReflect_eq_reflect_of_" ++ ·)
  let defineThenReflect_thm₂ ← `(simpLemma| $defineThenReflect₂:term)
  let defineThenReflect_thm₂' ← `(simpLemma| $defineThenReflect₂:term (by assumption))


  makeCommands `(section
    lemma $commOf : ∀ (t u : $R),
        ⁅ ($w $R).project {$r₁:term, $n₁, t}, ($w $R).project {$r₂:term, $n₂, u} ⁆ = 1 := by
      intro t u
      have : ⁅ ($w $R).project {$r₁:term, $n₁, t}, ($w $R).project {$r₂:term, $n₂, u} ⁆
        = defineThenReflectOfPresentedGroup $v
            ⁅ ($w $R).project {$r₁:term, $n₃, t}, ($w $R).project {$r₂:term, $n₄, u} ⁆ := by
        -- Sometimes, the `defineThenReflect_` lemmas require the `Fchar` assumption
        first
        | simp only [map_commutatorElement, defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₁, $defineThenReflect_thm₂, reflect, PositiveRootSystem.height, height]
          done
        | simp only [map_commutatorElement, defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₁', $defineThenReflect_thm₂, reflect, PositiveRootSystem.height, height]
          done
        | simp only [map_commutatorElement, defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₁, $defineThenReflect_thm₂', reflect, PositiveRootSystem.height, height]
          done
        | simp only [map_commutatorElement, defineThenReflectOfPresentedGroup_of_project, FreeGroup.lift.of,
            $defineThenReflect_thm₁', $defineThenReflect_thm₂', reflect, PositiveRootSystem.height, height]
      rw [this, $commLemmaRw]
      <;> try assumption
      rfl
  end)

end declareThms /- section -/

end GradedPartialChevalleyGroup

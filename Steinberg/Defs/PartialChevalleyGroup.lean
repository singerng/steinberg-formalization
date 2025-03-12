/-

LICENSE goes here.

-/

import Steinberg.Defs.PositiveRootSystem
import Steinberg.Defs.Commutator
import Steinberg.Upstream.PresentedGroup
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

namespace PartialChevalley

/-! ## Generators of (ungraded) Chevalley group -/

/--
  Generators of the Chevalley subgroup corresponding to a positive root system
  over a ring.
-/
structure ChevalleyGenerator (Φ : Type TΦ) [PositiveRootSystem Φ] (R : Type TR) [Ring R] where
  mk ::
  ζ : Φ
  t : R

namespace ChevalleyGenerator

/-- Helper function to construct and inject a `ChevalleyGenerator`. -/
def free_mk (ζ : Φ) (t : R) : FreeGroup (ChevalleyGenerator Φ R) :=
  FreeGroup.of <| (mk ζ t)

set_option hygiene false in
/--
  Shorthand for building free group elements from a root and ring element.

  Note: To re-use this notation for specific `Chevalley`-like groups,
  re-define it for that group and set the priority higher.

  Then implement delaboration to use the `free_mk` delab here.
-/
scoped notation (priority:=1000) "{{" ζ ", " t "}}" =>
  free_mk ζ t

open Lean PrettyPrinter Delaborator SubExpr in
/--
  Delaborates `free_mk` to use the `{ }` notation defined above.

  Delaboration makes it so that the infoview uses the nice notation.
-/
@[delab free_mk]
def delab_free_mk : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``free_mk 8
  let ζ ← withNaryArg 4 delab
  let t ← withNaryArg 5 delab
  `({{ $(ζ):term, $(t):term }})

theorem eq_of_R_eq (ζ : Φ) {t : R} (u : R) (h : t = u)
    : {{ζ, t}} = {{ζ, u}} := by
  congr

end ChevalleyGenerator

/-! ### Statements about generators which we assume and/or prove -/

open ChevalleyGenerator

/-! #### Commutator for generators from two roots which span no additional roots -/

/- Theorem stating that commutator of generators for two roots vanishes. -/
def trivial_commutator_of_root_pair (f : FreeGroup (ChevalleyGenerator Φ R) →* G) (ζ η : Φ) : Prop :=
  ∀ (t u : R),
    ⁅ f {{ζ, t}}, f {{η, u}} ⁆ = 1

/-
The set of elements which must vanish according to the theorem that the commutator of generators
for two roots vanishes. (Used to construct a `PresentedGroup`.)
-/
def rels_of_trivial_commutator_of_root_pair (R : Type TR) [Ring R] (ζη : Φ × Φ)
    : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  let (ζ, η) := ζη;
  { ⁅ {{ζ, t}}, {{η, u}} ⁆
    | (t : R) (u : R) }

/-! #### Commutator for two generators from two roots which span one additional root -/

def single_commutator_of_root_pair (f : FreeGroup (ChevalleyGenerator Φ R) →* G) (ζ η θ : Φ)
    (C : ℤ)  : Prop :=
  ∀ (t u : R),
    ⁅ f {{ζ, t}}, f {{η, u}} ⁆ = f {{θ, ↑C * t * u}}

def rels_of_single_commutator_of_root_pair (R : Type TR) [Ring R] (p : SingleSpanRootPair Φ) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  let ⟨ ζ, η, θ, C, h_height ⟩ := p;
  { ⁅ {{ζ, t}}, {{η, u}} ⁆ * {{θ, C * t * u}}⁻¹
    | (t : R) (u : R) }

/-! #### Commutator for two generators from two roots which span one additional root -/

def double_commutator_of_root_pair (f : FreeGroup (ChevalleyGenerator Φ R) →* G) (ζ η θ₁ θ₂ : Φ)
    (C₁ C₂ : ℤ) (h_height₁ : height θ₁ = height ζ + height η) (h_height₂ : height θ₂ = height ζ + 2 * height η) : Prop :=
  ∀ (t u : R),
    ⁅ f {{ζ, t}}, f {{η, u}} ⁆ = f {{θ₁, ↑C₁ * t * u}} * f {{θ₂, ↑C₂ * t * u * u}}

def rels_of_double_commutator_of_root_pair (R : Type TR) [Ring R] (p : DoubleSpanRootPair Φ) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  let ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ := p;
  { ⁅ {{ζ, t}}, {{η, u}} ⁆ *
    ({{θ₁, C₁ * t * u}} * {{θ₂, C₂ * t * u * u}})⁻¹
    | (t : R) (u : R) }

/-! #### Linearity relation for products of generators from a single root -/

/- Linearity of coefficients for products of generators of a single root (with the same degree). -/
def rels_of_lin_of_root (R : Type TR) [Ring R] (ζ : Φ) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  { {{ζ, t}} * {{ζ, u}} * {{ζ, t + u}}⁻¹
    | (t : R) (u : R) }

/-! ### Additional properties implied by linearity and implications therein -/

section ofRoot

set_option quotPrecheck false

/--
  Linearity of group elements on a particular root.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ) (t u), f {{ζ, t}} * f {ζ, i, u} = f {ζ, i, t + u}`.

  `(f : FreeGroup (ChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "lin_of_root" "(" f ", " ζ ")" =>
  ∀ (t u),
    f {{ζ, t}} * f {{ζ, u}} = f {{ζ, t + u}}

/--
  Ring coefficient 0 gives an identity element.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ), f {ζ, i, 0} = 1`.

  `(f : FreeGroup (ChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "id_of_root" "(" f ", " ζ ")" =>
  f {{ζ, 0}} = 1
/--
  Negating the coefficient inverts the generator.

  Equivalent to `∀ (i : ℕ) (hi : i ≤ height ζ) (t : R), (f {{ζ, t}})⁻¹ = 1`.

  `(f : FreeGroup (ChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "inv_of_root" "(" f ", " ζ ")" =>
  ∀ ⦃i : ℕ⦄ (hi : i ≤ height ζ) (t),
    (f {{ζ, t}})⁻¹ = f {{ζ, -t}}

/- Linearity implies identity (essentially a standard fact about group homomorphisms). -/
theorem id_of_lin_of_root {f : FreeGroup (ChevalleyGenerator Φ R) →* G} {ζ : Φ}
    : lin_of_root(f, ζ) → id_of_root(f, ζ) := by
  intro h_lin
  apply @mul_left_cancel _ _ _ (f {{ζ, 0}})
  rw [mul_one, h_lin, add_zero]

/- Linearity implies inverse-ness (essentially a standard fact about group homomorphisms). -/
theorem inv_of_lin_of_root {f : FreeGroup (ChevalleyGenerator Φ R) →* G} {ζ : Φ}
    : lin_of_root(f, ζ) → inv_of_root(f, ζ) := by
  intro h_lin i hi t
  apply @mul_left_cancel _ _ _ (f {{ζ, t}})
  rw [mul_inv_cancel, h_lin, add_neg_cancel, id_of_lin_of_root h_lin]

end ofRoot

/-! ### ASDFJKL; -/

structure PartialChevalleyGroup (Φ : Type TΦ) [PositiveRootSystem Φ] (R : Type TR) [Ring R] where
  mk ::
  sys : PartialChevalleySystem Φ

namespace PartialChevalleyGroup

open PartialChevalleyGroup

/-! ### Sets of relations -/
def trivial_comm_rels (w : PartialChevalleyGroup Φ R) :=
  ⋃₀ (rels_of_trivial_commutator_of_root_pair R '' w.sys.trivial_comm_root_pairs)

def single_comm_rels (w : PartialChevalleyGroup Φ R) :=
  ⋃₀ (rels_of_single_commutator_of_root_pair R '' w.sys.single_comm_root_pairs)

def double_comm_rels (w : PartialChevalleyGroup Φ R) :=
  ⋃₀ (rels_of_double_commutator_of_root_pair R  '' w.sys.double_comm_root_pairs)

def lin_rels (w : PartialChevalleyGroup Φ R) :=
  ⋃₀ (rels_of_lin_of_root R '' w.sys.present_roots)

def all_rels (w : PartialChevalleyGroup Φ R) :=
  ⋃₀ {trivial_comm_rels w, single_comm_rels w, double_comm_rels w, lin_rels w}

/-! ### The group and the embedding -/

abbrev group (w : PartialChevalleyGroup Φ R) :=
  PresentedGroup (PartialChevalleyGroup.all_rels w)

def pres_mk (w : PartialChevalleyGroup Φ R) : FreeGroup (ChevalleyGenerator Φ R) →* group w :=
  PresentedGroup.mk (PartialChevalleyGroup.all_rels w)

/-- Mapping between two PartialChevalleyGroup graded groups -/
theorem graded_injection (w₁ w₂ : PartialChevalleyGroup Φ R)
  (h_triv : ∀ p ∈ w₁.sys.trivial_comm_root_pairs, p ∈ w₂.sys.trivial_comm_root_pairs ∨
    (∀ r ∈ (rels_of_trivial_commutator_of_root_pair R p), w₂.pres_mk r = 1))
  (h_single : ∀ p ∈ w₁.sys.single_comm_root_pairs, p ∈ w₂.sys.single_comm_root_pairs ∨
    (∀ r ∈ (rels_of_single_commutator_of_root_pair R p), w₂.pres_mk r = 1))
  (h_doub : ∀ p ∈ w₁.sys.double_comm_root_pairs, p ∈ w₂.sys.double_comm_root_pairs ∨
    (∀ r ∈ (rels_of_double_commutator_of_root_pair R p), w₂.pres_mk r = 1))
  (h_lin : ∀ p ∈ w₁.sys.present_roots, p ∈ w₂.sys.present_roots ∨
    (∀ r ∈ (rels_of_lin_of_root R p), w₂.pres_mk r = 1))
  : ∀ r ∈ w₁.all_rels, w₂.pres_mk r = 1 := by
  simp only [all_rels]
  intro r h
  simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion] at h
  rcases h with h|h|h|h
  · simp only [trivial_comm_rels, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_triv p
    simp_all only [forall_const]
    rcases h_triv with h|h
    · apply eq_one_of_mem_rels
      simp only [all_rels]
      have : r ∈ w₂.trivial_comm_rels := by
        simp only [trivial_comm_rels]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto
  · simp only [single_comm_rels, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_single p
    simp_all only [forall_const]
    rcases h_single with h|h
    · apply eq_one_of_mem_rels
      simp only [all_rels]
      have : r ∈ w₂.single_comm_rels := by
        simp only [single_comm_rels]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto
  · simp only [double_comm_rels, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_doub p
    simp_all only [forall_const]
    rcases h_doub with h|h
    · apply eq_one_of_mem_rels
      simp only [all_rels]
      have : r ∈ w₂.double_comm_rels := by
        simp only [double_comm_rels]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto
  · simp only [lin_rels, Set.sUnion_image, Set.mem_iUnion, exists_prop] at h
    rcases h with ⟨ p, h_p, h_r_p ⟩
    specialize h_lin p
    simp_all only [forall_const]
    rcases h_lin with h|h
    · apply eq_one_of_mem_rels
      simp only [all_rels]
      have : r ∈ w₂.lin_rels := by
        simp only [lin_rels]
        simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
        use p
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      tauto
    · tauto

open Lean PrettyPrinter Delaborator SubExpr in
/--
  Delaborator for `pres_mk` when it's an application.

  Note that this will obscure the widgets on the infoview, such that
  hovering over the group elements won't bring you back to `pres_mk`.
-/
@[delab app.DFunLike.coe]
def delab_pres_mk' : Delab := do
  withOverApp 6 do
    let e ← getExpr
    let mkApp5 (.const ``pres_mk _) _ _ _ _ _ := e.appFn!.appArg!' | failure
    let f_mk_mk ← withNaryArg 5 delab
    `($f_mk_mk)

/-! ### Helpers -/

theorem trivial_commutator_helper {w : PartialChevalleyGroup Φ R} {ζ η : Φ}
    (h : (ζ, η) ∈ w.sys.trivial_comm_root_pairs)
      : trivial_commutator_of_root_pair w.pres_mk ζ η := by
  intro i j
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.trivial_comm_rels
  constructor
  · tauto
  · rw [trivial_comm_rels]
    apply Set.mem_sUnion.mpr
    use rels_of_trivial_commutator_of_root_pair R (ζ, η)
    constructor
    · simp only [Set.mem_image]
      use (ζ, η)
    · rw [rels_of_trivial_commutator_of_root_pair]
      exists i, j

-- TODO: Move this to a different file?
theorem helper {x y z : G} : x * y * z⁻¹ = 1 → x * y = z := by
  intro h
  apply @mul_right_cancel _ _ _ _ z⁻¹
  rw [mul_inv_cancel]
  exact h

theorem single_commutator_helper (w : PartialChevalleyGroup Φ R) (ζ η θ : Φ) (C : ℤ)
  (h_height : height θ = height ζ + height η)
  (h : ⟨ ζ, η, θ, C, h_height ⟩ ∈ w.sys.single_comm_root_pairs)
    : single_commutator_of_root_pair w.pres_mk ζ η θ C := by
  intro t u
  apply helper
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.single_comm_rels
  constructor
  · tauto
  · rw [single_comm_rels]
    apply Set.mem_sUnion.mpr
    use (rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩)
    constructor
    · simp only [Set.mem_image]
      use ⟨ ζ, η, θ, C, h_height ⟩
    · rw [rels_of_single_commutator_of_root_pair]
      exists t, u

theorem double_commutator_helper (w : PartialChevalleyGroup Φ R) (ζ η θ₁ θ₂ : Φ) (C₁ C₂ : ℤ)
  (h_height₁ : height θ₁ = height ζ + height η)
  (h_height₂ : height θ₂ = height ζ + 2 * height η)
  (h : ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ ∈ w.sys.double_comm_root_pairs)
    : double_commutator_of_root_pair w.pres_mk ζ η θ₁ θ₂ C₁ C₂ h_height₁ h_height₂ := by
  intro t u
  apply helper
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.double_comm_rels
  constructor
  · tauto
  · rw [double_comm_rels]
    apply Set.mem_sUnion.mpr
    use (rels_of_double_commutator_of_root_pair R ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩)
    constructor
    · simp only [Set.mem_image]
      use ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩
    · rw [rels_of_double_commutator_of_root_pair]
      exists t, u

theorem lin_helper (w : PartialChevalleyGroup Φ R) {ζ : Φ} (h : ζ ∈ w.sys.present_roots)
    : lin_of_root(w.pres_mk, ζ) := by
  intro t u
  apply helper
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.lin_rels
  constructor
  · tauto
  · rw [lin_rels]
    apply Set.mem_sUnion.mpr
    use rels_of_lin_of_root R ζ
    constructor
    · simp only [Set.mem_image]
      use ζ
    · rw [rels_of_lin_of_root]
      exists t, u

end PartialChevalleyGroup

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

instance instCoeProd : Coe (Φ × R) (ChevalleyGenerator Φ R) :=
  ⟨fun p => ⟨p.1, p.2⟩⟩

/--
  Shorthand for building free group elements from a root and ring element.

  Note: To re-use this notation for specific `Chevalley`-like groups,
  re-define it for that group and set the priority higher.
  Then implement delaboration to use the delab defined below.
-/
scoped notation (priority:=1000) "{" ζ ", " t "}" =>
  FreeGroup.of (ChevalleyGenerator.mk ζ t)

section DelabBraces

open Lean PrettyPrinter Delaborator SubExpr

/--
  Delaborates `ChevalleyGenerator.mk` to use the `{ }` notation.

  Delaboration makes it so that the infoview uses the nice notation.
-/
@[delab app.Steinberg.PartialChevalley.ChevalleyGenerator.mk]
def delab_generator_mk : Delab := do
  let e ← getExpr

  -- Only delab a full application of `.mk`
  guard $ e.isAppOfArity' ``ChevalleyGenerator.mk 6

  let ζ ← withNaryArg 4 delab
  let t ← withNaryArg 5 delab
  `({ $ζ:term, $t:term })


/--
  Delaborates `FreeGroup.of` to use the `{ }` notation.

  Delaboration makes it so that the infoview uses the nice notation.
-/
@[delab app.FreeGroup.of]
def delab_free_mk : Delab := do
  let e ← getExpr

  -- Only delab `FreeGroup.of` if its type and value are given to the app
  guard $ e.isAppOfArity' ``FreeGroup.of 2

  -- Only delab `FreeGroup.of` if the type is a Chevalley generator
  let ty := e.getAppArgs.get! 0
  guard $ ty.isAppOfArity' ``ChevalleyGenerator 4

  -- Use the delaboration of the generator
  -- Since this might be a more complicated term or calculation,
  -- we don't call `delab_generator_mk` directly
  let g ← withNaryArg 1 delab
  `($g)

end DelabBraces /- section -/

theorem eq_of_R_eq (ζ : Φ) {t : R} (u : R) (h : t = u)
    : {ζ, t} = {ζ, u} := by
  congr

end ChevalleyGenerator

open ChevalleyGenerator

/-! ### Statements about generators which we assume and/or prove -/

section Relations

/-! #### Commutator for generators from two roots which span no additional roots -/

/- Theorem stating that commutator of generators for two roots vanishes. -/
def trivial_commutator_of_root_pair (f : FreeGroup (ChevalleyGenerator Φ R) →* G) (p : Φ × Φ) : Prop :=
  let (ζ, η) := p;
  ∀ (t u : R),
    ⁅ f {ζ, t}, f {η, u} ⁆ = 1

/-
The set of elements which must vanish according to the theorem that the commutator of generators
for two roots vanishes. (Used to construct a `PresentedGroup`.)
-/
def rels_of_trivial_commutator_of_root_pair (R : Type TR) [Ring R] (p : Φ × Φ)
    : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  let (ζ, η) := p;
  { ⁅ {ζ, t}, {η, u} ⁆
    | (t : R) (u : R) }

/-! #### Commutator for two generators from two roots which span one additional root -/

def single_commutator_of_root_pair (f : FreeGroup (ChevalleyGenerator Φ R) →* G) (p : SingleSpanRootPair Φ) : Prop :=
  let ⟨ ζ, η, θ, C, _ ⟩ := p;
  ∀ (t u : R),
    ⁅ f {ζ, t}, f {η, u} ⁆ = f {θ, ↑C * t * u}

def rels_of_single_commutator_of_root_pair (R : Type TR) [Ring R] (p : SingleSpanRootPair Φ) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  let ⟨ ζ, η, θ, C, _ ⟩ := p;
  { ⁅ {ζ, t}, {η, u} ⁆ * {θ, C * t * u}⁻¹
    | (t : R) (u : R) }

/-! #### Commutator for two generators from two roots which span one additional root -/

def double_commutator_of_root_pair (f : FreeGroup (ChevalleyGenerator Φ R) →* G) (p : DoubleSpanRootPair Φ) : Prop :=
  let ⟨ ζ, η, θ₁, θ₂, C₁, C₂, _, _ ⟩ := p;
  ∀ (t u : R),
    ⁅ f {ζ, t}, f {η, u} ⁆ = f {θ₁, ↑C₁ * t * u} * f {θ₂, ↑C₂ * t * u * u}

def rels_of_double_commutator_of_root_pair (R : Type TR) [Ring R] (p : DoubleSpanRootPair Φ) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  let ⟨ ζ, η, θ₁, θ₂, C₁, C₂, _, _ ⟩ := p;
  { ⁅ {ζ, t}, {η, u} ⁆ *
    ({θ₁, C₁ * t * u} * {θ₂, C₂ * t * u * u})⁻¹
    | (t : R) (u : R) }

/-! #### Linearity relation for products of generators from a single root -/

/- Linearity of coefficients for products of generators of a single root (with the same degree). -/
def rels_of_lin_of_root (R : Type TR) [Ring R] (ζ : Φ) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  { {ζ, t} * {ζ, u} * {ζ, t + u}⁻¹
    | (t : R) (u : R) }

end Relations

/-! ### Additional properties implied by linearity and implications therein -/

section ofRoot

set_option quotPrecheck false

/--
  Linearity of group elements on a particular root.

  Equivalent to `∀ (t u), f {ζ, t} * f {ζ, i, u} = f {ζ, i, t + u}`.

  `(f : FreeGroup (ChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "lin_of_root" "(" f ", " ζ ")" =>
  ∀ (t u), f {ζ, t} * f {ζ, u} = f {ζ, t + u}

/--
  Ring coefficient 0 gives an identity element.

  Equivalent to `f {ζ, i, 0} = 1`.

  `(f : FreeGroup (ChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "id_of_root" "(" f ", " ζ ")" =>
  f {ζ, 0} = 1
/--
  Negating the coefficient inverts the generator.

  Equivalent to `∀ (t : R), (f {ζ, t})⁻¹ = 1`.

  `(f : FreeGroup (ChevalleyGenerator Φ R) →* G)`
  `(ζ : Φ)`
-/
scoped notation "inv_of_root" "(" f ", " ζ ")" =>
  ∀ (t), (f {ζ, t})⁻¹ = f {ζ, -t}

/- Linearity implies identity (essentially a standard fact about group homomorphisms). -/
theorem id_of_lin_of_root {f : FreeGroup (ChevalleyGenerator Φ R) →* G} {ζ : Φ}
    : lin_of_root(f, ζ) → id_of_root(f, ζ) := by
  intro h_lin
  apply @mul_left_cancel _ _ _ (f {ζ, 0})
  rw [mul_one, h_lin, add_zero]

/- Linearity implies inverse-ness (essentially a standard fact about group homomorphisms). -/
theorem inv_of_lin_of_root {f : FreeGroup (ChevalleyGenerator Φ R) →* G} {ζ : Φ}
    : lin_of_root(f, ζ) → inv_of_root(f, ζ) := by
  intro h_lin t
  apply @mul_left_cancel _ _ _ (f {ζ, t})
  rw [mul_inv_cancel, h_lin, add_neg_cancel, id_of_lin_of_root h_lin]

end ofRoot

structure PartialChevalleyGroup (Φ : Type TΦ) [PositiveRootSystem Φ] (R : Type TR) [Ring R] where
  mk ::
  sys : PartialChevalleySystem Φ

namespace PartialChevalleyGroup

open PartialChevalleyGroup

/-! ### Sets of relations -/
def trivial_comm_rels (w : PartialChevalleyGroup Φ R) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  ⋃ (p ∈ w.sys.trivial_comm_root_pairs), rels_of_trivial_commutator_of_root_pair R p

def single_comm_rels (w : PartialChevalleyGroup Φ R) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  ⋃ (p ∈ w.sys.single_comm_root_pairs), rels_of_single_commutator_of_root_pair R p

def double_comm_rels (w : PartialChevalleyGroup Φ R) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  ⋃ (p ∈ w.sys.double_comm_root_pairs), rels_of_double_commutator_of_root_pair R p

def lin_rels (w : PartialChevalleyGroup Φ R) : Set (FreeGroup (ChevalleyGenerator Φ R)) :=
  ⋃ (ζ ∈ w.sys.present_roots), rels_of_lin_of_root R ζ

def all_rels (w : PartialChevalleyGroup Φ R) :=
  ⋃₀ {trivial_comm_rels w, single_comm_rels w, double_comm_rels w, lin_rels w}

/-! ### The group and the embedding -/

abbrev group (w : PartialChevalleyGroup Φ R) :=
  PresentedGroup (PartialChevalleyGroup.all_rels w)

def pres_mk (w : PartialChevalleyGroup Φ R) : FreeGroup (ChevalleyGenerator Φ R) →* group w :=
  PresentedGroup.mk (PartialChevalleyGroup.all_rels w)

/-- Mapping between two PartialChevalleyGroups -/
theorem injection (w₁ w₂ : PartialChevalleyGroup Φ R)
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

theorem trivial_commutator_helper {w : PartialChevalleyGroup Φ R} {p : Φ × Φ}
    (h : p ∈ w.sys.trivial_comm_root_pairs)
      : trivial_commutator_of_root_pair w.pres_mk p := by
  intro t u
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.trivial_comm_rels
  constructor
  · tauto
  · simp only [trivial_comm_rels]
    simp only [Set.mem_iUnion]
    use p, h
    rw [rels_of_trivial_commutator_of_root_pair]
    exists t, u

theorem single_commutator_helper (w : PartialChevalleyGroup Φ R) (p : SingleSpanRootPair Φ)
  (h : p ∈ w.sys.single_comm_root_pairs)
    : single_commutator_of_root_pair w.pres_mk p := by
  intro t u
  apply eq_of_mul_inv_eq_one
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.single_comm_rels
  constructor
  · tauto
  · simp only [single_comm_rels]
    simp only [Set.mem_iUnion]
    use p, h
    rw [rels_of_single_commutator_of_root_pair]
    exists t, u

theorem double_commutator_helper (w : PartialChevalleyGroup Φ R) (p : DoubleSpanRootPair Φ)
  (h : p ∈ w.sys.double_comm_root_pairs)
    : double_commutator_of_root_pair w.pres_mk p := by
  intro t u
  apply eq_of_mul_inv_eq_one
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.double_comm_rels
  constructor
  · tauto
  · simp only [double_comm_rels]
    simp only [Set.mem_iUnion]
    use p, h
    rw [rels_of_double_commutator_of_root_pair]
    exists t, u

theorem lin_helper (w : PartialChevalleyGroup Φ R) {ζ : Φ} (h : ζ ∈ w.sys.present_roots)
    : lin_of_root(w.pres_mk, ζ) := by
  intro t u
  apply eq_of_mul_inv_eq_one
  apply eq_one_of_mem_rels
  apply Set.mem_sUnion.mpr
  use w.lin_rels
  constructor
  · tauto
  · simp only [lin_rels]
    simp only [Set.mem_iUnion]
    use ζ, h
    rw [rels_of_lin_of_root]
    exists t, u

section declareThms

open Lean Parser.Tactic
set_option hygiene false

def makeCommands (m : MacroM Syntax) : MacroM (TSyntax `command) := do
  let cmds ← Syntax.getArgs <$> m
  return ⟨mkNullNode cmds⟩

macro "declare_ungraded_lin_id_inv_thms" w:ident R:term:arg root:term:arg : command => do
  let linOf := root.mapIdent ("lin_of_" ++ ·)
  let idOf := root.mapIdent ("id_of_" ++ ·)
  let invOf := root.mapIdent ("inv_of_" ++ ·)
  makeCommands `(section
    @[group_reassoc (attr := simp, chev_simps)]
    theorem $linOf : lin_of_root(($w $R).pres_mk, $root) :=
      ($w $R).lin_helper (by unfold $w; simp only; tauto)

    @[simp, chev_simps]
    theorem $idOf : id_of_root(($w $R).pres_mk, $root) :=
      id_of_lin_of_root $linOf

    @[simp, chev_simps]
    theorem $invOf : inv_of_root(($w $R).pres_mk, $root) :=
      inv_of_lin_of_root $linOf
  end)

macro "declare_ungraded_triv_expr_thm" w:ident R:term:arg r₁:term:arg r₂:term:arg : command => do
  let exprAs := TSyntax.mapIdent₂ r₁ r₂
    (fun s₁ s₂ => "expr_" ++ s₁ ++ "_" ++ s₂ ++ "_as_" ++ s₂ ++ "_" ++ s₁)
  let commName := TSyntax.mapIdent₂ r₁ r₂
    (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂)
  let commOf ← `(rwRule| $commName:term)
  makeCommands `(section
    @[group_reassoc] theorem $exprAs
      : ∀ (t u : $R),
        commutes(($w $R).pres_mk {$r₁:term, t},
                ($w $R).pres_mk {$r₂:term, u}) := by
      intro t u
      apply triv_comm_iff_commutes.mp
      rw [$commOf]
      <;> try assumption
  end)

macro "declare_ungraded_triv_comm_of_root_pair_thms"
    w:ident R:term:arg
    r₁:term:arg r₂:term:arg : command => do
  let commOf := TSyntax.mapIdent₂ r₁ r₂ (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂)
  makeCommands `(section
    theorem $commOf : trivial_commutator_of_root_pair ($w $R).pres_mk ($r₁, $r₂) :=
      ($w $R).trivial_commutator_helper (by unfold $w; simp only; tauto)
    declare_ungraded_triv_expr_thm $w $R $r₁ $r₂
  end)

macro "declare_ungraded_single_expr_thms"
    w:ident R:term:arg
    r₁:term:arg r₂:term:arg r₃:term:arg isNeg:num n:num : command => do
  let innerTerm ←
    match isNeg.getNat, n.getNat with
    | 0, 1 => `(t * u)
    | 1, 1 => `(-(t * u))
    | 1, _ => `(-($n * t * u))
    | _, _ => `($n * t * u)

  let commOf := TSyntax.mapIdent₂ r₁ r₂ (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂)
  let exprAs := TSyntax.mapIdent₃ r₁ r₂ r₃
    (fun s₁ s₂ s₃ => "expr_" ++ s₃ ++ "_as_" ++ s₁ ++ "_" ++ s₂ ++ "_" ++ s₁ ++ "_" ++ s₂)
  let exprAsRev := TSyntax.mapIdent₃ r₁ r₂ r₃
    (fun s₁ s₂ s₃ => "expr_" ++ s₁ ++ "_" ++ s₂ ++ "_as_" ++ s₃ ++ "_" ++ s₂ ++ "_" ++ s₁)
  makeCommands `(section
    theorem $exprAs : ∀ (t u : $R),
        (($w $R).pres_mk {$r₃:term, $innerTerm})
          = ($w $R).pres_mk {$r₁:term, t}
            * ($w $R).pres_mk {$r₂:term, u}
            * ($w $R).pres_mk {$r₁:term, -t}
            * ($w $R).pres_mk {$r₂:term, -u} := by
      intro t u
      have := $commOf t u
      chev_simp [commutatorElement_def, one_mul, mul_one] at this
      symm at this
      exact this

    @[group_reassoc]
    theorem $exprAsRev : ∀ (t u : $R),
        reorder_left(
          ($w $R).pres_mk {$r₁:term, t},
          ($w $R).pres_mk {$r₂:term, u},
          (($w $R).pres_mk {$r₃:term, $innerTerm})
        ) := by
      intro t u
      have := $commOf t u
      chev_simp [commutatorElement_def, one_mul, mul_one] at this
      grw [← this]
  end)

macro "declare_ungraded_single_comm_of_root_pair_thms"
    w:ident R:term:arg
    r₁:term:arg r₂:term:arg r₃:term:arg isNeg:num n:num : command => do
  let innerTerm ←
    match isNeg.getNat with
    | 1 => `(-($n))
    | _ => `($n)

  let commOf := TSyntax.mapIdent₂ r₁ r₂ (fun s₁ s₂ => "comm_of_" ++ s₁ ++ "_" ++ s₂)
  makeCommands `(section
    theorem $commOf : single_commutator_of_root_pair ($w $R).pres_mk ⟨$r₁, $r₂, $r₃, $innerTerm, rfl⟩ :=
      ($w $R).single_commutator_helper ⟨$r₁, $r₂, $r₃, $innerTerm, rfl⟩ (
        by unfold $w; simp only; tauto)
    declare_ungraded_single_expr_thms $w $R $r₁ $r₂ $r₃ $isNeg $n
  end)

end declareThms /- section -/

end PartialChevalleyGroup

/-

LICENSE goes here.

-/

import Steinberg.Defs.GradedPartialChevalleyGroup
import Steinberg.Upstream.PresentedGroup

import Mathlib.GroupTheory.Commutator.Basic

/-!

  File dox go here.

-/

namespace Steinberg

open PositiveRootSystem GradedPartialChevalley GradedChevalleyGenerator GradedPartialChevalleyGroup
open Set

variable {G : Type TG} [Group G]
         {Φ : Type TΦ} [PositiveRootSystem Φ]
         {R : Type TR} [Ring R]

/-- "Degree-reflection" map of `GradedGen`s corresponding to swapping degree `i` with `height ζ - i`. (An involution.) -/
def refl_of_gen (g : GradedChevalleyGenerator Φ R) : GradedChevalleyGenerator Φ R :=
  GradedChevalleyGenerator.mk g.ζ (height g.ζ - g.i) (by ht) g.t

def refl_def (w : GradedPartialChevalleyGroup Φ R) : GradedChevalleyGenerator Φ R → FreeGroup (GradedChevalleyGenerator Φ R) :=
  (FreeGroup.map refl_of_gen) ∘ w.define

theorem lift_of_refl_eq_comp (w : GradedPartialChevalleyGroup Φ R) : FreeGroup.lift (refl_def w) = (FreeGroup.map refl_of_gen).comp (FreeGroup.lift w.define)
  := by
  ext a : 1
  simp_all only [FreeGroup.lift.of, MonoidHom.coe_comp, Function.comp_apply]
  rfl

-- reflecting a present root simply applies refl_of_gen to it
theorem refl_def_eq_refl_gen_of_present (w : GradedPartialChevalleyGroup Φ R)
      (g : GradedChevalleyGenerator Φ R) (h : g.ζ ∈ w.sys.present_roots)
    : refl_def w g = FreeGroup.of (refl_of_gen g) := by
  simp only [refl_def, MonoidHom.coe_comp, Function.comp_apply, FreeGroup.lift.of]
  have : w.define g = FreeGroup.of g := by exact w.h_define_of_present h
  rw [this]
  simp only [FreeGroup.map.of]

/-! ### Generic reflection theorems -/

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_trivial_commutator_of_root_pair (ζ η : Φ)
  (h_ζ : ζ ∈ w.sys.present_roots) (h_η : η ∈ w.sys.present_roots)
    : ∀ r ∈ rels_of_trivial_commutator_of_root_pair R (ζ, η),
      (FreeGroup.lift (refl_def w)) r ∈ rels_of_trivial_commutator_of_root_pair R (ζ, η) := by
  intro r h
  simp only [rels_of_trivial_commutator_of_root_pair, mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, rfl ⟩
  simp only [map_commutatorElement, FreeGroup.lift.of]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk ζ i hi t) h_ζ]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk η j hj u) h_η]
  exists (height ζ - i), (height η - j), (by omega), (by omega), t, u

/-- Degree-reflection preserves the set of single commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_single_commutator_of_root_pair
  (ζ η θ : Φ) (C : ℤ) (h_height : height θ = height ζ + height η)
  (h_ζ : ζ ∈ w.sys.present_roots) (h_η : η ∈ w.sys.present_roots) (h_θ : θ ∈ w.sys.present_roots)
    : ∀ r ∈ rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩,
      (FreeGroup.lift (refl_def w)) r ∈ rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩ := by
  intro r h
  simp only [rels_of_single_commutator_of_root_pair, mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, rfl ⟩
  simp only [map_mul, map_commutatorElement, FreeGroup.lift.of, map_inv]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk ζ i hi t) h_ζ]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk η j hj u) h_η]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk θ (i + j) (by omega) (C * t * u)) h_θ]
  exists (height ζ - i), (height η - j), (by omega), (by omega), t, u
  congr
  simp only
  omega

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_double_commutator_of_root_pair
  (ζ η θ₁ θ₂ : Φ) (C₁ C₂ : ℤ) (h_height₁ : height θ₁ = height ζ + height η) (h_height₂ : height θ₂ = height ζ + 2 * height η)
  (h_ζ : ζ ∈ w.sys.present_roots) (h_η : η ∈ w.sys.present_roots) (h_θ₁ : θ₁ ∈ w.sys.present_roots) (h_θ₂ : θ₂ ∈ w.sys.present_roots)
    : ∀ r ∈ rels_of_double_commutator_of_root_pair R ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩,
      (FreeGroup.lift (refl_def w)) r ∈ rels_of_double_commutator_of_root_pair R ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ := by
  intro r h
  simp only [rels_of_double_commutator_of_root_pair, mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, rfl ⟩
  simp only [mul_inv_rev, map_mul, map_commutatorElement, FreeGroup.lift.of, map_inv]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk ζ i hi t) h_ζ]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk η j hj u) h_η]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk θ₁ (i + j) (by omega) (C₁ * t * u)) h_θ₁]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk θ₂ (i + 2 * j) (by omega) (C₂ * t * u * u)) h_θ₂]
  exists (height ζ - i), (height η - j), (by omega), (by omega), t, u
  simp only [mul_inv_rev]
  congr
  all_goals (ht)

/-- Degree-reflection preserves the set of mixed-degree commutator relations for any root. -/
private theorem refl_deg_of_rels_of_mixed_commutes_of_root (ζ : Φ) (h_ζ : ζ ∈ w.sys.present_roots):
  ∀ r ∈ rels_of_mixed_commutes_of_root R ζ,
    (FreeGroup.lift (refl_def w)) r ∈ rels_of_mixed_commutes_of_root R ζ := by
  intro r h
  simp only [rels_of_mixed_commutes_of_root, mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, rfl ⟩
  simp only [map_commutatorElement, FreeGroup.lift.of]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk ζ i hi t) h_ζ]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk ζ j hj u) h_ζ]
  exists (height ζ - i), (height ζ - j), (by omega), (by omega), t, u

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_lin_of_root (ζ : Φ) (h_ζ : ζ ∈ w.sys.present_roots) :
  ∀ r ∈ rels_of_lin_of_root R ζ,
    (FreeGroup.lift (refl_def w)) r ∈ rels_of_lin_of_root R ζ := by
  intro r h
  simp only [rels_of_lin_of_root, mem_setOf_eq] at h
  rcases h with ⟨ i, hi, t, u, rfl ⟩
  simp only [map_mul, FreeGroup.lift.of, map_inv]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk ζ i hi t) h_ζ]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk ζ i hi u) h_ζ]
  rw [refl_def_eq_refl_gen_of_present w (GradedChevalleyGenerator.mk ζ i hi (t + u)) h_ζ]
  exists (height ζ - i), (by omega), t, u

def refl_valid (w : GradedPartialChevalleyGroup Φ R) :=
  (∀ S ∈ w.lifted_rels_sets, ∀ r ∈ S, w.pres_mk ((FreeGroup.lift (refl_def w)) r) = 1)

theorem reflect_degree_of_rels {w : GradedPartialChevalleyGroup Φ R} (h' : refl_valid w) :
    (FreeGroup.lift (refl_def w)) '' w.all_rels ⊆ Subgroup.normalClosure w.all_rels := by
  nth_rewrite 1 [all_rels]
  intro r h_r
  simp only [sUnion_insert, sUnion_singleton, mem_image, mem_union, mem_sUnion] at h_r
  rcases h_r with ⟨ r, ⟨ h_r, rfl ⟩ ⟩
  rcases h_r with (h_triv | h_sing | h_doub | h_mix | h_lin | h_lift | h_def)
  · apply Subgroup.subset_normalClosure
    simp only [trivial_comm_rels, mem_iUnion, exists_prop, Prod.exists] at h_triv
    rcases h_triv with ⟨ ζ, η, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.lift (refl_def w)) r ∈ w.trivial_comm_rels by
      simp only [all_rels, sUnion_insert]
      tauto
    rw [trivial_comm_rels]
    simp only [mem_iUnion, exists_prop, Prod.exists]
    use ζ, η, h_in_pairs
    exact refl_deg_of_rels_of_trivial_commutator_of_root_pair ζ η (w.sys.h_trivial_valid (ζ, η) h_in_pairs).1 (w.sys.h_trivial_valid (ζ, η) h_in_pairs).2 r h_t_in_rels
  · apply Subgroup.subset_normalClosure
    simp only [single_comm_rels, mem_iUnion, exists_prop, Sigma.exists, PProd.exists] at h_sing
    rcases h_sing with ⟨ ζ, η, θ, C, h_height, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.lift (refl_def w)) r ∈ w.single_comm_rels by
      simp only [all_rels, sUnion_insert]
      tauto
    simp only [single_comm_rels, mem_iUnion, exists_prop, Prod.exists]
    use ⟨ ζ, η, θ, C, h_height ⟩, h_in_pairs
    exact refl_deg_of_rels_of_single_commutator_of_root_pair ζ η θ C h_height
      (w.sys.h_single_valid ⟨ ζ, η, θ, C, h_height ⟩ h_in_pairs).1 (w.sys.h_single_valid ⟨ ζ, η, θ, C, h_height ⟩ h_in_pairs).2.1
      (w.sys.h_single_valid ⟨ ζ, η, θ, C, h_height ⟩ h_in_pairs).2.2
      r h_t_in_rels
  · apply Subgroup.subset_normalClosure
    simp only [double_comm_rels, mem_iUnion, exists_prop, Sigma.exists, PProd.exists] at h_doub
    rcases h_doub with ⟨ ζ, η, θ₁, θ₂, ⟨ C₁, C₂, h_height₁, h_height₂ ⟩ , h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.lift (refl_def w)) r ∈ w.double_comm_rels by
      simp only [all_rels, sUnion_insert]
      tauto
    simp only [double_comm_rels, mem_iUnion, exists_prop, Prod.exists]
    use ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩, h_in_pairs
    exact refl_deg_of_rels_of_double_commutator_of_root_pair ζ η θ₁ θ₂ C₁ C₂ h_height₁ h_height₂
      (w.sys.h_double_valid ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ h_in_pairs).1
      (w.sys.h_double_valid ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ h_in_pairs).2.1
      (w.sys.h_double_valid ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ h_in_pairs).2.2.1
      (w.sys.h_double_valid ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ h_in_pairs).2.2.2
      r h_t_in_rels
  · apply Subgroup.subset_normalClosure
    simp only [mixed_commutes_rels, mem_iUnion, exists_prop, Prod.exists] at h_mix
    rcases h_mix with ⟨ ζ, h_in_present, h_t_in_rels ⟩
    suffices (FreeGroup.lift (refl_def w)) r ∈ w.mixed_commutes_rels by
      simp only [all_rels, sUnion_insert, sUnion_singleton, mem_union, mem_sUnion]
      tauto
    simp only [mixed_commutes_rels, mem_iUnion, exists_prop, Prod.exists]
    use ζ, h_in_present
    exact refl_deg_of_rels_of_mixed_commutes_of_root ζ h_in_present r h_t_in_rels
  · apply Subgroup.subset_normalClosure
    simp only [lin_rels, mem_iUnion, exists_prop, Prod.exists] at h_lin
    rcases h_lin with ⟨ ζ, h_in_present, h_t_in_rels ⟩
    suffices (FreeGroup.lift (refl_def w)) r ∈ w.lin_rels by
      simp only [all_rels, sUnion_insert]
      tauto
    simp only [lin_rels, mem_iUnion, exists_prop, Prod.exists]
    use ζ, h_in_present
    exact refl_deg_of_rels_of_lin_of_root ζ h_in_present r h_t_in_rels
  · apply eq_one_iff_mem_closure.mp
    rcases h_lift with ⟨ T, ⟨ h_T, h_t_T ⟩ ⟩
    exact h' T h_T r h_t_T
  · simp only [def_rels, mem_setOf_eq] at h_def
    rcases h_def with ⟨ S, h_S, h_r ⟩
    simp only [mem_range, SetLike.mem_coe] at h_S
    rcases h_S with ⟨ ζ, h_ζ ⟩
    subst S
    simp only [mem_setOf_eq] at h_r
    rcases h_r with ⟨ i, hi, t, h ⟩
    subst r
    simp only [lift_of_refl_eq_comp, map_mul, map_inv, MonoidHom.coe_comp, Function.comp_apply,
      FreeGroup.lift.of, w.h_define_is_projection, inv_mul_cancel, SetLike.mem_coe, one_mem]

def refl_symm {w : GradedPartialChevalleyGroup Φ R} (h : refl_valid w) : group w →* group w :=
  toPresentedGroup (reflect_degree_of_rels h)

theorem refl_symm_of_pres_mk {w : GradedPartialChevalleyGroup Φ R} {h : refl_valid w} {g : FreeGroup (GradedChevalleyGenerator Φ R)} :
  refl_symm h (w.pres_mk g) = w.pres_mk (FreeGroup.lift (refl_def w) g) := by
  simp only [refl_symm, pres_mk, toPresentedGroup.mk]

section declareThms

open Lean Parser.Tactic
set_option hygiene false

-- macro "declare_refl_def_thm" Φ:ident w:ident R:term:arg r:term:arg : command => do
--   let reflName := r.mapIdent (fun s => "refl_def_of" ++ s)
--   let wDefRw ← `(rwRule| $w:term)
--   let cmds ← Syntax.getArgs <$> `(
--     section
--     @[group_reassoc]
--     theorem $reflName (g : GradedChevalleyGenerator $Φ $R) (h : g.ζ = $r) :
--           ($w $R).pres_mk (refl_def $w g) = ($w $R).pres_mk (FreeGroup.of (refl_of_gen g)) := by
--       congr
--       apply refl_def_of_present
--       rw [h]
--       simp only [$wDefRw, present_roots]
--       tauto
--     end
--   )
--   return ⟨mkNullNode cmds⟩

end declareThms

end Steinberg

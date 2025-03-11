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

namespace ReflDeg

open PositiveRootSystem GradedPartialChevalley GradedChevalleyGenerator GradedPartialChevalleyGroup
open Set

variable {G : Type TG} [Group G]
         {Φ : Type TΦ} [PositiveRootSystem Φ]
         {R : Type TR} [Ring R]

/-- "Degree-reflection" map of `GradedGen`s corresponding to swapping degree `i` with `height ζ - i`. (An involution.) -/
def refl_deg_of_gen (g : GradedChevalleyGenerator Φ R) : GradedChevalleyGenerator Φ R :=
  GradedChevalleyGenerator.mk g.ζ (height g.ζ - g.i) (by omega) g.t

/-! ### Generic reflection theorems -/

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_trivial_commutator_of_root_pair (ζ η : Φ)
    : ∀ r ∈ rels_of_trivial_commutator_of_root_pair R (ζ, η),
      FreeGroup.map refl_deg_of_gen r ∈ rels_of_trivial_commutator_of_root_pair R (ζ, η) := by
  intro r h
  simp only [rels_of_trivial_commutator_of_root_pair, mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, rfl ⟩
  simp only [map_commutatorElement, refl_deg_of_gen]
  exists (height ζ - i), (height η - j), (by omega), (by omega), t, u

/-- Degree-reflection preserves the set of single commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_single_commutator_of_root_pair
  (ζ η θ : Φ) (C : R) (h_height : height θ = height ζ + height η)
    : ∀ r ∈ rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩,
      FreeGroup.map refl_deg_of_gen r ∈ rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩ := by
  intro r h
  simp only [rels_of_single_commutator_of_root_pair, mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, rfl ⟩
  simp only [map_mul, map_commutatorElement, map_inv, refl_deg_of_gen]
  exists (height ζ - i), (height η - j), (by omega), (by omega), t, u
  congr
  simp only
  omega

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_double_commutator_of_root_pair
  (ζ η θ₁ θ₂ : Φ) (C₁ C₂ : R) (h_height₁ : height θ₁ = height ζ + height η) (h_height₂ : height θ₂ = height ζ + 2 * height η)
    : ∀ r ∈ rels_of_double_commutator_of_root_pair R ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩,
      FreeGroup.map refl_deg_of_gen r ∈ rels_of_double_commutator_of_root_pair R ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩ := by
  intro r h
  simp only [rels_of_double_commutator_of_root_pair, mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, rfl ⟩
  simp only [map_mul, map_commutatorElement, map_inv, refl_deg_of_gen]
  exists (height ζ - i), (height η - j), (by omega), (by omega), t, u
  congr
  simp only
  omega
  simp only
  omega

/-- Degree-reflection preserves the set of mixed-degree commutator relations for any root. -/
private theorem refl_deg_of_rels_of_mixed_commutes_of_root (ζ : Φ) :
  ∀ r ∈ rels_of_mixed_commutes_of_root R ζ,
    FreeGroup.map refl_deg_of_gen r ∈ rels_of_mixed_commutes_of_root R ζ := by
  intro r h
  simp only [rels_of_mixed_commutes_of_root, mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, rfl ⟩
  simp only [map_commutatorElement, refl_deg_of_gen]
  exists (height ζ - i), (height ζ - j), (by omega), (by omega), t, u

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_lin_of_root (ζ : Φ) :
  ∀ r ∈ rels_of_lin_of_root R ζ,
    FreeGroup.map refl_deg_of_gen r ∈ rels_of_lin_of_root R ζ := by
  intro r h
  simp only [rels_of_lin_of_root, mem_setOf_eq] at h
  rcases h with ⟨ i, hi, t, u, rfl ⟩
  exists (height ζ - i), (by omega), t, u

/-- Map a generator to its reflected image in the presented group (used to define the symmetry below). -/
private def pres_of_refl_deg_of_gen (w : GradedPartialChevalleyGroup Φ R) (g : GradedChevalleyGenerator Φ R) : w.group :=
  w.pres_mk (FreeGroup.of (refl_deg_of_gen g))

def refl_valid (w : GradedPartialChevalleyGroup Φ R) :=
  (∀ S ∈ w.lifted_rels_sets, ∀ r ∈ S, w.pres_mk (FreeGroup.map refl_deg_of_gen r) = 1) ∧
  (∀ S ∈ w.def_rels_sets, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S)

theorem reflect_degree_of_rels {w : GradedPartialChevalleyGroup Φ R} (h' : refl_valid w) :
    FreeGroup.lift (FreeGroup.of ∘ refl_deg_of_gen) '' w.all_rels ⊆ Subgroup.normalClosure w.all_rels := by
  nth_rewrite 1 [all_rels]
  intro r h_r
  simp only [sUnion_insert, sUnion_singleton, mem_image, mem_union, mem_sUnion] at h_r
  rcases h_r with ⟨ t, ⟨ h_t, rfl ⟩ ⟩
  rw [lift_of_is_map]
  have all_rels_to_normal_closure_all_rels := @Subgroup.subset_normalClosure _ _ (w.all_rels)
  rcases h_t with (h_triv | h_sing | h_doub | h_mix | h_lin | h_non | h_def)
  · apply all_rels_to_normal_closure_all_rels
    simp only [trivial_comm_rels, sUnion_image, mem_iUnion, exists_prop, Prod.exists] at h_triv
    rcases h_triv with ⟨ ζ, η, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.trivial_comm_rels by
      simp only [all_rels, sUnion_insert, sUnion_singleton, mem_union, mem_sUnion]
      simp_all only [true_or]
    rw [trivial_comm_rels]
    simp only [sUnion_image, mem_iUnion, exists_prop, Prod.exists]
    use ζ, η, h_in_pairs
    exact refl_deg_of_rels_of_trivial_commutator_of_root_pair ζ η t h_t_in_rels
  · apply all_rels_to_normal_closure_all_rels
    simp only [single_comm_rels, sUnion_image, mem_iUnion, exists_prop, Sigma.exists, PProd.exists] at h_sing
    rcases h_sing with ⟨ ζ, η, θ, C, h_height, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.single_comm_rels by
      simp only [all_rels, sUnion_insert, sUnion_singleton, mem_union, mem_sUnion]
      simp_all only [true_or, or_true]
    simp only [single_comm_rels, sUnion_image, mem_iUnion, exists_prop, Prod.exists]
    use ⟨ ζ, η, θ, C, h_height ⟩, h_in_pairs
    exact refl_deg_of_rels_of_single_commutator_of_root_pair ζ η θ C h_height t h_t_in_rels
  · apply all_rels_to_normal_closure_all_rels
    simp only [double_comm_rels, sUnion_image, mem_iUnion, exists_prop, Sigma.exists, PProd.exists] at h_doub
    rcases h_doub with ⟨ ζ, η, θ₁, θ₂, ⟨ C₁, C₂, h_height₁, h_height₂ ⟩ , h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.double_comm_rels by
      simp only [all_rels, sUnion_insert, sUnion_singleton, mem_union, mem_sUnion]
      simp_all only [true_or, or_true]
    simp only [double_comm_rels, sUnion_image, mem_iUnion, exists_prop, Prod.exists]
    use ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h_height₁, h_height₂ ⟩, h_in_pairs
    exact refl_deg_of_rels_of_double_commutator_of_root_pair ζ η θ₁ θ₂ C₁ C₂ h_height₁ h_height₂ t h_t_in_rels
  · apply all_rels_to_normal_closure_all_rels
    simp only [mixed_commutes_rels, sUnion_image, mem_iUnion, exists_prop, Prod.exists] at h_mix
    rcases h_mix with ⟨ ζ, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.mixed_commutes_rels by
      simp only [all_rels, sUnion_insert, sUnion_singleton, mem_union, mem_sUnion]
      simp_all only [true_or, or_true]
    simp only [mixed_commutes_rels, sUnion_image, mem_iUnion, exists_prop, Prod.exists]
    use ζ, h_in_pairs
    exact refl_deg_of_rels_of_mixed_commutes_of_root ζ t h_t_in_rels
  · apply all_rels_to_normal_closure_all_rels
    simp only [lin_rels, sUnion_image, mem_iUnion, exists_prop, Prod.exists] at h_lin
    rcases h_lin with ⟨ ζ, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.lin_rels by
      simp only [all_rels, sUnion_insert, sUnion_singleton, mem_union, mem_sUnion]
      simp_all only [true_or, or_true]
    simp only [lin_rels, sUnion_image, mem_iUnion, exists_prop, Prod.exists]
    use ζ, h_in_pairs
    exact refl_deg_of_rels_of_lin_of_root ζ t h_t_in_rels
  · apply eq_one_iff_mem_closure.mp
    rcases h_non with ⟨ T, ⟨ h_T, h_t_T ⟩ ⟩
    exact h'.1 T h_T t h_t_T
  · apply all_rels_to_normal_closure_all_rels
    rcases h_def with ⟨ T, ⟨ h_T, h_t_T ⟩ ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ ⋃₀ w.def_rels_sets by
      simp only [all_rels, sUnion_insert, sUnion_singleton, mem_union, mem_sUnion, true_or]
      simp_all only [mem_sUnion, or_true]
    use T, h_T, h'.2 T h_T t h_t_T

def refl_symm {w : GradedPartialChevalleyGroup Φ R} (h : refl_valid w) : group w →* group w :=
  toPresentedGroup (reflect_degree_of_rels h)

/- Calculates the image of a generator in the presented group by the degree-reflection homomorphism. -/
theorem refl_im (ζ : Φ) (i : ℕ) (hi : i ≤ height ζ) (t : R) {w : GradedPartialChevalleyGroup Φ R} (h : refl_valid w) :
  refl_symm h (pres_mk w (free_mk ζ i hi t)) =
    (pres_mk w (free_mk ζ (height ζ - i) (by omega) t)) := by
  simp only [refl_symm, pres_mk, free_mk]
  rw [← PresentedGroup.of, toPresentedGroup.of]
  simp only [FreeGroup.lift.of, Function.comp_apply, refl_deg_of_gen]

end ReflDeg

end Steinberg


import Steinberg.Defs.Root
import Steinberg.Defs.Chevalley
import Steinberg.Defs.WeakChevalley

import Steinberg.Upstream.PresentedGroup

namespace Steinberg

namespace ReflDeg

open PosRootSys
open WeakChevalley

variable {G : Type TG} [Group G]
         {Φ : Type TΦ} [PosRootSys Φ]
         {R : Type TR} [Ring R]

/-- "Degree-reflection" map of `GradedGen`s corresponding to swapping degree `i` with `height ζ - i`. (An involution.) -/
def refl_deg_of_gen (g : GradedGen Φ R) : GradedGen Φ R :=
  GradedGen.mk g.ζ (height g.ζ - g.i) (by omega) g.t

/-! ### Generic reflection theorems -/

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_trivial_commutator_of_root_pair (ζ η : Φ) :
  ∀ r ∈ rels_of_trivial_commutator_of_root_pair R (ζ, η), FreeGroup.map refl_deg_of_gen r ∈ rels_of_trivial_commutator_of_root_pair R (ζ, η) := by
  intro r h
  simp only [rels_of_trivial_commutator_of_root_pair, Set.mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, h' ⟩
  simp only [← h', map_commutatorElement, refl_deg_of_gen, rels_of_trivial_commutator_of_root_pair]
  exists (PosRootSys.height ζ - i), (PosRootSys.height η - j), (by omega), (by omega), t, u

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_single_commutator_of_root_pair (ζ η θ : Φ) (C : R) (h_height : height θ = height ζ + height η) :
  ∀ r ∈ rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩,
    FreeGroup.map refl_deg_of_gen r ∈ rels_of_single_commutator_of_root_pair R ⟨ ζ, η, θ, C, h_height ⟩ := by
  intro r h
  simp only [rels_of_single_commutator_of_root_pair, Set.mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, h' ⟩
  simp only [← h', map_mul, map_commutatorElement, map_inv, refl_deg_of_gen, rels_of_single_commutator_of_root_pair]
  exists (PosRootSys.height ζ - i), (PosRootSys.height η - j), (by omega), (by omega), t, u
  congr
  simp only
  omega

private theorem refl_deg_of_rels_of_double_commutator_of_root_pair (ζ η θ₁ θ₂ : Φ) (C₁ C₂ : R)
  (h₁_height : height θ₁ = height ζ + height η) (h₂_height : height θ₂ = height ζ + 2 * height η) :
  ∀ r ∈ rels_of_double_commutator_of_root_pair R ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h₁_height, h₂_height⟩,
    FreeGroup.map refl_deg_of_gen r ∈ rels_of_double_commutator_of_root_pair R ⟨ ζ, η, θ₁, θ₂, C₁, C₂, h₁_height, h₂_height⟩ :=
    by sorry

/-- Degree-reflection preserves the set of mixed-degree commutator relations for any root. -/
private theorem refl_deg_of_rels_of_mixed_commutes_of_root (ζ : Φ) :
  ∀ r ∈ rels_of_mixed_commutes_of_root R ζ,
    FreeGroup.map refl_deg_of_gen r ∈ rels_of_mixed_commutes_of_root R ζ := by
  intro r h
  simp only [rels_of_mixed_commutes_of_root, Set.mem_setOf_eq] at h
  rcases h with ⟨ i, j, hi, hj, t, u, h' ⟩
  simp only [← h', map_commutatorElement, refl_deg_of_gen, rels_of_mixed_commutes_of_root]
  exists (PosRootSys.height ζ - i), (PosRootSys.height ζ - j), (by omega), (by omega), t, u

/-- Degree-reflection preserves the set of trivial commutator relations for any root pair. -/
private theorem refl_deg_of_rels_of_lin_of_root (ζ : Φ) :
  ∀ r ∈ rels_of_lin_of_root R ζ,
    FreeGroup.map refl_deg_of_gen r ∈ rels_of_lin_of_root R ζ := by
  intro r h
  simp only [rels_of_lin_of_root, Set.mem_setOf_eq] at h
  rcases h with ⟨ i, hi, t, u, h' ⟩
  simp only [← h', rels_of_lin_of_root]
  exists (PosRootSys.height ζ - i), (by omega), t, u

/-- Map a generator to its reflected image in the presented group (used to define the symmetry below). -/
private def pres_of_refl_deg_of_gen (R : Type TR) [Ring R] (w : WeakChevalley Φ R) (g : GradedGen Φ R) : WeakChevalley.group w :=
  WeakChevalley.pres_mk w (GradedGen.free_mk (refl_deg_of_gen g))

def refl_valid {w : WeakChevalley Φ R} :=
  (∀ S ∈ w.nonhomog_rels_sets, ∀r ∈ S, w.pres_mk (FreeGroup.map refl_deg_of_gen r) = 1) ∧
  (∀ S ∈ w.def_rels_sets, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S)

theorem reflect_degree_of_rels {w : WeakChevalley Φ R} (h' : @refl_valid Φ _ R _ w) :
  FreeGroup.lift (FreeGroup.of ∘ refl_deg_of_gen) '' (WeakChevalley.all_rels w) ⊆ Subgroup.normalClosure (WeakChevalley.all_rels w) := by
  nth_rewrite 1 [all_rels]
  rw [Set.subset_def]
  intro r h_r
  simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_image, Set.mem_union, Set.mem_sUnion] at h_r
  rcases h_r with ⟨ t, ⟨ h_t, h_t_r ⟩ ⟩
  rcases h_t_r
  rw [lift_of_is_map]
  have all_rels_to_normal_closure_all_rels := @Subgroup.subset_normalClosure _ _ (w.all_rels)
  rw [Set.subset_def] at all_rels_to_normal_closure_all_rels
  rcases h_t with h_triv | h_sing | h_mix | h_lin | h_non | h_def
  · apply all_rels_to_normal_closure_all_rels
    rw [trivial_comm_rels] at h_triv
    simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop, Prod.exists] at h_triv
    rcases h_triv with ⟨ ζ, η, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.trivial_comm_rels by
      rw [all_rels]
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      simp_all only [true_or]
    rw [trivial_comm_rels]
    simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop, Prod.exists]
    use ζ, η, h_in_pairs
    exact @refl_deg_of_rels_of_trivial_commutator_of_root_pair Φ _ R _ ζ η t h_t_in_rels
  · apply all_rels_to_normal_closure_all_rels
    rw [single_comm_rels] at h_sing
    simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop, Sigma.exists, PProd.exists] at h_sing
    rcases h_sing with ⟨ ζ, η, θ, C, h_height, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.single_comm_rels by
      rw [all_rels]
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      simp_all only [true_or, or_true]
    rw [single_comm_rels]
    simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop, Prod.exists]
    use ⟨ ζ, η, θ, C, h_height ⟩, h_in_pairs
    exact @refl_deg_of_rels_of_single_commutator_of_root_pair Φ _ R _ ζ η θ C h_height t h_t_in_rels
  · apply all_rels_to_normal_closure_all_rels
    rw [mixed_commutes_rels] at h_mix
    simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop, Prod.exists] at h_mix
    rcases h_mix with ⟨ ζ, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.mixed_commutes_rels by
      rw [all_rels]
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      simp_all only [true_or, or_true]
    rw [mixed_commutes_rels]
    simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop, Prod.exists]
    use ζ, h_in_pairs
    exact @refl_deg_of_rels_of_mixed_commutes_of_root Φ _ R _ ζ t h_t_in_rels
  · apply all_rels_to_normal_closure_all_rels
    rw [lin_rels] at h_lin
    simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop, Prod.exists] at h_lin
    rcases h_lin with ⟨ ζ, h_in_pairs, h_t_in_rels ⟩
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ w.lin_rels by
      rw [all_rels]
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion]
      simp_all only [true_or, or_true]
    rw [lin_rels]
    simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop, Prod.exists]
    use ζ, h_in_pairs
    exact @refl_deg_of_rels_of_lin_of_root Φ _ R _ ζ t h_t_in_rels
  · apply eq_one_iff_mem_closure.mp
    rcases h_non with ⟨ T, ⟨ h_T, h_t_T ⟩ ⟩
    rw [refl_valid] at h'
    exact h'.1 T h_T t h_t_T
  · apply all_rels_to_normal_closure_all_rels
    rcases h_def with ⟨ T, ⟨ h_T, h_t_T ⟩ ⟩
    rw [refl_valid] at h'
    suffices (FreeGroup.map refl_deg_of_gen) t ∈ ⋃₀ w.def_rels_sets by
      rw [all_rels]
      simp only [Set.sUnion_insert, Set.sUnion_singleton, Set.mem_union, Set.mem_sUnion, true_or]
      simp_all only [Set.mem_sUnion, or_true]
    use T, h_T, h'.2 T h_T t h_t_T

def refl_symm {w : WeakChevalley Φ R} (h : @refl_valid Φ _ R _ w) : WeakChevalley.group w →* WeakChevalley.group w :=
  @toPresentedGroup _ _ _ _ (FreeGroup.of ∘ refl_deg_of_gen) (reflect_degree_of_rels h)

/- Calculates the image of a generator in the presented group by the degree-reflection homomorphism. -/
theorem refl_im (ζ : Φ) (i : ℕ) (hi : i ≤ PosRootSys.height ζ) (t : R) (w : WeakChevalley Φ R) (h :  @refl_valid Φ _ R _ w) :
  refl_symm h (WeakChevalley.pres_mk w (GradedGen.free_mk_mk ζ i hi t)) =
    (WeakChevalley.pres_mk w (GradedGen.free_mk_mk ζ (PosRootSys.height ζ - i) (by omega) t)) := by
  simp only [refl_symm, pres_mk, GradedGen.free_mk_mk]
  rw [← PresentedGroup.of, toPresentedGroup.of]
  simp only [FreeGroup.lift.of, Function.comp_apply]
  rw [refl_deg_of_gen]

end ReflDeg

end Steinberg

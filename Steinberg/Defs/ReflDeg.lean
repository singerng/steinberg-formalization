
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
private theorem refl_deg_of_rels_of_single_commutator_of_root_pair (ζ η : Φ) (C : R) (h_height : height θ = height ζ + height η) :
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

-- theorem helper {SS : Set (Set (FreeGroupOnGradedGens Φ R))} {f : FreeGroupOnGradedGens Φ R → FreeGroupOnGradedGens Φ R}
--   : (∀ S ∈ SS, f '' S ⊆ S) → f '' (⋃₀ SS) ⊆ ⋃₀ SS := by
--   intro h
--   rw [Set.image_sUnion]
--   apply Set.sUnion_subset
--   intro S'
--   simp only [Set.mem_image]
--   intro h
--   rcases h with ⟨ x, ⟨ h1, h2 ⟩ ⟩
--   rw [← h2]
--   have this1 : f '' x ⊆ x := by exact h x h1
--   have this2 : x ⊆ ⋃₀ SS := by exact Set.subset_sUnion_of_mem h1
--   exact Set.Subset.trans this1 this2

-- slightly ugly...
-- private theorem reflect_degree_of_weak_rels' :
--   FreeGroup.map refl_deg_of_gen '' (WeakChevalley.all_rels w) ⊆ (WeakChevalley.all_rels w) := by

--   sorry
  -- rw [all_rels]
  -- apply helper
  -- intro S h_S
  -- simp at h_S
  -- rcases h_S with h_triv | h_sing | h_mixed | h_lin | h_nonhomog | h_lin
  -- · rw [h_triv]
  --   rw [trivial_comm_rels]
  --   apply helper
  --   intro S h_S
  --   simp at h_S
  --   rcases h_S with ⟨ ζ, η, ⟨ h1, h2 ⟩ ⟩
  --   rw [← h2]
  --   rw [Set.subset_def]
  --   intro x h_x
  --   exact @refl_deg_of_rels_of_trivial_commutator_of_root_pair Φ _ R _ ζ η

-- theorem reflect_degree_of_rels :
--   FreeGroup.lift (FreeGroup.of ∘ (refl_deg_of_gen Φ R)) '' (WeakChevalley.all_rels w) ⊆ Subgroup.normalClosure (WeakChevalley.all_rels w) := by
--   (
--     rw [lift.hom2]
--     exact Set.Subset.trans reflect_degree_of_weak_rels' Subgroup.subset_normalClosure
--   )

def refl_symm {w : WeakChevalley Φ R} : WeakChevalley.group w →* WeakChevalley.group w :=
  @toPresentedGroup _ _ _ _ (FreeGroup.of ∘ refl_deg_of_gen) (by sorry)

/- Calculates the image of a generator in the presented group by the degree-reflection homomorphism. -/
theorem refl_im (ζ : Φ) (i : ℕ) (hi : i ≤ PosRootSys.height ζ) (t : R) (w : WeakChevalley Φ R) :
  refl_symm (WeakChevalley.pres_mk w (GradedGen.free_mk_mk ζ i hi t)) =
    (WeakChevalley.pres_mk w (GradedGen.free_mk_mk ζ (PosRootSys.height ζ - i) (by omega) t)) := by
  simp only [refl_symm, pres_mk, GradedGen.free_mk_mk]
  rw [← PresentedGroup.of, toPresentedGroup.of]
  simp only [FreeGroup.lift.of, Function.comp_apply]
  rw [refl_deg_of_gen]

end ReflDeg

end Steinberg

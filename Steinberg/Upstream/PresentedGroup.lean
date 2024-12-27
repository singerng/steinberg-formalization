import Mathlib.GroupTheory.PresentedGroup

import Steinberg.Upstream.FreeGroup

theorem eq_one_iff_mem_closure {α : Type u} {rels : Set (FreeGroup α)} {x : FreeGroup α} :
  PresentedGroup.mk rels x = 1 ↔ x ∈ Subgroup.normalClosure rels := by
  nth_rewrite 2 [← one_mul x, ← inv_one]
  apply Iff.trans _ (@QuotientGroup.eq _ _ (Subgroup.normalClosure rels) 1 x)
  simp only [QuotientGroup.mk_one, PresentedGroup.mk, MonoidHom.coe_mk, OneHom.coe_mk]
  use Eq.symm, Eq.symm

theorem eq_one_of_mem_rels {α : Type u} {rels : Set (FreeGroup α)} {x : FreeGroup α} :
  x ∈ rels → PresentedGroup.mk rels x = 1 := by
  intro h
  apply eq_one_iff_mem_closure.mpr
  exact Subgroup.subset_normalClosure h

private theorem helper {α β : Type u} {S : Set (FreeGroup α)} {T : Set (FreeGroup β)} {f : α → FreeGroup β}
  (h : FreeGroup.lift f '' S ⊆ Subgroup.normalClosure T)
  : ∀ r ∈ S, (FreeGroup.lift ((PresentedGroup.mk T) ∘ f)) r = 1 := by
  intro r h_r
  rw [lift.hom]
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  apply eq_one_iff_mem_closure.mpr
  rw [Set.subset_def] at h
  simp only [Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at h
  exact h r h_r

def toPresentedGroup {α β : Type u} {S : Set (FreeGroup α)} {T : Set (FreeGroup β)} {f : α → FreeGroup β}
  (h : FreeGroup.lift f '' S ⊆ Subgroup.normalClosure T) :=
  @PresentedGroup.toGroup α (PresentedGroup T) _ (PresentedGroup.mk T ∘ f) S (helper h)

theorem toPresentedGroup.of {α β : Type u} {S : Set (FreeGroup α)} {T : Set (FreeGroup β)} {f : α → FreeGroup β}
  (h : FreeGroup.lift f '' S ⊆ Subgroup.normalClosure T) (x : α) :
  (toPresentedGroup h) (PresentedGroup.of x) = PresentedGroup.mk T (f x) := by
  rw [toPresentedGroup, PresentedGroup.toGroup.of]
  simp only [Function.comp_apply]

theorem toPresentedGroup.mk {α β : Type u} {S : Set (FreeGroup α)} {T : Set (FreeGroup β)} {f : α → FreeGroup β}
  (h : FreeGroup.lift f '' S ⊆ Subgroup.normalClosure T) :
  (toPresentedGroup h).comp (PresentedGroup.mk S) = (PresentedGroup.mk T).comp (FreeGroup.lift f) := by
  ext a
  simp only [MonoidHom.coe_comp, Function.comp_apply, FreeGroup.lift.of]
  rw [← PresentedGroup.of]
  exact toPresentedGroup.of h a

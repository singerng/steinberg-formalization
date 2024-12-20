import Mathlib.GroupTheory.PresentedGroup

theorem eq_one_of_mem_rels {α : Type u} {rels : Set (FreeGroup α)}
    {x : FreeGroup α} : x ∈ rels → PresentedGroup.mk rels x = 1 := by
  intro h_x
  symm
  apply QuotientGroup.eq.mpr
  rw [inv_one, one_mul]
  exact Subgroup.subset_normalClosure h_x

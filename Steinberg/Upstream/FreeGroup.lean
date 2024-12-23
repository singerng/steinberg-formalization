import Mathlib.GroupTheory.FreeGroup.Basic

theorem lift.hom (α β G : Type u) [Group G] (f : α → FreeGroup β) (g : FreeGroup β →* G) :
  FreeGroup.lift (g ∘ f) = g.comp (FreeGroup.lift f) := by
  ext a
  simp

theorem lift_of_is_map (α β : Type u) (f : α → β) :
  FreeGroup.lift (FreeGroup.of ∘ f) = FreeGroup.map f := by
  ext a -- only have to prove for generators!
  simp only [FreeGroup.lift.of, Function.comp_apply, FreeGroup.map.of]

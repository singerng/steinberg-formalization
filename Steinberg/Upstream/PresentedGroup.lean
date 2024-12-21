import Mathlib.GroupTheory.PresentedGroup

theorem eq_one_of_mem_rels {α : Type u} {rels : Set (FreeGroup α)}
    {x : FreeGroup α} : x ∈ rels → PresentedGroup.mk rels x = 1 := by
  intro h_x
  symm
  apply QuotientGroup.eq.mpr
  rw [inv_one, one_mul]
  exact Subgroup.subset_normalClosure h_x

theorem lift.hom (α G : Type) [Group G] (ξ : FreeGroup α →* G) (r : FreeGroup α) :
  (FreeGroup.lift (ξ ∘ FreeGroup.of)) r = ξ r := by
  have : (ξ ∘ FreeGroup.of) = FreeGroup.lift.symm ξ := by
    ext s
    exact FreeGroup.lift_symm_apply ξ s
  rw [this]
  simp only [Equiv.apply_symm_apply, Function.comp_apply]

theorem lift.gens (α β : Type) (T : Set (FreeGroup β)) (f : α → β) (r : FreeGroup α):
  (FreeGroup.lift (PresentedGroup.of ∘ f)) r = ((PresentedGroup.mk T) ∘ (FreeGroup.map f)) r := by
  have : PresentedGroup.of = (PresentedGroup.mk T) ∘ FreeGroup.of := by
    ext s
    simp only [PresentedGroup.of]
    rfl
  rw [this]
  generalize PresentedGroup.mk T = φ
  have : (⇑φ ∘ FreeGroup.of) ∘ f = ⇑φ ∘ (FreeGroup.of ∘ f) := rfl
  rw [this]
  have : ⇑φ ∘ (FreeGroup.of ∘ f) = ⇑φ ∘ (FreeGroup.map f ∘ FreeGroup.of) := rfl
  rw [this]
  generalize FreeGroup.map f = ψ
  have : ⇑φ ∘ ⇑ψ ∘ FreeGroup.of = (⇑φ ∘ ⇑ψ) ∘ FreeGroup.of := rfl
  rw [this]
  generalize h : φ.comp ψ = ξ
  have iddd : (⇑φ ∘ ⇑ψ) = ξ := by subst h; simp_all only [MonoidHom.coe_comp]
  simp_all
  have : φ (ψ r) = (φ ∘ ψ) r := by rfl
  rw [this]
  rw [lift.hom α (PresentedGroup T) ξ r]
  rw [iddd]

theorem lift.homm {α β : Type} (T : Set (FreeGroup β)) (f : α → FreeGroup β) (r : FreeGroup α):
  (FreeGroup.lift ((PresentedGroup.mk T) ∘ f)) r = FreeGroup.lift ((PresentedGroup.mk T) ∘ f) r := by
  have : PresentedGroup.of = (PresentedGroup.mk T) ∘ FreeGroup.of := by
    ext s
    simp only [PresentedGroup.of]
    rfl
  rw [this]
  generalize PresentedGroup.mk T = φ
  have : (⇑φ ∘ FreeGroup.of) ∘ f = ⇑φ ∘ (FreeGroup.of ∘ f) := rfl
  rw [this]
  have : ⇑φ ∘ (FreeGroup.of ∘ f) = ⇑φ ∘ (FreeGroup.map f ∘ FreeGroup.of) := rfl
  rw [this]
  generalize FreeGroup.map f = ψ
  have : ⇑φ ∘ ⇑ψ ∘ FreeGroup.of = (⇑φ ∘ ⇑ψ) ∘ FreeGroup.of := rfl
  rw [this]
  generalize h : φ.comp ψ = ξ
  have iddd : (⇑φ ∘ ⇑ψ) = ξ := by subst h; simp_all only [MonoidHom.coe_comp]
  simp_all
  have : φ (ψ r) = (φ ∘ ψ) r := by rfl
  rw [this]
  rw [lift.hom α (PresentedGroup T) ξ r]
  rw [iddd]

theorem lift.gens2 (α β : Type) (T : Set (FreeGroup β)) (f : α → β) (r : FreeGroup α):
  (FreeGroup.lift (PresentedGroup.of ∘ f)) r = ((PresentedGroup.mk T) ∘ (FreeGroup.map f)) r := by
  have : PresentedGroup.of ∘ f = (PresentedGroup.mk T) ∘ FreeGroup.of ∘ f := by sorry
  rw [this]
  let x := lifttttttttt T (FreeGroup.of ∘ f) r
  rw [x]
  simp_all
  generalize PresentedGroup.mk T = φ
  have : ⇑φ ∘ (FreeGroup.of ∘ f) = ⇑φ ∘ (FreeGroup.map f ∘ FreeGroup.of) := rfl
  rw [this]
  generalize FreeGroup.map f = ψ
  have : ⇑φ ∘ ⇑ψ ∘ FreeGroup.of = (⇑φ ∘ ⇑ψ) ∘ FreeGroup.of := rfl
  rw [this]
  generalize h : φ.comp ψ = ξ



  -- rw [lift.hom]





  -- generalize FreeGroup.map f = ψ

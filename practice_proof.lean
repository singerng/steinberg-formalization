import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Set.Defs

-- ∀ s ∈ S, s ∈ F(A)
-- ∀ t ∈ T, t ∈ F(B)
-- r ∈ S

-- PresentedGroup.mk T (FreeGroup.map f r) is the equivalence class of
-- (FreeGroup.map f r) in ⟨B | T⟩.

-- ((@PresentedGroup.of _ T) ∘ f) maps a : A to the equivalence class of f a
-- in ⟨B | T⟩. This map is lifted to the group homomorphism from F(A) to ⟨B | T⟩,
-- and applied to r.

-- ((@PresentedGroup.of _ T) ∘ f) = F ≃ λ a : A. PresentedGroup.mk T (FreeGroup.of (f a))
-- Let r be a₁a₂...aₙ for aᵢ ∈ A ∪ A⁻¹
-- FreeGroup.Lift F r ≃ F(a₁)F(a₂)...F(aₙ), applying inverses appropriately
-- when aᵢ ∈ A

-- CLAIM: given a group ⟨B | T⟩, r ∈ F(A), and a generator map f : A → B,
-- (mapping generators in r through f; reducing; taking equivalence class) is the same as
-- (taking the equivalence class of generators in r through f; reducing)

theorem out_of_fg_elem {α : Type*} (r : FreeGroup α) : ∃ L : List (α × Bool), r = FreeGroup.mk L := by
  rcases r with ⟨L⟩
  use L
  rfl

theorem need_to_prove (a b : Type) (S : Set (FreeGroup a)) (T : Set (FreeGroup b)) (f : a → b) (r : S):
  (PresentedGroup.mk T (FreeGroup.map f r) = (FreeGroup.lift ((@PresentedGroup.of _ T) ∘ f)) r) := by
  have ⟨rL, rEqL⟩ := @out_of_fg_elem a r; simp [rEqL]
  generalize rL = rL
  induction' rL with hd tl tl_ih
  . simp only [List.map_nil, List.prod_nil]; trivial
  . simp [List.prod_cons, ← tl_ih]
    cases' hd.2; all_goals simp; exact rfl

theorem need_to_prove2 (a b : Type) (S : Set (FreeGroup a)) (T : Set (FreeGroup b)) (f : a → b) (r : S):
  (PresentedGroup.mk T (FreeGroup.map f r) = (FreeGroup.lift ((@PresentedGroup.of _ T) ∘ f)) r) := by
  rcases r with ⟨r, ppty⟩
  induction' r with r r rHyp r₁ r₂ r₁Hyp r₂Hyp
  . exact rfl
  . exact rfl
  . exact rfl
  .
    -- can probably be proven by induction
    sorry

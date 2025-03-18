import Steinberg.B3Large.Defs

open Steinberg B3Large GradedPartialChevalley PartialChevalley ChevalleyGenerator B3LargePosRoot

variable {F : Type TF} [Field F]

-- Instantiate macros for ungraded case

macro "declare_B3Large_ungraded_triv_expr_thm" F:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_expr_thm weakB3Large $F 0 $r₁ $r₂)

macro "declare_B3Large_ungraded_triv_comm_of_root_pair_thms" F:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_comm_of_root_pair_thms weakB3Large $F 0 $r₁ $r₂)

macro "declare_B3Large_ungraded_single_expr_thms" F:term:arg r₁:term:arg r₂:term:arg r₃:term:arg n:num : command =>
  `(command| declare_single_expr_thms weakB3Large $F 0 $r₁ $r₂ $r₃ $n)

macro "declare_B3Large_ungraded_single_comm_of_root_pair_thms" F:term:arg r₁:term:arg r₂:term:arg r₃:term:arg n:num : command =>
  `(command| declare_single_comm_of_root_pair_thms weakB3Large $F 0 $r₁ $r₂ $r₃ $n)

-- Declare relations

declare_B3Large_ungraded_triv_expr_thm F αβ2ψ α2β2ψ

theorem valid_of_hom_lifted (F : Type TF) [Field F] :
  ∀ S ∈ hom_lifted_sets F, ∃ r : FreeGroup (ChevalleyGenerator B3LargePosRoot F), S = hom_lift_set r ∧ (fullB3Large F).pres_mk r = 1 := by
  intro S h_S
  simp only [hom_lifted_sets] at h_S
  simp only [Set.mem_image] at h_S
  rcases h_S with ⟨ r, h_r, h ⟩
  use r
  subst S
  constructor
  tauto
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at h_r
  rcases h_r with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst r
  · simp only [base_rel_of_hom_lift_of_interchange_of_αβψ]
    sorry
  stop sorry

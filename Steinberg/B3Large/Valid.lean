import Steinberg.B3Large.Defs

open Steinberg B3Large GradedPartialChevalley PartialChevalley

theorem valid_of_hom_lifted (F : Type TF) [Field F] :
  ∀ S ∈ hom_lifted_sets F, ∃ r : FreeGroup (ChevalleyGenerator B3LargePosRoot F), S = hom_lift_set r ∧ (fullB3Large F).pres_mk r = 1 := by
  intro S h_S
  simp only [hom_lifted_sets] at h_S
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at h_S
  rcases h_S with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst h
  stop sorry

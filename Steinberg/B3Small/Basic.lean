/-

LICENSE goes here.

-/

import Steinberg.B3Small.Defs

/-!

  File dox.

-/

namespace Steinberg.B3Small

open B3SmallPosRoot GradedPartialChevalley GradedChevalleyGenerator GradedPartialChevalleyGroup

variable {F : Type TF} [Field F]

/-! # "Given" relations for specific roots -/

declare_B3Small_lin_id_inv_thms F β
declare_B3Small_lin_id_inv_thms F ψ
declare_B3Small_lin_id_inv_thms F ω
declare_B3Small_lin_id_inv_thms F βψ
declare_B3Small_lin_id_inv_thms F ψω
declare_B3Small_lin_id_inv_thms F β2ψ

-- declare_B3Small_refl_def_thm F β


declare_B3Small_triv_comm_of_root_pair_thms F β βψ
declare_B3Small_triv_comm_of_root_pair_thms F β β2ψ
declare_B3Small_triv_comm_of_root_pair_thms F ψ β2ψ
declare_B3Small_triv_comm_of_root_pair_thms F βψ β2ψ
declare_B3Small_triv_comm_of_root_pair_thms F β ω
declare_B3Small_triv_comm_of_root_pair_thms F ψ ψω
declare_B3Small_triv_comm_of_root_pair_thms F ω ψω

declare_B3Small_single_comm_of_root_pair_thms F ψ ω ψω 2
declare_B3Small_single_comm_of_root_pair_thms F ψ βψ β2ψ 2

/-! ### Mixed-degree theorem for specific roots -/

declare_B3Small_mixed_comm_thms F βψ
declare_B3Small_mixed_comm_thms F ψω
declare_B3Small_mixed_comm_thms F β2ψ

open ReflDeg in
theorem refl_def_of_βψ_eq_refl_of_gen (F : Type TR) [Field F] (g : GradedChevalleyGenerator B3SmallPosRoot F) (h : g.ζ = βψ) :
          (weakB3Small F).pres_mk (refl_def (weakB3Small F) g) = (weakB3Small F).pres_mk (FreeGroup.of (refl_of_gen g)) := by
  congr
  apply refl_def_of_present_eq_refl_of_gen
  rw [h]
  simp only [weakB3Small, present_roots]
  tauto

open ReflDeg in
theorem refl_def_of_ψω_eq_refl_of_gen (F : Type TR) [Field F] (g : GradedChevalleyGenerator B3SmallPosRoot F) (h : g.ζ = ψω) :
          (weakB3Small F).pres_mk (refl_def (weakB3Small F) g) = (weakB3Small F).pres_mk (FreeGroup.of (refl_of_gen g)) := by
  congr
  apply refl_def_of_present_eq_refl_of_gen
  rw [h]
  simp only [weakB3Small, present_roots]
  tauto

open ReflDeg in
theorem refl_def_of_ω_eq_refl_of_gen (F : Type TR) [Field F] (g : GradedChevalleyGenerator B3SmallPosRoot F) (h : g.ζ = ω) :
          (weakB3Small F).pres_mk (refl_def (weakB3Small F) g) = (weakB3Small F).pres_mk (FreeGroup.of (refl_of_gen g)) := by
  congr
  apply refl_def_of_present_eq_refl_of_gen
  rw [h]
  simp only [weakB3Small, present_roots]
  tauto

end Steinberg.B3Small

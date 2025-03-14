/-

LICENSE goes here.

-/

import Steinberg.B3Large.Defs

/-!

  File dox.

-/

namespace Steinberg.B3Large

open B3LargePosRoot GradedPartialChevalley GradedChevalleyGenerator GradedPartialChevalleyGroup

variable {F : Type TF} [Field F]

/-! # "Given" relations for specific roots -/

declare_B3Large_lin_id_inv_thms F α
declare_B3Large_lin_id_inv_thms F β
declare_B3Large_lin_id_inv_thms F ψ
declare_B3Large_lin_id_inv_thms F αβ
declare_B3Large_lin_id_inv_thms F βψ
declare_B3Large_lin_id_inv_thms F β2ψ

declare_B3Large_triv_comm_of_root_pair_thms F α αβ
declare_B3Large_triv_comm_of_root_pair_thms F β αβ
declare_B3Large_triv_comm_of_root_pair_thms F α ψ
declare_B3Large_triv_comm_of_root_pair_thms F β βψ
declare_B3Large_triv_comm_of_root_pair_thms F β β2ψ
declare_B3Large_triv_comm_of_root_pair_thms F ψ β2ψ
declare_B3Large_triv_comm_of_root_pair_thms F βψ β2ψ

declare_B3Large_single_comm_of_root_pair_thms F α β αβ 1
declare_B3Large_single_comm_of_root_pair_thms F ψ βψ β2ψ 2

-- Double: {(β, ψ)}
theorem comm_of_β_ψ : double_commutator_of_root_pair (weakB3Large F).pres_mk ⟨β, ψ, βψ, β2ψ, 1, 1, by rfl, by rfl⟩ :=
  (weakB3Large F).double_commutator_helper ⟨β, ψ, βψ, β2ψ, 1, 1, by rfl, by rfl⟩
    (by unfold weakB3Large; simp)

/-! ### Mixed-degree theorem for specific roots -/

declare_B3Large_mixed_comm_thms F α
declare_B3Large_mixed_comm_thms F β
declare_B3Large_mixed_comm_thms F ψ
declare_B3Large_mixed_comm_thms F αβ
declare_B3Large_mixed_comm_thms F βψ
declare_B3Large_mixed_comm_thms F β2ψ

end Steinberg.B3Large

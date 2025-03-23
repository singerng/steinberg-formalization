/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.A3.Ungraded.Defs

/-!

  By definition, we can immediately prove many theorems about the
  triviality of commutators, that group elements are linear in their
  ring elements, and so on.

  All the proofs for these theorems are extremely similar, so much so
  that we can declare and prove them from macros agnostic to the root system.

  See `PartialChevalleyGroup.lean` for their definitions.

-/

namespace Steinberg.A3

open A3PosRoot PartialChevalley PartialChevalleyGroup ChevalleyGenerator

variable {R : Type TR} [Ring R]

/-! # "Given" relations for specific roots -/

declare_A3_ungraded_lin_id_inv_thms R α
declare_A3_ungraded_lin_id_inv_thms R β
declare_A3_ungraded_lin_id_inv_thms R γ
declare_A3_ungraded_lin_id_inv_thms R αβ
declare_A3_ungraded_lin_id_inv_thms R βγ

declare_A3_ungraded_triv_comm_of_root_pair_thms R α γ
declare_A3_ungraded_triv_comm_of_root_pair_thms R α αβ
declare_A3_ungraded_triv_comm_of_root_pair_thms R β αβ
declare_A3_ungraded_triv_comm_of_root_pair_thms R β βγ
declare_A3_ungraded_triv_comm_of_root_pair_thms R γ βγ

declare_A3_ungraded_single_comm_of_root_pair_thms R α β αβ 0 1
declare_A3_ungraded_single_comm_of_root_pair_thms R β γ βγ 0 1

/-

Macros and other convenience keywords when doing proofs on groups.

-/

import Mathlib.Tactic.SimpRw
import Mathlib.Algebra.Group.Defs

namespace Steinberg.Macro

/-- Shorthand for `simp_rw [← mul_assoc]`, which applies the `mul_assoc` tactic to the left. -/
macro (name := mul_assoc_l) "mul_assoc_l" : tactic => `(tactic|
  simp_rw [← mul_assoc]
)

/-- Shorthand for `simp_rw [mul_assoc]`, which applies the `mul_assoc` tactic to the right. -/
macro (name := mul_assoc_r) "mul_assoc_r" : tactic => `(tactic|
  simp_rw [mul_assoc]
)

end Steinberg.Macro

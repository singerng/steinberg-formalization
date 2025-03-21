/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Mathlib.Tactic.Group
import Steinberg.Macro.Group

namespace Steinberg

variable {G : Type TG} [Group G]
         {w x y z : G}

-- Star operator
def star (x y : G) := y⁻¹ * x * y^2 * x⁻¹ * y⁻¹
infix:68 " ⋆ " => star

theorem star_commutator (x y : G) : (x ⋆ y) * ⁅(x ⋆ y)⁻¹, y⁆ = ⁅x, y^2⁆ := by
  unfold star
  group

theorem commutator_star (x y : G) : ⁅x ⋆ y, y⁆⁻¹ * (x ⋆ y) = ⁅x, y^2⁆ := by
  unfold star
  group

end Steinberg

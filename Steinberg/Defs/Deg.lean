import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Use

namespace Steinberg

-- NS: For now, we encode an input "i ≤ n" as a pair (i : ℕ) (hi : i ≤ n).

/--
  Decompose a number `0 ≤ i ≤ n + m` into `i₁ + i₂`, where `0 ≤ i₁ ≤ n` and `0 ≤ i₂ ≤ m`.
 -/
theorem decompose (n m i : ℕ) (h : i ≤ (n+m)) : ∃ (i₁ i₂ : ℕ), i = i₁ + i₂ ∧ i₁ ≤ n ∧ i₂ ≤ m := by
  by_cases i ≤ n
  · use i, 0
    omega
  · use n, i-n
    omega

end Steinberg

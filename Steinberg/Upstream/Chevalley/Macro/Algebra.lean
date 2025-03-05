import Mathlib.Tactic
import Mathlib.Algebra.Algebra.Defs


namespace Steinberg

-- tactic, under development, to simplify algebra expressions
macro (name := algebra) "algebra" : tactic => `(tactic|
  simp only [
    -- additive ring structure
    mul_add, add_mul, neg_add, sub_eq_add_neg, add_zero, zero_add,
    -- multiplicative ring structure
    one_mul, mul_one, mul_zero, zero_mul, mul_neg,
    -- scalar structure
    smul_smul,              -- t • (u • x) = (t * u) • x
    mul_smul_comm,          -- x * (t • y) = t • (x * y)
    smul_mul_assoc,         -- (t • x) * y = t • (x * y)
    ← neg_one_smul,         -- -x = (-1) • x
    ← neg_smul,             -- -(r • x) = (-r) • x
    smul_add,               -- t • (x + y) = t • x + t • y
    smul_zero, zero_smul    -- 0 • x = x • 0 = 0
  ]
)

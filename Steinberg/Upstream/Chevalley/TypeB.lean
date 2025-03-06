import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import Steinberg.Upstream.Chevalley.Macro.Algebra
import Steinberg.Upstream.Chevalley.IndicatorMatrix


/-!
  An implementation of the group `Ω_{2n+1}(R)` of `(2n+1)×(2n+1)` matrices over a ring `R`.
  This is a certain "mysterious" subgroup of `SO_{2n+1}(R)`, the group of `(2n+1)×(2n+1)`
  *orthogonal* matrices with determinant `1` over `R`. The group `Ω_{2n+1}(R)` is the Chevalley
  group for the root system `B_n`. Its generators fall into two disjoint classes corresponding
  to `short` and `long` roots in the root system. All generators have `1`'s on the diagonal. The
  `long` matrices have two paired nonzero off-diagonal entries, and the `short` matrices have three.
  We again verify the *Steinberg* relations followed by these roots.

  The paired structure of the coordinates is reflected in the type `Signed I` below, which given an
  instance `I` of `Fintype` and `DecidableEq` produces a new type which is an instance of the same
  typeclasses and has cardinality `2|I|+1`; the members are `plus (i : I)`, `minus (i : I)`, and `zero`.
-/

universe u v

variable {R : Type u} [CommRing R]
variable {I : Type v} [DecidableEq I] [Fintype I]

inductive Sign
  | plus
  | minus

def Sign.neg (s : Sign) : Sign :=
  match s with
  | Sign.plus => Sign.minus
  | Sign.minus => Sign.plus

inductive Signed (I : Type v) [DecidableEq I] where
  | plus : I → Signed I
  | minus : I → Signed I
  | zero
deriving Fintype

def Sign.inj (s : Sign) (i : I) : Signed I :=
  match s with
  | Sign.plus => Signed.plus i
  | Sign.minus => Signed.minus i

def Sign.toRing {R : Type u} [CommRing R] (s : Sign) : R :=
  match s with
  | Sign.plus => (1 : R)
  | Sign.minus => (-1 : R)

instance : DecidableEq (Signed I) := by
  intro i₁ i₂
  cases i₁ <;> cases i₂
  all_goals simp
  any_goals apply isFalse; simp only [not_false_eq_true]
  any_goals apply isTrue; trivial
  all_goals rename_i x _ a₁ a₂; exact x a₁ a₂

instance : Coe Sign R where
  coe x := x.toRing

theorem Sign.square_eq_one {a : Sign} : a.toRing^2 = (1 : R) := by
  rcases a
  all_goals (
    simp only [Sign.toRing]
    ring
  )

@[simp]
theorem Sign.neg_of_neg {a : Sign} : a.neg.neg = a := by
  rcases a
  all_goals simp only [Sign.neg]

@[simp]
theorem Sign.int_of_neg {R : Type u} [CommRing R] (a : Sign) : @a.neg.toRing R _ = -a.toRing := by
  rcases a
  all_goals simp only [Sign.neg, Sign.toRing, neg_neg]

theorem Signed.zero_ne_signed {a : Sign} {i : I} : Signed.zero ≠ a.inj i := by
  by_contra h'
  simp only [Sign.inj] at h'
  rcases a
  all_goals contradiction

theorem Signed.signed_ne_zero {a : Sign} {i : I} : a.inj i ≠ Signed.zero := Ne.symm zero_ne_signed

theorem Signed.ne_of_neg {a : Sign} {i j : I} : a.neg.inj i ≠ a.inj j := by
  by_contra h'
  simp only [Sign.inj, Sign.neg] at h'
  rcases a
  all_goals contradiction

theorem Signed.ne_of_ne {a b : Sign} {i j : I} (h : i ≠ j) : a.inj i ≠ b.inj j := by
  by_contra h'
  simp only [Sign.inj] at h'
  rcases a <;> rcases b
  all_goals injection h'
  all_goals contradiction

theorem Signed.neg_of_ne {a b : Sign} {i j : I} (h : a.inj i ≠ b.neg.inj j) : a.neg.inj i ≠ b.inj j := by
  by_contra h'
  simp only [Sign.inj] at h'
  rcases a <;> rcases b
  all_goals injection h'
  all_goals tauto

/-- The generator matrices -/
def MS (a : Sign) (i : I) (t : R) : Matrix (Signed I) (Signed I) R :=
  1 + (2 * a * t) • (E (a.inj i) Signed.zero)
    - (a * t) • (E Signed.zero (a.neg.inj i))
    - (t^2) • (E (a.inj i) (a.neg.inj i))

def ML (a b : Sign) (i j : I) (t : R) (hij : i ≠ j) : Matrix (Signed I) (Signed I) R :=
  1 + (a * t) • (E (a.inj i) (b.neg.inj j))
    - (a * t) • (E (b.inj j) (a.neg.inj i))

-- /-- Relation A.9, identity for short matrices -/
theorem MS_zero_eq_one {a : Sign} {i : I}
  : MS a i (0 : R) = 1 := by
  rw [MS]
  algebra
  module

-- /-- Relation A.10, identity for long matrices -/
theorem ML_zero_eq_one {a b : Sign} {i j : I} {hij : i ≠ j}
  : ML a b i j (0 : R) hij = 1 := by
  rw [ML]
  algebra
  module

/-- Relation A.11, linearity for short matrices -/
theorem MS_mul_add {a : Sign} {i : I} {t u : R}
  : (MS a i t) * (MS a i u) = MS a i (t + u) := by
  let x := MS a i t
  repeat rw [MS]
  algebra
  simp only [E_mul_disjoint Signed.zero_ne_signed,
            E_mul_disjoint Signed.signed_ne_zero,
            E_mul_disjoint Signed.ne_of_neg, E_mul_overlap]
  algebra
  ring_nf
  simp only [Sign.square_eq_one]
  module

/-- Relation A.11, linearity for long matrices -/
theorem ML_mul_add {a b : Sign} {i j : I} {t u : R} (hij : i ≠ j)
  : (ML a b i j t hij) * (ML a b i j u hij) = ML a b i j (t + u) hij := by
  repeat rw [ML]
  algebra
  simp only [E_mul_disjoint (Signed.ne_of_ne hij),
            E_mul_disjoint (Signed.ne_of_ne (Ne.symm hij)),
            E_mul_disjoint (Signed.ne_of_neg)]
  module

theorem MS_comm {a b : Sign} {i j : I} {t u : R} (hij : i ≠ j)
  : (MS a i t) * (MS b j u) * (MS a i (-t)) * (MS b j (-u)) = ML a b i j (-2*b*t*u) hij := by
  simp only [MS, ML]
  algebra
  simp only [E_mul_disjoint Signed.zero_ne_signed,
    E_mul_disjoint Signed.signed_ne_zero,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint (Signed.ne_of_ne hij),
    E_mul_disjoint (Signed.ne_of_ne (Ne.symm hij)),
    E_mul_overlap
    ]
  algebra
  ring_nf
  simp only [Sign.square_eq_one]
  module

theorem ML_comm_disjoint {a b c d : Sign} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : a.inj i ≠ c.neg.inj k) (hil : a.inj i ≠ d.neg.inj l) (hjk : b.inj j ≠ c.neg.inj k) (hjl : b.inj j ≠ d.neg.inj l)
  : (ML a b i j t hij) * (ML c d k l u hkl) = (ML c d k l u hkl) * (ML a b i j t hij) := by
  simp only [ML]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    E_mul_disjoint (Ne.symm hik),
    E_mul_disjoint (Ne.symm hil),
    E_mul_disjoint (Ne.symm hjk),
    E_mul_disjoint (Ne.symm hjl),
    E_mul_disjoint (Signed.neg_of_ne hik),
    E_mul_disjoint (Signed.neg_of_ne hil),
    E_mul_disjoint (Signed.neg_of_ne hjk),
    E_mul_disjoint (Signed.neg_of_ne hjl)]
  algebra
  module

theorem ML_comm_overlap {a b c : Sign} {i j k : I} {t u : R} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : (ML a b i j t hij) * (ML b.neg c j k u hjk) * (ML a b i j (-t) hij) * (ML b.neg c j k (-u) hjk) = (ML a c i k (-b*t*u) hik) := by
  simp only [ML]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    Sign.neg_of_neg,
    E_mul_disjoint Signed.ne_of_neg,
    E_mul_disjoint Signed.ne_of_neg.symm,
    E_mul_disjoint (Signed.ne_of_ne hjk),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hjk.symm)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hik)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hik.symm)),
    E_mul_disjoint (Signed.neg_of_ne (Signed.ne_of_ne hij)),
    E_mul_disjoint (Signed.ne_of_ne hij.symm),
  ]
  algebra
  simp only [Sign.int_of_neg]
  module

theorem ML_MS_comm_disjoint {a b c : Sign} {i j k : I} {t u : R} (hij : i ≠ j)
  (hik : a.inj i ≠ c.neg.inj k) (hjk : b.inj j ≠ c.neg.inj k)
  : (ML a b i j t hij) * (MS c k u) = (MS c k u) * (ML a b i j t hij)
  := by
    simp only [ML, MS]
    algebra
    ring_nf
    simp only [E_mul_overlap,
      E_mul_disjoint Signed.zero_ne_signed,
      E_mul_disjoint Signed.signed_ne_zero,
      E_mul_disjoint Signed.ne_of_neg,
      E_mul_disjoint hik.symm,
      E_mul_disjoint hjk.symm,
      E_mul_disjoint (Signed.neg_of_ne hik),
      E_mul_disjoint (Signed.neg_of_ne hjk)
      ]
    algebra
    module

theorem ML_MS_comm_overlap {a b : Sign} {i j : I} {t u : R} (hij : i ≠ j)
  : (ML a b i j t hij) * (MS a.neg i u) * (ML a b i j (-t) hij) * (MS a.neg i (-u)) =
    (ML a.neg b i j (-t*u^2) hij) * (MS b j (b*t*u)) := by
    simp only [ML, MS]
    algebra
    simp only [Sign.neg_of_neg]
    simp only [E_mul_overlap,
      E_mul_disjoint Signed.zero_ne_signed,
      E_mul_disjoint Signed.signed_ne_zero,
      E_mul_disjoint Signed.ne_of_neg,
      E_mul_disjoint (Ne.symm (Signed.ne_of_neg)),
      E_mul_disjoint (Signed.ne_of_ne hij),
      E_mul_disjoint (Signed.ne_of_ne (Ne.symm hij))]
    algebra
    ring_nf
    match_scalars
    any_goals simp
    any_goals simp only [Sign.square_eq_one]
    all_goals ring_nf
    all_goals simp only [Sign.square_eq_one]
    all_goals ring_nf

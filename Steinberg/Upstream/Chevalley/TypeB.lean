import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Module

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

def SignedWithZero (I : Type v) [DecidableEq I] [Fintype I] :=
  (Bool × I) ⊕ Unit
instance : DecidableEq (SignedWithZero I) := instDecidableEqSum
instance : Fintype (SignedWithZero I) := instFintypeSum _ _

-- NS: Maybe there is a more 'idiomatic' way to write this shortly?

def SignedWithZero.zero : SignedWithZero I := Sum.inr ()
def Bool.inj (s : Bool) (i : I) : SignedWithZero I := Sum.inl (s, i)

def Bool.toRing {R : Type u} [CommRing R] (s : Bool) : R :=
  match s with
  | Bool.true => (1 : R)
  | Bool.false => (-1 : R)

instance : Coe Bool R where
  coe x := x.toRing

theorem square_eq_one {a : Bool} : a.toRing^2 = (1 : R) := by
  rcases a
  all_goals (
    simp only [Bool.toRing]
    ring
  )

@[simp]
theorem Bool.int_of_neg {R : Type u} [CommRing R] (a : Bool) : @(!a).toRing R _ = -a.toRing := by
  rcases a
  all_goals simp only [Bool.not, Bool.toRing, neg_neg]

theorem SignedWithZero.zero_ne_signed {a : Bool} {i : I} : SignedWithZero.zero ≠ a.inj i := by
  simp only [Bool.inj, SignedWithZero.zero]
  by_contra
  injections

theorem SignedWithZero.signed_ne_zero {a : Bool} {i : I} : a.inj i ≠ SignedWithZero.zero := Ne.symm zero_ne_signed

theorem SignedWithZero.ne_of_neg {a : Bool} {i j : I} : (!a).inj i ≠ a.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  simp_all only [Bool.not_eq_eq_eq_not, Bool.eq_not_self]

theorem SignedWithZero.ne_of_ne {a b : Bool} {i j : I} (h : i ≠ j) : a.inj i ≠ b.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  contradiction

theorem SignedWithZero.neg_of_ne {a b : Bool} {i j : I} (h : a.inj i ≠ (!b).inj j) : (!a).inj i ≠ b.inj j := by
  simp only [Bool.inj]
  by_contra
  injections
  simp_all only [ne_eq, Bool.not_eq_eq_eq_not, not_true_eq_false]

/-- The generator matrices -/
def MShort (a : Bool) (i : I) (t : R) : Matrix (SignedWithZero I) (SignedWithZero I) R :=
  1 + (2 * a * t) • (E (a.inj i) SignedWithZero.zero)
    - (a * t) • (E SignedWithZero.zero ((!a).inj i))
    - (t^2) • (E (a.inj i) ((!a).inj i))

def MLong (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) : Matrix (SignedWithZero I) (SignedWithZero I) R :=
  1 + (a * t) • (E (a.inj i) ((!b).inj j))
    - (a * t) • (E (b.inj j) ((!a).inj i))

-- /-- Relation A.9, identity for short matrices -/
theorem MShort_zero_eq_one {a : Bool} {i : I}
  : MShort a i (0 : R) = 1 := by
  rw [MShort]
  algebra
  module

-- /-- Relation A.10, identity for long matrices -/
theorem MLong_zero_eq_one {a b : Bool} {i j : I} {hij : i ≠ j}
  : MLong a b i j (0 : R) hij = 1 := by
  rw [MLong]
  algebra
  module

/-- Relation A.11, linearity for short matrices -/
theorem MShort_mul_add {a : Bool} {i : I} {t u : R}
  : (MShort a i t) * (MShort a i u) = MShort a i (t + u) := by
  let x := MShort a i t
  repeat rw [MShort]
  algebra
  simp only [E_mul_disjoint SignedWithZero.zero_ne_signed,
            E_mul_disjoint SignedWithZero.signed_ne_zero,
            E_mul_disjoint SignedWithZero.ne_of_neg, E_mul_overlap]
  algebra
  ring_nf
  simp only [square_eq_one]
  module

/-- Relation A.11, linearity for long matrices -/
theorem MLong_mul_add {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (MLong a b i j t hij) * (MLong a b i j u hij) = MLong a b i j (t + u) hij := by
  repeat rw [MLong]
  algebra
  simp only [E_mul_disjoint (SignedWithZero.ne_of_ne hij),
            E_mul_disjoint (SignedWithZero.ne_of_ne (Ne.symm hij)),
            E_mul_disjoint (SignedWithZero.ne_of_neg)]
  module

theorem MShort_comm {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (MShort a i t) * (MShort b j u) * (MShort a i (-t)) * (MShort b j (-u)) = MLong a b i j (-2*b*t*u) hij := by
  simp only [MShort, MLong]
  algebra
  simp only [E_mul_disjoint SignedWithZero.zero_ne_signed,
    E_mul_disjoint SignedWithZero.signed_ne_zero,
    E_mul_disjoint SignedWithZero.ne_of_neg,
    E_mul_disjoint (SignedWithZero.ne_of_ne hij),
    E_mul_disjoint (SignedWithZero.ne_of_ne (Ne.symm hij)),
    E_mul_overlap
    ]
  algebra
  ring_nf
  simp only [square_eq_one]
  module

theorem MLong_comm_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : a.inj i ≠ (!c).inj k) (hil : a.inj i ≠ (!d).inj l) (hjk : b.inj j ≠ (!c).inj k) (hjl : b.inj j ≠ (!d).inj l)
  : (MLong a b i j t hij) * (MLong c d k l u hkl) = (MLong c d k l u hkl) * (MLong a b i j t hij) := by
  simp only [MLong]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    E_mul_disjoint (Ne.symm hik),
    E_mul_disjoint (Ne.symm hil),
    E_mul_disjoint (Ne.symm hjk),
    E_mul_disjoint (Ne.symm hjl),
    E_mul_disjoint (SignedWithZero.neg_of_ne hik),
    E_mul_disjoint (SignedWithZero.neg_of_ne hil),
    E_mul_disjoint (SignedWithZero.neg_of_ne hjk),
    E_mul_disjoint (SignedWithZero.neg_of_ne hjl)]
  algebra
  module

theorem MLong_comm_overlap {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : (MLong a b i j t hij) * (MLong (!b) c j k u hjk) * (MLong a b i j (-t) hij) * (MLong (!b) c j k (-u) hjk) = (MLong a c i k (-b*t*u) hik) := by
  simp only [MLong]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    Bool.not_not,
    E_mul_disjoint SignedWithZero.ne_of_neg,
    E_mul_disjoint SignedWithZero.ne_of_neg.symm,
    E_mul_disjoint (SignedWithZero.ne_of_ne hjk),
    E_mul_disjoint (SignedWithZero.neg_of_ne (SignedWithZero.ne_of_ne hjk.symm)),
    E_mul_disjoint (SignedWithZero.neg_of_ne (SignedWithZero.ne_of_ne hik)),
    E_mul_disjoint (SignedWithZero.neg_of_ne (SignedWithZero.ne_of_ne hik.symm)),
    E_mul_disjoint (SignedWithZero.neg_of_ne (SignedWithZero.ne_of_ne hij)),
    E_mul_disjoint (SignedWithZero.ne_of_ne hij.symm),
  ]
  algebra
  simp only [Bool.int_of_neg]
  module

theorem MLong_MShort_comm_disjoint {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j)
  (hik : a.inj i ≠ (!c).inj k) (hjk : b.inj j ≠ (!c).inj k)
  : (MLong a b i j t hij) * (MShort c k u) = (MShort c k u) * (MLong a b i j t hij)
  := by
    simp only [MLong, MShort]
    algebra
    ring_nf
    simp only [E_mul_overlap,
      E_mul_disjoint SignedWithZero.zero_ne_signed,
      E_mul_disjoint SignedWithZero.signed_ne_zero,
      E_mul_disjoint SignedWithZero.ne_of_neg,
      E_mul_disjoint hik.symm,
      E_mul_disjoint hjk.symm,
      E_mul_disjoint (SignedWithZero.neg_of_ne hik),
      E_mul_disjoint (SignedWithZero.neg_of_ne hjk)
      ]
    algebra
    module

theorem MLong_MShort_comm_overlap {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (MLong a b i j t hij) * (MShort (!a) i u) * (MLong a b i j (-t) hij) * (MShort (!a) i (-u)) =
    (MLong (!a) b i j (-t*u^2) hij) * (MShort b j (b*t*u)) := by
    simp only [MLong, MShort]
    algebra
    simp only [Bool.not_not]
    simp only [E_mul_overlap,
      E_mul_disjoint SignedWithZero.zero_ne_signed,
      E_mul_disjoint SignedWithZero.signed_ne_zero,
      E_mul_disjoint SignedWithZero.ne_of_neg,
      E_mul_disjoint (Ne.symm (SignedWithZero.ne_of_neg)),
      E_mul_disjoint (SignedWithZero.ne_of_ne hij),
      E_mul_disjoint (SignedWithZero.ne_of_ne (Ne.symm hij))]
    algebra
    ring_nf
    match_scalars
    any_goals simp
    any_goals simp only [square_eq_one]
    all_goals ring_nf
    all_goals simp only [square_eq_one]
    all_goals ring_nf

/-- Encodes a vector with exactly two nonzero, ±1 elements -/
structure BLongRoot (I : Type v) where
  mk ::
  i : I
  j : I
  a : Bool
  b : Bool
  hij : i ≠ j

def BLongRoot.M (ζ : BLongRoot I) (t : R) :=
  MLong ζ.a ζ.b ζ.i ζ.j t ζ.hij

structure BShortRoot (I : Type v) where
  mk ::
  i : I
  a : Bool

def BShortRoot.M (ζ : BShortRoot I) (t : R) :=
  MShort ζ.a ζ.i t

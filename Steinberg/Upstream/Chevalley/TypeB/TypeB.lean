
import Steinberg.Upstream.Chevalley.TypeB.MatrixDefs

import Steinberg.Macro.Group

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

variable {I : Type TI} [DecidableEq I] [Fintype I] [LinearOrder I]
variable {R : Type TR} [CommRing R]

namespace Chevalley.TypeB
open Chevalley.TypeB

theorem MLong_swap (a b : Bool) (i j : I) (t : R) (hij : i ≠ j) :
  (MLong a b i j t hij) = (MLong b a j i (-t * a * b) (Ne.symm hij)) := by
  ext1
  simp only [MLong, raw_MLong]
  ring_nf
  simp only [square_eq_one]
  module


-- /-- Relation A.9, identity for short matrices -/
theorem MShort_zero_eq_one {a : Bool} {i : I}
  : MShort a i (0 : R) = 1 := by
  ext1
  simp only [MShort, raw_MShort]
  algebra
  module

-- /-- Relation A.10, identity for long matrices -/
theorem MLong_zero_eq_one {a b : Bool} {i j : I} {hij : i ≠ j}
  : MLong a b i j (0 : R) hij = 1 := by
  ext1
  simp only [MLong, raw_MLong, Units.val_one]
  algebra
  module

/-- Relation A.11, linearity for short matrices -/
theorem MShort_mul_add {a : Bool} {i : I} {t u : R}
  : (MShort a i t) * (MShort a i u) = MShort a i (t + u) := by
  ext1
  simp only [MShort, raw_MShort, Units.val_mul]
  algebra
  simp only [E_mul_disjoint SignedWithZero.zero_ne_signed,
            E_mul_disjoint SignedWithZero.signed_ne_zero,
            E_mul_disjoint SignedWithZero.ne_of_neg, E_mul_overlap]
  algebra
  ring_nf
  simp only [square_eq_one]
  module


theorem MLong_mul_add {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : (MLong a b i j t hij) * (MLong a b i j u hij) = MLong a b i j (t + u) hij := by
  ext1
  simp only [MLong, raw_MLong, Units.val_mul]
  algebra
  simp only [E_mul_disjoint (SignedWithZero.ne_of_ne hij),
            E_mul_disjoint (SignedWithZero.ne_of_ne (Ne.symm hij)),
            E_mul_disjoint (SignedWithZero.ne_of_neg)]
  module

/- ### Trivial commutators -/

private theorem MLong_prod_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : a.inj i ≠ (!c).inj k) (hil : a.inj i ≠ (!d).inj l) (hjk : b.inj j ≠ (!c).inj k) (hjl : b.inj j ≠ (!d).inj l)
  : (raw_MLong a b i j t hij) * (raw_MLong c d k l u hkl) =
  1 + (a * t) • E (a.inj i) ((!b).inj j)
    - (a * t) • E (b.inj j) ((!a).inj i)
    + (c * u) • E (c.inj k) ((!d).inj l)
    - (c * u) • E (d.inj l) ((!c).inj k)  := by
  simp only [raw_MLong]
  algebra
  ring_nf
  simp only [E_mul_disjoint (SignedWithZero.neg_of_ne hik),
  E_mul_disjoint (SignedWithZero.neg_of_ne hjk),
  E_mul_disjoint (SignedWithZero.neg_of_ne hjl),
  E_mul_disjoint (SignedWithZero.neg_of_ne hil)
  ]
  algebra

theorem MLong_comm_disjoint {a b c d : Bool} {i j k l : I} {t u : R} (hij : i ≠ j) (hkl : k ≠ l)
  (hik : a.inj i ≠ (!c).inj k) (hil : a.inj i ≠ (!d).inj l) (hjk : b.inj j ≠ (!c).inj k) (hjl : b.inj j ≠ (!d).inj l)
  : ⁅ (MLong a b i j t hij), (MLong c d k l u hkl) ⁆ = 1 := by
  rw [commutatorElement_def]
  ext1
  simp only [MLong, Units.val_mul, Units.inv_mk]
  grw [MLong_prod_disjoint]
  grw [MLong_prod_disjoint]


  algebra


  -- apply mul_inv_eq_of_eq_mul
  -- apply mul_inv_eq_of_eq_mul
  -- simp only [one_mul]
  -- ext1
  -- simp only [MLong, raw_MLong, Units.val_mul]
  -- algebra
  -- ring_nf
  -- simp only [E_mul_overlap,
  --   E_mul_disjoint (Ne.symm hik),
  --   E_mul_disjoint (Ne.symm hil),
  --   E_mul_disjoint (Ne.symm hjk),
  --   E_mul_disjoint (Ne.symm hjl),
  --   E_mul_disjoint (SignedWithZero.neg_of_ne hik),
  --   E_mul_disjoint (SignedWithZero.neg_of_ne hil),
  --   E_mul_disjoint (SignedWithZero.neg_of_ne hjk),
  --   E_mul_disjoint (SignedWithZero.neg_of_ne hjl)]
  -- algebra
  -- module

theorem MLong_comm_disjoint' {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (MLong a b i j t hij), (MLong a (!b) i j u hij) ⁆ = 1 := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  simp only [one_mul]
  ext1
  simp only [MLong, raw_MLong, Units.val_mul]
  algebra
  ring_nf
  simp only [E_mul_overlap,
    E_mul_disjoint SignedWithZero.ne_of_neg,
    E_mul_disjoint (SignedWithZero.ne_of_ne hij),
    E_mul_disjoint (SignedWithZero.ne_of_ne hij.symm),
    Bool.not_not
    ]
  algebra
  module

theorem MLong_MShort_comm_disjoint {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j)
  (hik : a.inj i ≠ (!c).inj k) (hjk : b.inj j ≠ (!c).inj k)
  : ⁅ (MLong a b i j t hij), (MShort c k u) ⁆ = 1 := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  simp only [one_mul]
  ext1
  simp only [MLong, raw_MLong, MShort, raw_MShort, Units.val_mul]
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

/- ### Single commutators -/

theorem MLong_comm_overlap {a b c : Bool} {i j k : I} {t u : R} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
  : ⁅ (MLong a b i j t hij), (MLong (!b) c j k u hjk) ⁆ = (MLong a c i k (-b*t*u) hik) := by
  rw [commutatorElement_def]
  apply mul_inv_eq_of_eq_mul
  apply mul_inv_eq_of_eq_mul
  ext1
  simp only [MLong, raw_MLong, Units.val_mul]
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

theorem MShort_comm {a b : Bool} {i j : I} {t u : R} (hij : i ≠ j)
  : ⁅ (MShort a i t), (MShort b j u) ⁆ = MLong a b i j (-2*b*t*u) hij := by
  rw [commutatorElement_def]
  ext1
  simp only [MShort, MLong, raw_MShort, raw_MLong, Units.inv_mk, Units.val_mul]
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


/- ### Double commutators -/

theorem MLong_MShort_comm_overlap (a b : Bool) (i j : I) (t u : R) (hij : i ≠ j)
  : ⁅ (MLong a b i j t hij), (MShort (!a) i u) ⁆ =
    (MShort b j (b*t*u)) * (MLong (!a) b i j (-t*u^2) hij) := by
    rw [commutatorElement_def]
    ext1
    simp only [MShort, MLong, raw_MShort, raw_MLong, Units.inv_mk, Units.val_mul]
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

/- ### Symmetrized versions of statements -/

theorem symm_MLong_MShort_comm_overlap (x : Bool) (a b c : Bool) (i j k : I) (t u : R) (hij : i ≠ j)
   (h_eq : k = cond x i j) (h_neq : c = !(cond x a b)) :
  ⁅ MLong a b i j t hij, MShort c k u ⁆ =
    (MShort (cond x b a) (cond x j i) (x * b * t * u)) *
    (MLong (a^^(x)) (b^^(!x)) i j (-x * t * u^2) hij) := by
  wlog h : x = true -- wlog they overlap on the first coordinate of (i,j)
  · simp only [Bool.not_eq_true] at h
    subst x
    simp only [cond_false] at h_eq h_neq
    subst c k
    replace this := this true b a (!b) j i j (-a * b * t) u hij.symm
    simp only [cond_true, neg_mul, mul_neg, Bool.not_true, Bool.bne_false, Bool.bne_true, neg_neg,
      forall_const] at this
    simp only [cond_false, Bool.not_false, Bool.bne_true, Bool.bne_false, neg_mul]
    nth_rewrite 1 [MLong_swap] at this
    nth_rewrite 2 [MLong_swap] at this
    simp only [Bool.int_of_neg] at this
    ring_nf at this
    simp only [square_eq_one, mul_one, true_toRing, one_mul] at this
    rw [this]
    simp only [false_toRing, neg_mul, one_mul, neg_neg]
  subst x
  simp only [Bool.not_false, cond_true, neg_mul, false_toRing, neg_neg, one_mul]
  simp only [cond_true] at *
  subst c k
  simp only [cond_false, Bool.bne_true, Bool.bne_false]
  simp only [Bool.not_true, Bool.bne_false, true_toRing, one_mul, ← neg_mul]
  exact MLong_MShort_comm_overlap a b i j t u hij


/-- Encodes a vector with exactly two nonzero, ±1 elements -/
structure BLongRoot (I : Type TI) [LinearOrder I] where
  mk ::
  a : Bool
  b : Bool
  i : I
  j : I
  hij : i < j

def BLongRoot.M (ζ : BLongRoot I) (t : R) :=
  MLong ζ.a ζ.b ζ.i ζ.j t (ne_of_lt ζ.hij)


structure BShortRoot (I : Type TI) where
  mk ::
  a : Bool
  i : I

def BShortRoot.M (ζ : BShortRoot I) (t : R) :=
  MShort ζ.a ζ.i t

def BRoot (I : Type TI) [LinearOrder I] := BLongRoot I ⊕ BShortRoot I

def BRoot.M (ζ : BRoot I) (t : R) :=
  match ζ with
  | Sum.inl ζ => ζ.M t
  | Sum.inr ζ => ζ.M t

import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.Group
import Mathlib.Algebra.Ring.Defs

import Steinberg.Defs.Basic
import Steinberg.Macro.Group

namespace Steinberg

open Steinberg.Macro

/-!
A formalization of a certain presentation of a variant of the group of 4x4 unipotent matrices.
A unipotent matrix has 1's on the diagonal, 0's below the diagonal, and arbitrary entries from some ring above the diagonal.

In our group, the entries are *polynomials* with `R` coefficients, i.e., the ring `R[x]` where `R` is a ring and
`x` is an indeterminate. Specifically, we consider the group where every matrix position of "height" `i` has an
entry of degree at most `i`, where the "height" of a position is the taxicab distance to the diagonal.

We label the entries thusly:

(1   α   αβ  αβγ )
(0   1   β   βγ  )
(0   0   1   γ   )
(0   0   0   1   )

Note that α, β, and γ have height 1, αβ and βγ have height 2, and αβγ has height 3. Thus, the α, β, and γ entries are linear
polynomials with `R` coefficients; αβ and βγ are quadratic; and αβγ is cubic. The positions α, β, etc. are also called "roots".

In our group presentation, the generators are of the form {`r` `t` `i`}, where `r` is one of α, β, γ, αβ, or βγ; `t` is in `R`
(an arbitrary ring); and `i` is between 0 and height(`r`) inclusive. Such a generator corresponds to a unipotent matrix with a single homogeneous
entry, `tx^i`, in the `r` position. We consider a certain set of relations which these generators satisfy, and prove from these
all relations characterizing interactions of single-homogeneous-entry-above-diagonal unipotent matrices. (These, in turn,
form a canonical presentation of the entire group.)
-/

variable {G : Type Tu} [Group G]
         {R : Type Tv} [Ring R]


/-- Degrees `Deg` are the (sub)type of natural numbers (including 0)
    that do not exceed `n`, i.e., that `Deg n = {0, 1, ..., n}`. -/
abbrev Deg (n : ℕ) := Fin (n + 1)

/- defining the A3 positive root system -/
inductive A3PositiveRoot
  | α | β | γ | αβ | βγ

namespace A3PositiveRoot

-- CC: Adding the reducible tag lets `simp` peer into the definition,
--     so that you don't have to manually unfold it during proving.
@[reducible]
def height : A3PositiveRoot → Nat
  | A3PositiveRoot.α => 1
  | A3PositiveRoot.β => 1
  | A3PositiveRoot.γ => 1
  | A3PositiveRoot.αβ => 2
  | A3PositiveRoot.βγ => 2

def toString : A3PositiveRoot → String
  | α => "α"
  | β => "β"
  | γ => "γ"
  | αβ => "αβ"
  | βγ => "βγ"

instance instToString : ToString A3PositiveRoot := ⟨toString⟩

end A3PositiveRoot


structure A3UnipGen (R : Type Tv) [Ring R] where
  root : A3PositiveRoot
  coeff : R
  i : Deg root.height

namespace A3UnipGen

open A3PositiveRoot

def mkOf (r : A3PositiveRoot) (coeff : R) (i : Deg r.height) :=
  FreeGroup.of <| mk r coeff i

/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation "{" r ", " coeff ", " i "}" => A3UnipGen.mkOf r coeff i

/--
  Additional shorthand for building free group elements from a root, degree, and ring element.

  CC: It turns out that both `{ }` and `( )` are "reserved syntax" by Lean, and so
      it can't make up its mind if you use things that are also reserved for
      (Fin)sets and Prods. Thus, if you get an "ambiguous, possible interpretations"
      error, you can fall back on using the pipe character '|' to wrap the triple.
-/
scoped notation "|" r ", " coeff ", " i "|" => A3UnipGen.mkOf r coeff i

/--
  Syntax for adding two `Deg`s together, and then automatically deriving the
  proof term needed to show that the resulting value is in range.

  CC: Ideally, we would just use a `Fin` operation, but the closest I could
      find was `Fin.natAdd`, since `Fin.add` takes two `Fin`s of the same
      limit and adds their values together, modulo `n`. Since we know that
      the argument to derive the proof term for the addition probably only
      depends on height, we do that here.
-/
syntax (name := degAdd) term " +' " term : term
macro_rules
  | `($x +' $y) => `(⟨($x).val + ($y).val, by simp [height] at *; omega⟩)

def Linearity (R : Type Tv) [Ring R] : Prop :=
  ∀ (r : A3PositiveRoot) (t u : R) (i : Deg r.height),
    {r, t, i} * {r, u, i} = {r, t + u, i}

-- nontrivial commutators
def α_comm_β (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg α.height) (j : Deg β.height),
 ⁅ {α, t, i}, {β, u, j} ⁆ = |αβ, (t * u), (i +' j)|

def β_comm_γ (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg β.height) (j : Deg γ.height),
 ⁅ {β, t, i}, {γ, u, j} ⁆ = |βγ, (t * u), (i +' j)|

/-
open Lean in
set_option hygiene false in
macro "declare_trivial_commutator" rootOne:ident rootTwo:ident : command => do
  let thmName := ($rootOne : A3PositiveRoot).toString ++ "_comm_" ++ ($rootTwo : A3PositiveRoot).toString
  let mut cmds ← Syntax.getArgs <$> `(
    def $thmName (R : Type Tv) [Ring R] :=
      ∀ (t u : R) (i : Deg $rootOne.height) (j : Deg $rootTwo.height),
        ⁅ { $rootOne, t, i }, { $rootTwo, u, j } ⁆ = 1
  )
  return (mkNullNode cmds) -/

-- trivial commutators

def trivial_commutator (r₁ r₂ : A3PositiveRoot) (R : Type Tv) [Ring R] : Prop :=
  ∀ (t u : R) (i : Deg r₁.height) (j : Deg r₂.height),
    ⁅ {r₁, t, i}, {r₂, u, j} ⁆ = 1

def β_comm_αβ  := trivial_commutator β αβ
def γ_comm_βγ  := trivial_commutator γ βγ
def α_comm_γ   := trivial_commutator α γ
def αβ_comm_βγ := trivial_commutator αβ βγ

structure WeakA3 (R : Type Tv) [Ring R] where
  h_lin : Linearity R
  h_α_β : α_comm_β R
  h_β_γ : β_comm_γ R
  h_α_γ : α_comm_γ R
  h_β_αβ : β_comm_αβ R
  h_γ_βγ : γ_comm_βγ R
  h_αβ_βγ : αβ_comm_βγ R

/- analysis of the group -/
-- deduce identity relations from linearity relations
@[simp]
theorem Identity (h : WeakA3 R) (r : A3PositiveRoot) (i : Deg r.height) :
    {r, (0 : R), i} = 1 := by
  apply @mul_left_cancel _ _ _ |r, 0, i|
  rw [mul_one, h.h_lin r (0 : R) (0 : R) i, add_zero]

-- deduce inverse relations from linearity relations
@[simp]
theorem Inverse (h : WeakA3 R) (r : A3PositiveRoot) (t : R) (i : Deg r.height) :
    |r, -t, i| = |r, t, i|⁻¹ := by
  apply @mul_left_cancel _ _ _ |r, t, i|
  rw [h.h_lin, add_neg_cancel, Identity h, mul_inv_cancel]

-- explicit expressions of commutators
@[simp]
theorem expr_βγ_as_β_comm_γ (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg γ.height) :
    |βγ, (t*u), (i +' j)| = {β, t, i} * {γ, u, j} * {β, (-t), i} * {γ, (-u), j} := by
  rw [Inverse h β, Inverse h γ, ← commutatorElement_def, ← h.h_β_γ]

-- rewrites for products of noncommuting elements
@[simp]
theorem expr_α_β_as_αβ_β_α (h : WeakA3 R) (t u : R) (i : Deg α.height) (j : Deg β.height) :
    |α, t, i| * {β, u, j} = |αβ, (t*u), (i +' j)| * {β, u, j} * {α, t, i} := by
  rw [comm_left_str, h.h_α_β]

@[simp]
theorem expr_β_γ_as_βγ_γ_β (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg γ.height) :
    |β, t, i| * |γ, u, j| = |βγ, (t * u), (i +' j)| * |γ, u, j| * |β, t, i| := by
  rw [comm_left_str, h.h_β_γ]

-- rewrites for products of commuting elements
@[simp]
theorem expr_α_γ_as_γ_α (h : WeakA3 R) (t u : R) (i : Deg α.height) (j : Deg γ.height) :
    |α, t, i| * |γ, u, j| = |γ, u, j| * |α, t, i| := by
  apply comm_to_comm
  rw [h.h_α_γ]

@[simp]
theorem expr_β_αβ_as_αβ_β (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg αβ.height) :
    |β, t, i| * |αβ, u, j| = |αβ, u, j| * |β, t, i| := by
  apply comm_to_comm
  rw [h.h_β_αβ]

@[simp]
theorem expr_γ_βγ_as_βγ_γ (h : WeakA3 R) (t u : R) (i : Deg γ.height) (j : Deg βγ.height) :
    |γ, t, i| * |βγ, u, j| = |βγ, u, j| * |γ, t, i| := by
  apply comm_to_comm
  rw [h.h_γ_βγ]

@[simp]
theorem expr_αβ_βγ_as_βγ_αβ (h : WeakA3 R) (t u : R) (i : Deg αβ.height) (j : Deg βγ.height) :
    |αβ, t, i| * |βγ, u, j| = |βγ, u, j| * |αβ, t, i| := by
  apply comm_to_comm
  rw [h.h_αβ_βγ]

-- interchange theorem, ⁅α, βγ⁆ = ⁅αβ, γ⁆
theorem Interchange (h : WeakA3 R) (t u v : R) (i : Deg α.height) (j : Deg β.height) (k : Deg γ.height) :
    ⁅ |α, t, i|, |βγ, (u * v), (j +' k)| ⁆ = ⁅ |αβ, (t * u), (i +' j)|, |γ, v, k| ⁆ := by
  apply comm_on_left
  -- phase I: push α to right
  rw [expr_βγ_as_β_comm_γ h]
  mul_assoc_l
  rw [expr_α_β_as_αβ_β_α h]
  rw [mul_assoc _ |α, t, i|]
  rw [expr_α_γ_as_γ_α h]
  mul_assoc_l
  rw [mul_assoc _ |α, t, i|]
  rw [expr_α_β_as_αβ_β_α h]
  rw [mul_neg] -- rewrite t*(-u) as -(t*u)
  mul_assoc_l
  rw [mul_assoc _ |α, t, i|]
  rw [expr_α_γ_as_γ_α h]
  mul_assoc_l
  -- phase II: move β's together
  rw [mul_assoc _ |β, u, j|]
  rw [expr_β_γ_as_βγ_γ_β h]
  mul_assoc_l
  rw [mul_assoc _ |β, u, j|]
  rw [expr_β_αβ_as_αβ_β h]
  mul_assoc_l
  rw [mul_assoc _ |β, u, j|]
  rw [Inverse h β]
  group
  -- phase III: push βγ to the right
  rw [mul_assoc _ |βγ, (u * v), (j +' k)|]
  rw [← expr_γ_βγ_as_βγ_γ h]
  mul_assoc_l
  rw [mul_assoc _ |βγ, u * v, j +' k|]
  rw [← expr_αβ_βγ_as_βγ_αβ h]
  mul_assoc_l
  rw [mul_assoc _ |βγ, u * v, j +' k|]
  rw [← expr_γ_βγ_as_βγ_γ h]
  mul_assoc_l
  repeat rw [Inverse h]
  simp only [← commutatorElement_def]
  sorry
  done

theorem InterchangeEmpty (h : WeakA3 R) (t v : R) (i : Deg α.height) (j : Deg β.height) (k : Deg γ.height) :
    ⁅ |α, t, i|, |βγ, v, j +' k| ⁆ = ⁅ |αβ, t, i +' j|, |γ, v, k| ⁆ := by
  nth_rewrite 1 [← one_mul v]
  nth_rewrite 2 [← mul_one t]
  rw [Interchange h]

def mkαβγ {R : Type Tv} [Ring R] (t : R) :=
  ⁅ |α, t, (0 : Fin 2)|, |βγ, (1 : R), (0 : Fin 3)| ⁆
-- ⁅ (mkOf α t (0 : Deg 1)), (mkOf βγ (1 : R) (0 : Deg 2)) ⁆
-- match i.val with
--   | 0 => ⁅ (mkOf 0 (by simp [height] at *)), (@mkOf _ _ βγ (1 : R) 0 (by simp [height] at *)) ⁆
--   | 1 => ⁅ (@mkOf _ _ α t 0 (by simp [height] at *)), (@mkOf _ _ βγ (1 : R) 1 (by simp [height] at *)) ⁆
--   | 2 => ⁅ (@mkOf _ _ α t 0 (by simp [height] at *)), (@mkOf _ _ βγ (1 : R) 2 (by simp [height] at *)) ⁆
--   | 3 => ⁅ (@mkOf _ _ α t 1 (by simp [height] at *)), (@mkOf _ _ βγ (1 : R) 2 (by simp [height] at *)) ⁆

-- theorem comm_α_βγ_0 (h : WeakA3 R) (t u : R) :
--   ⁅@mkOf _ _ α t 0 (by simp [height] at *), @mkOf _ _ βγ u 0 (by simp [height] at *)⁆ =
--   @mkαβγ _ _ (t * u) 0 := by
--   -- rw [mkαβγ (t*u) 0]
--   nth_rewrite 1 [← one_mul u]
--   rw [Interchange h t 1 u]
--   sorry


-- theorem comm_α_βγ [Ring R] (t u : R) {i j : Nat} (hi : i ≤ α.height) (hj : j ≤ βγ.height) :
--   ⁅mkOf α t hi, mkOf βγ u hj⁆ = @mkαβγ _ _ (t * u) (i+j) (by simp [height] at *; omega) := by
--   simp_rw [Interchange, mul_one]
--   sorry

end A3UnipGen

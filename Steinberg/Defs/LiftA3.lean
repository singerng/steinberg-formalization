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
  | α | β | γ | αβ | βγ | αβγ

namespace A3PositiveRoot

-- CC: Adding the reducible tag lets `simp` peer into the definition,
--     so that you don't have to manually unfold it during proving.
@[reducible]
def height : A3PositiveRoot → Nat
  | α => 1
  | β => 1
  | γ => 1
  | αβ => 2
  | βγ => 2
  | αβγ => 3

def toString : A3PositiveRoot → String
  | α => "α"
  | β => "β"
  | γ => "γ"
  | αβ => "α+β"
  | βγ => "β+γ"
  | αβγ => "α+β+γ"

@[simp]
def isPresent : A3PositiveRoot → Bool
  | αβγ => false
  | _ => true

instance instToString : ToString A3PositiveRoot := ⟨toString⟩

end A3PositiveRoot

structure A3UnipGen (R : Type Tv) [Ring R] where
  ζ : A3PositiveRoot -- really, this should only be allowed to be present...
  i : Deg ζ.height
  t : R

namespace A3UnipGen

open A3PositiveRoot

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
  | `($x +' $y) => `(⟨($x).val + ($y).val, by first | trivial | omega | simp [height] at *; omega⟩)

-- "{αβγ t i}" -> ⁅ |α, i, t1|, |βγ, (1 : R), i2| ⁆

def split_deg3 (i : Deg 3) : (Deg 1) × (Deg 2) :=
  match i with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (1, 2)

-- theorem split_deg3_sum (i : Deg 3) :
--   let (i₁, i₂) := split_deg3 i
--   i.val = i₁.val + i₂.val := by
--   match i with
--   | 0 => omega
--   | 1 => omega
--   | 2 => omega
--   | 3 => omega
--   done

def mkOf (ζ : A3PositiveRoot) (i : Deg ζ.height) (t : R) : FreeGroup (A3UnipGen R) :=
  match ζ with
    | αβγ =>
      let (i₁, i₂) := split_deg3 i
      ⁅ mkOf α i₁ t, mkOf βγ i₂ (1 : R) ⁆
    | ζ => FreeGroup.of <| mk ζ i t
termination_by ζ.height

/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation "{" ζ ", " i ", " t "}" => A3UnipGen.mkOf ζ i t

/--
  Additional shorthand for building free group elements from a root, degree, and ring element.

  CC: It turns out that both `{ }` and `( )` are "reserved syntax" by Lean, and so
      it can't make up its mind if you use things that are also reserved for
      (Fin)sets and Prods. Thus, if you get an "ambiguous, possible interpretations"
      error, you can fall back on using the pipe character '|' to wrap the triple.
-/
scoped notation "|" ζ ", " i ", " t "|" => A3UnipGen.mkOf ζ i t

/-
open Lean in
set_option hygiene false in
macro "declare_trivial_commutator" rootOne:ident rootTwo:ident : command => do
  let thmName := ($rootOne : A3PositiveRoot).toString ++ "_comm_" ++ ($rootTwo : A3PositiveRoot).toString
  let mut cmds ← Syntax.getArgs <$> `(
    def $thmName (R : Type Tv) [Ring R] :=
      ∀ (t u : R) (i : Deg $rootOne.height) (j : Deg $rootTwo.height),
        ⁅ { $rootOne, i, t }, { $rootTwo, j, u } ⁆ = 1
  )
  return (mkNullNode cmds) -/

-- types of statements which we assume or want to prove about roots...
abbrev trivial_commutator_of_root_pair (ζ η : A3PositiveRoot) (R : Type Tv) [Ring R] : Prop :=
  ∀ (t u : R) (i : Deg ζ.height) (j : Deg η.height),
    TrivialCommutatorProp {ζ, i, t} {η, j, u}

abbrev linearity_of_root (ζ : A3PositiveRoot) (R : Type Tv) [Ring R] : Prop :=
  ∀ (t u : R) (i : Deg ζ.height), {ζ, i, t} * {ζ, i, u} = {ζ, i, t+u}

abbrev id_of_root (ζ : A3PositiveRoot) (R : Type Tv) [Ring R] : Prop :=
  ∀ (i : Deg ζ.height), {ζ, i, (0 : R)} = 1

abbrev inv_of_root (ζ : A3PositiveRoot) (R : Type Tv) [Ring R] : Prop :=
  ∀ (t : R) (i : Deg ζ.height), {ζ, i, -t} = {ζ, i, t}⁻¹

-- assumptions
-- trivial commutators
def β_comm_αβ  := trivial_commutator_of_root_pair β αβ
def γ_comm_βγ  := trivial_commutator_of_root_pair γ βγ
def α_comm_γ   := trivial_commutator_of_root_pair α γ
def αβ_comm_βγ := trivial_commutator_of_root_pair αβ βγ

-- linearity
def lin_of_present (R : Type Tv) [Ring R] : Prop := ∀ (ζ : A3PositiveRoot) (i : Deg ζ.height),
  -- ζ.isPresent →
  linearity_of_root ζ R

-- nontrivial commutators
def α_comm_β (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg α.height) (j : Deg β.height),
 ⁅ {α, i, t}, {β, j, u} ⁆ = |αβ, (i +' j), (t * u)|

def β_comm_γ (R : Type Tv) [Ring R] := ∀ (t u : R) (i : Deg β.height) (j : Deg γ.height),
 ⁅ {β, i, t}, {γ, j, u} ⁆ = |βγ, (i +' j), (t * u)|

structure WeakA3 (R : Type Tv) [Ring R] where
  h_lin : lin_of_present R
  h_α_β : α_comm_β R
  h_β_γ : β_comm_γ R
  h_α_γ : α_comm_γ R
  h_β_αβ : β_comm_αβ R
  h_γ_βγ : γ_comm_βγ R
  h_αβ_βγ : αβ_comm_βγ R

/- analysis of the group -/
-- deduce identity relations from linearity relations
@[simp]
theorem id_of_present (h : WeakA3 R) (ζ : A3PositiveRoot) (i : Deg ζ.height) :
    ζ.isPresent →
    id_of_root ζ R := by
  sorry

-- deduce inverse relations from linearity relations
@[simp]
theorem inv_of_present (h : WeakA3 R) (ζ : A3PositiveRoot) (i : Deg ζ.height) :
    ζ.isPresent →
    inv_of_root ζ R := by
  sorry

-- explicit expressions of commutators
@[simp]
theorem expr_βγ_as_β_comm_γ (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg γ.height) :
    |βγ, (i +' j), (t*u)| = {β, i, t} * {γ, j, u} * {β, i, (-t)} * {γ, j, (-u)} := by
  -- have : β.isPresent := rfl
  have := inv_of_present h i --this
  simp [this]
  -- have : γ.isPresent := rfl
  have := inv_of_present h j --this
  simp [this]
  rw [← commutatorElement_def]
  rw [← h.h_β_γ t u i j]
  done

-- rewrites for products of noncommuting elements
@[simp]
theorem expr_α_β_as_αβ_β_α (h : WeakA3 R) (t u : R) (i : Deg α.height) (j : Deg β.height) :
    ReorderLeftProp {α, i, t} {β, j, u} |αβ, (i +' j), (t*u)| := by
  rw [← h.h_α_β]
  rw [ReorderLeftProp]
  rw [comm_left_str]
  done

@[simp]
theorem expr_β_γ_as_βγ_γ_β (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg γ.height) :
    ReorderLeftProp {β, i, t} {γ, j, u} |βγ, (i +' j), (t*u)| := by
  rw [← h.h_β_γ]
  rw [ReorderLeftProp]
  rw [comm_left_str]
  done

-- rewrites for products of commuting elements
@[simp]
theorem expr_α_γ_as_γ_α (h : WeakA3 R) (t u : R) (i : Deg α.height) (j : Deg γ.height) :
    CommutesProp {α, i, t} {γ, j, u} := by
  apply comm_to_comm
  rw [h.h_α_γ]

@[simp]
theorem expr_β_αβ_as_αβ_β (h : WeakA3 R) (t u : R) (i : Deg β.height) (j : Deg αβ.height) :
    CommutesProp {β, i, t} {αβ, j, u} := by
  apply comm_to_comm
  rw [h.h_β_αβ]

@[simp]
theorem expr_γ_βγ_as_βγ_γ (h : WeakA3 R) (t u : R) (i : Deg γ.height) (j : Deg βγ.height) :
    CommutesProp {γ, i, t} {βγ, j, u} := by
  apply comm_to_comm
  rw [h.h_γ_βγ]

@[simp]
theorem expr_αβ_βγ_as_βγ_αβ (h : WeakA3 R) (t u : R) (i : Deg αβ.height) (j : Deg βγ.height) :
    CommutesProp {αβ, i, t} {βγ, j, u} := by
  apply comm_to_comm
  rw [h.h_αβ_βγ]

-- interchange theorem, ⁅α, βγ⁆ = ⁅αβ, γ⁆
theorem Interchange (h : WeakA3 R) (t u v : R) (i : Deg α.height) (j : Deg β.height) (k : Deg γ.height) :
    ⁅ |α, i, t|, |βγ, (j +' k), (u * v)| ⁆ = ⁅ |αβ, (i +' j), (t * u)|, |γ, k, v| ⁆ := by
  apply comm_on_left
  -- phase I: push α to right
  conv =>
    lhs
    rw [expr_βγ_as_β_comm_γ h]
    simp [← mul_assoc]
    rw [expr_α_β_as_αβ_β_α h]
    rw [mul_assoc _ |α, i, t|]
    rw [expr_α_γ_as_γ_α h]
    simp [← mul_assoc]
    rw [mul_assoc _ |α, i, t|]
    rw [expr_α_β_as_αβ_β_α h]
    rw [mul_neg] -- rewrite t*(-u) as -(t*u)
    simp [← mul_assoc]
    rw [mul_assoc _ |α, i, t|]
    rw [expr_α_γ_as_γ_α h]
    simp [← mul_assoc]
    -- phase II: move β's together
    rw [mul_assoc _ |β, j, u|]
    rw [expr_β_γ_as_βγ_γ_β h]
    simp [← mul_assoc]
    rw [mul_assoc _ |β, j, u|]
    rw [expr_β_αβ_as_αβ_β h]
    simp [← mul_assoc]
    rw [mul_assoc _ |β, j, u|]
  rw [inv_of_present h β i]
  group
  conv =>
    lhs
    -- phase III: push βγ to the right
    rw [mul_assoc _ |βγ, (j +' k), (u * v)|]
    rw [← expr_γ_βγ_as_βγ_γ h]
    simp [← mul_assoc]
    rw [mul_assoc _ |βγ, (j +' k), u * v|]
    rw [← expr_αβ_βγ_as_βγ_αβ h]
    simp [← mul_assoc]
    rw [mul_assoc _ |βγ, (j +' k), u * v|]
    rw [← expr_γ_βγ_as_βγ_γ h]
    simp [← mul_assoc]
  repeat rw [inv_of_present h αβ (i +' j)]
  repeat rw [inv_of_present h γ k]
  group
  done

end A3UnipGen

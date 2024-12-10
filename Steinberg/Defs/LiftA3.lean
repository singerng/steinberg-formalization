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
  ζ : A3PositiveRoot -- NS: really, the type checker should reject making a A3UnipGen when ζ isn't present...
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

/--
  Decompose a number `0 ≤ i ≤ n + m` into `i₁ + i₂`, where `0 ≤ i₁ ≤ n` and `0 ≤ i₂ ≤ m`.
 -/
theorem decompose (n m : ℕ) : ∀ (i : Deg (n + m)), ∃ (i₁ : Deg n) (i₂ : Deg m), i = i₁ +' i₂ := by
  intro i
  if h : i.val < n + 1 then (
    let i₁ : Deg n := ⟨ i.val, h ⟩
    let i₂ : Deg m := 0
    exists i₁
    exists i₂
  ) else (
    have id₁ : n < n + 1 := by simp;
    let i₁ : Deg n := ⟨ n, id₁ ⟩;
    have id₂ : i.val - n < m + 1 := by omega;
    let i₂ : Deg m := ⟨ i.val - n, id₂ ⟩;
    have id₃ : i₁.val + i₂.val < n + m + 1 := by omega;
    have id₄ : i = ⟨ i₁.val + i₂.val, id₃ ⟩ := by
      apply Fin.eq_of_val_eq
      simp
      omega
    exists i₁
    exists i₂
  )

-- "{αβγ t i}" -> ⁅ |α, i, t1|, |βγ, (1 : R), i2| ⁆

@[simp]
def split_deg3 (i : Deg 3) : (Deg 1) × (Deg 2) :=
  match i with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)

theorem split_deg3_sum (i : Deg 3) :
  let (i₁, i₂) := split_deg3 i
  i = i₁ +' i₂ := by
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp
  done

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
abbrev trivial_commutator_of_root_pair (R : Type Tv) [Ring R] (ζ η : A3PositiveRoot) : Prop :=
  ∀ (i : Deg ζ.height) (j : Deg η.height) (t u : R),
    TrivialCommutatorProp {ζ, i, t} {η, j, u}

abbrev single_commutator_of_root_pair (R : Type Tv) [Ring R] (ζ η θ : A3PositiveRoot)
  (C : R) (h_height : ζ.height + η.height = θ.height) : Prop :=
  ∀ (i : Deg ζ.height) (j : Deg η.height) (t u : R),
    -- CommutatorProp {ζ, i, t} {η, j, u} |θ, i +' j, C * (t * u)|
    ⁅ {ζ, i, t}, {η, j, u} ⁆ = |θ, i +' j, C * (t * u)|

abbrev linearity_of_root (R : Type Tv) [Ring R] (ζ : A3PositiveRoot) : Prop :=
  ∀ (i : Deg ζ.height) (t u : R), {ζ, i, t} * {ζ, i, u} = {ζ, i, t+u}

abbrev id_of_root (R : Type Tv) [Ring R] (ζ : A3PositiveRoot) : Prop :=
  ∀ (i : Deg ζ.height), {ζ, i, (0 : R)} = 1

abbrev inv_of_root (R : Type Tv) [Ring R] (ζ : A3PositiveRoot) : Prop :=
  ∀ (i : Deg ζ.height) (t : R), {ζ, i, -t} = {ζ, i, t}⁻¹

-- assumptions
-- trivial commutators
def α_comm_αβ  (R : Type Tv) [Ring R] := trivial_commutator_of_root_pair R α αβ
def β_comm_αβ  (R : Type Tv) [Ring R] := trivial_commutator_of_root_pair R β αβ
def β_comm_βγ  (R : Type Tv) [Ring R] := trivial_commutator_of_root_pair R β βγ
def γ_comm_βγ  (R : Type Tv) [Ring R] := trivial_commutator_of_root_pair R γ βγ
def α_comm_γ   (R : Type Tv) [Ring R] := trivial_commutator_of_root_pair R α γ

-- linearity
def lin_of_present (R : Type Tv) [Ring R] : Prop := ∀ (ζ : A3PositiveRoot),
  ζ.isPresent → linearity_of_root R ζ

-- nontrivial commutators
def α_comm_β (R : Type Tv) [Ring R] : Prop := single_commutator_of_root_pair R α β αβ 1 (by simp [height] at *)

def β_comm_γ (R : Type Tv) [Ring R] : Prop := single_commutator_of_root_pair R β γ βγ 1 (by simp [height] at *)

structure WeakA3 (R : Type Tv) [Ring R] where
  h_lin : lin_of_present R
  h_α_β : α_comm_β R
  h_β_γ : β_comm_γ R
  h_α_γ : α_comm_γ R
  h_α_αβ : α_comm_αβ R
  h_β_αβ : β_comm_αβ R
  h_β_βγ : β_comm_βγ R
  h_γ_βγ : γ_comm_βγ R
  h_αβ_βγ_nonhomog_lift : true

theorem αβ_comm_βγ (R : Type Tv) [Ring R] : trivial_commutator_of_root_pair R αβ βγ := by
  sorry

/- analysis of the group -/
-- deduce identity relations from linearity relations
@[simp]
theorem id_of_present (h : WeakA3 R) (ζ : A3PositiveRoot) :
    ζ.isPresent → id_of_root R ζ := by
  intro h_pres i
  apply @mul_left_cancel _ _ _ {ζ, i, 0}
  rw [mul_one, h.h_lin, add_zero]
  exact h_pres
  done

-- deduce inverse relations from linearity relations
@[simp]
theorem inv_of_present (h : WeakA3 R) (ζ : A3PositiveRoot):
    ζ.isPresent → inv_of_root R ζ := by
  intro h_pres i t
  apply @mul_left_cancel _ _ _ {ζ, i, t}
  group
  rw [h.h_lin]
  rw [add_neg_cancel]
  apply id_of_present h
  exact h_pres
  exact h_pres
  done

-- explicit expressions of commutators
@[simp]
theorem expr_βγ_as_β_γ_β_γ (h : WeakA3 R) :
    ∀ (i : Deg β.height) (j : Deg γ.height) (t u : R),
      |βγ, (i +' j), (t * u)| = {β, i, t} * {γ, j, u} * {β, i, (-t)} * {γ, j, (-u)} := by
  intro i j t u
  rw [inv_of_present h β]
  rw [inv_of_present h γ]
  rw [← commutatorElement_def]
  rw [← one_mul (t * u)]
  rw [← h.h_β_γ]
  repeat simp
  done

-- rewrites for products of noncommuting elements
@[simp]
theorem expr_α_β_as_αβ_β_α (h : WeakA3 R) :
    ∀ (i : Deg α.height) (j : Deg β.height) (t u : R),
      ReorderLeftProp {α, i, t} {β, j, u} |αβ, (i +' j), (t*u)| := by
  intro i j t u
  rw [← one_mul (t * u)]
  rw [← h.h_α_β]
  rw [ReorderLeftProp]
  rw [comm_left_str]
  done

@[simp]
theorem expr_β_γ_as_βγ_γ_β (h : WeakA3 R)  :
    ∀ (i : Deg β.height) (j : Deg γ.height) (t u : R), ReorderLeftProp {β, i, t} {γ, j, u} |βγ, (i +' j), (t*u)| := by
  intro i j t u
  rw [← one_mul (t * u)]
  rw [← h.h_β_γ]
  rw [ReorderLeftProp]
  rw [comm_left_str]
  done

-- rewrites for products of commuting elements
theorem expr_α_γ_as_γ_α (h : WeakA3 R)  :
    ∀ (i : Deg α.height) (j : Deg γ.height) (t u : R), CommutesProp {α, i, t} {γ, j, u} := by
  intro i j t u
  apply trivial_comm_to_commutes
  rw [h.h_α_γ]

theorem expr_α_αβ_as_αβ_α (h : WeakA3 R) :
    ∀ (i : Deg α.height) (j : Deg αβ.height) (t u : R), CommutesProp {α, i, t} {αβ, j, u} := by
  intro i j t u
  apply trivial_comm_to_commutes
  rw [h.h_α_αβ]

theorem expr_β_αβ_as_αβ_β (h : WeakA3 R) :
    ∀ (i : Deg β.height) (j : Deg αβ.height) (t u : R), CommutesProp {β, i, t} {αβ, j, u} := by
  intro i j t u
  apply trivial_comm_to_commutes
  rw [h.h_β_αβ]

theorem expr_γ_βγ_as_βγ_γ (h : WeakA3 R) :
    ∀ (i : Deg γ.height) (j : Deg βγ.height) (t u : R), CommutesProp {γ, i, t} {βγ, j, u} := by
  intro i j t u
  apply trivial_comm_to_commutes
  rw [h.h_γ_βγ]

theorem expr_αβ_βγ_as_βγ_αβ :
  ∀ (i : Deg αβ.height) (j : Deg βγ.height) (t u : R), CommutesProp {αβ, i, t} {βγ, j, u} := by
  intro i j t u
  apply trivial_comm_to_commutes
  rw [αβ_comm_βγ]

-- interchange theorem, ⁅α, βγ⁆ = ⁅αβ, γ⁆
theorem Interchange (h : WeakA3 R) (i : Deg α.height) (j : Deg β.height) (k : Deg γ.height) :
    ∀ (t u v : R), ⁅ |α, i, t|, |βγ, (j +' k), (u * v)| ⁆ = ⁅ |αβ, (i +' j), (t * u)|, |γ, k, v| ⁆ := by
  intro t u v
  apply comm_on_left
  -- phase I: push α to right
  conv =>
    lhs
    rw [expr_βγ_as_β_γ_β_γ h]
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
  nth_rewrite 2 [inv_of_present h]
  group
  conv =>
    lhs
    -- phase III: push βγ to the right
    rw [mul_assoc _ |βγ, (j +' k), (u * v)|]
    rw [← expr_γ_βγ_as_βγ_γ h]
    simp [← mul_assoc]
    rw [mul_assoc _ |βγ, (j +' k), u * v|]
    rw [← expr_αβ_βγ_as_βγ_αβ]
    simp [← mul_assoc]
    rw [mul_assoc _ |βγ, (j +' k), u * v|]
    rw [← expr_γ_βγ_as_βγ_γ h]
    simp [← mul_assoc]
    repeat rw [inv_of_present h]
  group
  simp
  done

/-- the whopper: establishing an "αβγ" element as either ⁅α,βγ⁆ or ⁅αβ,γ⁆ -/

theorem InterchangeTrans (h : WeakA3 R) (i : Deg α.height) (j : Deg β.height) (k : Deg γ.height) :
    ∀ (t u : R), ⁅ |α, i, t|, |βγ, (j +' k), u| ⁆ = ⁅ |αβ, (i +' j), t|, |γ, k, u| ⁆ := by
  intro t u
  nth_rewrite 1 [← one_mul u]
  nth_rewrite 2 [← mul_one t]
  rw [Interchange h]
  done

theorem InterchangeRefl (h : WeakA3 R) (i : Deg α.height) (j : Deg β.height) (k : Deg γ.height) :
    ∀ (t u : R), ⁅ |α, i, 1 * (t * u)|, |βγ, (j +' k), 1| ⁆ = ⁅ |α, i, t|, |βγ, (j +' k), u| ⁆ := by
  intro t u
  nth_rewrite 2 [← mul_one u]
  rw [Interchange h]
  rw [InterchangeTrans h]
  rw [one_mul]
  done

theorem id₀₀ : (0 : Deg 2) = (0 : Deg 1) +' (0 : Deg 1) := by simp
theorem id₀₁ : (1 : Deg 2) = (0 : Deg 1) +' (1 : Deg 1) := by simp
theorem id₁₀ : (1 : Deg 2) = (1 : Deg 1) +' (0 : Deg 1) := by simp
theorem id₁₁ : (2 : Deg 2) = (1 : Deg 1) +' (1 : Deg 1) := by simp

-- height 0
theorem comm_α_βγ_00 (h : WeakA3 R) (t u : R) : ⁅ {α, 0, t}, {βγ, 0, u} ⁆ = |αβγ, (0 : Deg 1) +' (0 : Deg 2), 1*(t*u)| := by
  nth_rewrite 1 [id₀₀]
  rw [← InterchangeRefl h (0 : Deg 1) (0 : Deg 1) (0 : Deg 1)]
  simp [mkOf]
theorem comm_αβ_γ_00 (h : WeakA3 R) (t u : R) : ⁅ {αβ, 0, t}, {γ, 0, u} ⁆ = |αβγ, (0 : Deg 2) +' (0 : Deg 0), 1*(t*u)| := by
  nth_rewrite 1 [id₀₀]
  rw [← InterchangeTrans h (0 : Deg 1) (0 : Deg 1) (0 : Deg 1)]
  simp [height]
  rw [comm_α_βγ_00 h]
  simp [height]

-- height 1
theorem comm_α_βγ_01 (h : WeakA3 R) (t u : R) : ⁅ {α, 0, t}, {βγ, 1, u} ⁆ = |αβγ, (0 : Deg 1) +' (1 : Deg 2), 1*(t*u)| := by
  nth_rewrite 1 [id₀₁]
  rw [← InterchangeRefl h (0 : Deg 1) (0 : Deg 1) (1 : Deg 1)]
  simp [mkOf]
theorem comm_αβ_γ_10 (h : WeakA3 R) (t u : R) : ⁅ {αβ, 1, t}, {γ, 0, u} ⁆ = |αβγ, (1 : Deg 2) +' (0 : Deg 0), 1*(t*u)| := by
  nth_rewrite 1 [id₀₁]
  rw [← InterchangeTrans h (0 : Deg 1) (1 : Deg 1) (0 : Deg 1)]
  simp [height]
  rw [comm_α_βγ_01 h]
  simp [height]
theorem comm_α_βγ_10 (h : WeakA3 R) (t u : R) : ⁅ {α, 1, t}, {βγ, 0, u} ⁆ = |αβγ, (1 : Deg 1) +' (0 : Deg 2), 1*(t*u)| := by
  nth_rewrite 1 [id₀₀]
  rw [InterchangeTrans h (1 : Deg 1) (0 : Deg 1) (0 : Deg 1)]
  simp [height]
  rw [comm_αβ_γ_10 h]
  simp [height]
theorem comm_αβ_γ_01 (h : WeakA3 R) (t u : R) : ⁅ {αβ, 0, t}, {γ, 1, u} ⁆ = |αβγ, (0 : Deg 2) +' (1 : Deg 1), 1*(t*u)| := by
  nth_rewrite 1 [id₀₀]
  rw [← InterchangeTrans h (0 : Deg 1) (0 : Deg 1) (1 : Deg 1)]
  simp [height]
  rw [comm_α_βγ_01 h]
  simp [height]

-- height 2
theorem comm_α_βγ_11 (h : WeakA3 R) (t u : R) : ⁅ {α, 1, t}, {βγ, 1, u} ⁆ = |αβγ, (1 : Deg 1) +' (1 : Deg 2), 1*(t*u)| := by
  nth_rewrite 1 [id₀₁]
  rw [← InterchangeRefl h (1 : Deg 1) (0 : Deg 1) (1 : Deg 1)]
  simp [mkOf]
theorem comm_αβ_γ_11 (h : WeakA3 R) (t u : R) : ⁅ {αβ, 1, t}, {γ, 1, u} ⁆ = |αβγ, (1 : Deg 2) +' (1 : Deg 1), 1*(t*u)| := by
  nth_rewrite 1 [id₁₀]
  rw [← InterchangeTrans h (1 : Deg 1) (0 : Deg 1) (1 : Deg 1)]
  simp [height]
  rw [comm_α_βγ_11 h]
  simp [height]
theorem comm_α_βγ_02 (h : WeakA3 R) (t u : R) : ⁅ {α, 0, t}, {βγ, 2, u} ⁆ = |αβγ, (0 : Deg 1) +' (2 : Deg 2), 1*(t*u)|:= by
  nth_rewrite 1 [id₁₁]
  rw [InterchangeTrans h (0 : Deg 1) (1 : Deg 1) (1 : Deg 1)]
  simp [height]
  rw [comm_αβ_γ_11 h]
  simp [height]
theorem comm_αβ_γ_20 (h : WeakA3 R) (t u : R) : ⁅ {αβ, 2, t}, {γ, 0, u} ⁆ = |αβγ, (2 : Deg 2) +' (0 : Deg 1), 1*(t*u)| := by
  nth_rewrite 1 [id₁₁]
  rw [← InterchangeTrans h (1 : Deg 1) (1 : Deg 1) (0 : Deg 1)]
  simp [height]
  rw [comm_α_βγ_11 h]
  simp [height]

-- height 3
theorem comm_α_βγ_12 (h : WeakA3 R) (t u : R) : ⁅ {α, 1, t}, {βγ, 2, u} ⁆ = |αβγ, (1 : Deg 1) +' (2 : Deg 2), 1*(t*u)| := by
  nth_rewrite 1 [id₁₁]
  rw [← InterchangeRefl h (1 : Deg 1) (1 : Deg 1) (1 : Deg 1)]
  simp [mkOf]
  simp [height]
theorem comm_αβ_γ_21 (h : WeakA3 R) (t u : R) : ⁅ {αβ, 2, t}, {γ, 1, u} ⁆ = |αβγ, (2 : Deg 2) +' (1 : Deg 1), 1*(t*u)| := by
  nth_rewrite 1 [id₁₁]
  rw [← InterchangeTrans h (1 : Deg 1) (1 : Deg 1) (1 : Deg 1)]
  simp [height]
  rw [comm_α_βγ_12 h]
  simp [height]

theorem comm_α_βγ (h : WeakA3 R) : single_commutator_of_root_pair R α βγ αβγ 1 (by simp [height] at *) := by
  intro i j t u
  match i, j with
  | 0, 0 => exact comm_α_βγ_00 h t u
  | 0, 1 => exact comm_α_βγ_01 h t u
  | 0, 2 => exact comm_α_βγ_02 h t u
  | 1, 0 => exact comm_α_βγ_10 h t u
  | 1, 1 => exact comm_α_βγ_11 h t u
  | 1, 2 => exact comm_α_βγ_12 h t u

theorem comm_αβ_γ (h : WeakA3 R) : single_commutator_of_root_pair R αβ γ αβγ 1 (by simp [height] at *) := by
  intro i j t u
  match i, j with
  | 0, 0 => exact comm_αβ_γ_00 h t u
  | 1, 0 => exact comm_αβ_γ_10 h t u
  | 2, 0 => exact comm_αβ_γ_20 h t u
  | 0, 1 => exact comm_αβ_γ_01 h t u
  | 1, 1 => exact comm_αβ_γ_11 h t u
  | 2, 1 => exact comm_αβ_γ_21 h t u

/-- we're cooking.... -/
theorem expr_αβγ_as_α_βγ_α_βγ (h : WeakA3 R) :
    ∀ (i : Deg α.height) (j : Deg βγ.height) (t u : R),
      |αβγ, (i +' j), (t * u)| = {α, i, t} * {βγ, j, u} * {α, i, (-t)} * {βγ, j, (-u)} := by
  intro i j t u
  rw [inv_of_present h α]
  rw [inv_of_present h βγ]
  rw [← commutatorElement_def]
  rw [← one_mul (t * u)]
  rw [← comm_α_βγ h]
  repeat simp
  done

theorem expr_αβγ_as_αβ_γ_αβ_γ (h : WeakA3 R) :
    ∀ (i : Deg αβ.height) (j : Deg γ.height) (t u : R),
      |αβγ, (i +' j), (t * u)| = {αβ, i, t} * {γ, j, u} * {αβ, i, (-t)} * {γ, j, (-u)} := by
  intro i j t u
  rw [inv_of_present h αβ]
  rw [inv_of_present h γ]
  rw [← commutatorElement_def]
  rw [← one_mul (t * u)]
  rw [← comm_αβ_γ h]
  repeat simp
  done

/- simple proof: we know αβγ is expressible as a product of αβ's and γ's (expr_αβγ_as_αβ_γ_αβ_γ), and we know that α's
   commute with αβ's (expr_α_αβ_as_αβ_α) and γ's (expr_α_γ_as_γ_α) -/
theorem comm_α_αβγ (R : Type Tv) [Ring R] (h : WeakA3 R) : trivial_commutator_of_root_pair R α αβγ := by
  intro i j t u
  apply commutes_to_trivial_comm
  let ⟨ j₁, j₂, id ⟩ := (decompose αβ.height γ.height j)
  rw [id]
  rw [← one_mul u]
  rw [expr_αβγ_as_αβ_γ_αβ_γ h]
  mul_assoc_l
  rw [expr_α_αβ_as_αβ_α h]
  rw [mul_assoc _ |α, i, t|]
  rw [expr_α_γ_as_γ_α h]
  mul_assoc_l
  rw [mul_assoc _ |α, i, t|]
  rw [expr_α_αβ_as_αβ_α h]
  mul_assoc_l
  rw [mul_assoc _ |α, i, t|]
  rw [expr_α_γ_as_γ_α h]
  mul_assoc_l

theorem comm_γ_αβγ (R : Type Tv) [Ring R] (h : WeakA3 R) : trivial_commutator_of_root_pair R γ αβγ := by
  intro i j t u
  apply commutes_to_trivial_comm
  let ⟨ j₁, j₂, id ⟩ := (decompose α.height βγ.height j)
  rw [id]
  rw [← one_mul u]
  rw [expr_αβγ_as_α_βγ_α_βγ h]
  mul_assoc_l
  rw [← expr_α_γ_as_γ_α h]
  rw [mul_assoc _ |γ, i, t|]
  rw [expr_γ_βγ_as_βγ_γ h]
  mul_assoc_l
  rw [mul_assoc _ |γ, i, t|]
  rw [← expr_α_γ_as_γ_α h]
  mul_assoc_l
  rw [mul_assoc _ |γ, i, t|]
  rw [expr_γ_βγ_as_βγ_γ h]
  mul_assoc_l

theorem comm_β_αβγ (R : Type Tv) [Ring R] (h : WeakA3 R) : trivial_commutator_of_root_pair R β αβγ := by
  sorry

theorem comm_αβ_αβγ (R : Type Tv) [Ring R] (h : WeakA3 R) : trivial_commutator_of_root_pair R αβ αβγ := by
  sorry

theorem comm_βγ_αβγ (R : Type Tv) [Ring R] (h : WeakA3 R) : trivial_commutator_of_root_pair R βγ αβγ := by
  sorry

theorem comm_αβγ_αβγ (R : Type Tv) [Ring R] (h : WeakA3 R) : trivial_commutator_of_root_pair R αβγ αβγ := by
  sorry

theorem expr_α_αβγ_as_αβγ_α (h : WeakA3 R) :
    ∀ (i : Deg α.height) (j : Deg αβγ.height) (t u : R), CommutesProp {α, i, t} {αβγ, j, u} := by
  intro i j t u
  apply trivial_comm_to_commutes
  rw [comm_α_αβγ R h]

theorem expr_βγ_αβγ_as_αβγ_βγ (h : WeakA3 R) :
    ∀ (i : Deg βγ.height) (j : Deg αβγ.height) (t u : R), CommutesProp {βγ, i, t} {αβγ, j, u} := by
  intro i j t u
  apply trivial_comm_to_commutes
  rw [comm_βγ_αβγ R h]

theorem lin_αβγ (R : Type Tv) [Ring R] (h : WeakA3 R) : linearity_of_root R αβγ := by
  intro i t u
  let ⟨ i₁, i₂, id ⟩ := (decompose α.height βγ.height i)
  rw [id]
  nth_rewrite 1 [← mul_one t]
  rw [expr_αβγ_as_α_βγ_α_βγ h]
  rw [mul_assoc _ _ |αβγ, i₁ +' i₂, u|]
  rw [expr_βγ_αβγ_as_αβγ_βγ h]
  mul_assoc_l
  rw [mul_assoc _ _ |αβγ, i₁ +' i₂, u|]
  rw [expr_α_αβγ_as_αβγ_α h]
  mul_assoc_l
  rw [mul_assoc _ _ |αβγ, i₁ +' i₂, u|]
  rw [expr_βγ_αβγ_as_αβγ_βγ h]
  mul_assoc_l
  nth_rewrite 1 [← mul_one u]
  rw [expr_αβγ_as_α_βγ_α_βγ h]
  mul_assoc_l
  rw [h.h_lin]
  nth_rewrite 1 [inv_of_present h βγ]
  group
  rw [mul_assoc _ |α, i₁, -u|]
  rw [h.h_lin]
  have rid : -u + -t = -(t+u) := by simp
  rw [rid]
  rw [← expr_αβγ_as_α_βγ_α_βγ h]
  simp [height] at *
  repeat simp [isPresent] at *

end A3UnipGen

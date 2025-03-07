/-

LICENSE goes here.

-/

import Steinberg.Defs.WeakChevalley
import Mathlib.Tactic.DeriveFintype

/-!

  File dox.

-/

namespace Steinberg.B3Small

/-! ### Defining the B3 small positive root system -/

inductive B3SmallPosRoot
  | β | ψ | ω | βψ | ψω | β2ψ | βψω
deriving Fintype, DecidableEq, Inhabited

namespace B3SmallPosRoot

@[reducible, height_simps]
def height : B3SmallPosRoot → Nat
  | β | ψ | ω => 1
  | βψ | ψω => 2
  | βψω | β2ψ => 3

def toString : B3SmallPosRoot → String
  | β => "β"
  | ψ => "ψ"
  | ω => "ω"
  | βψ => "β+ψ"
  | ψω => "ψ+ω"
  | βψω => "β+ψ+ω"
  | β2ψ => "β+2ψ"

instance : PosRootSys B3SmallPosRoot where
  height := height
  toString := toString

instance instCoeNat : Coe B3SmallPosRoot Nat where
  coe r := height r

end B3SmallPosRoot

open B3SmallPosRoot GradedGen

variable {F : Type TR} [Field F]

/-! # Relations -/

/-
The specific relation arises from "nonhomogeneously lifting" the commutator of βψ and ψω elements. (There is no analogue
of this relation for other root-pairs, since all other present pairs lie in a common two-dimensional subspace.)
-/
def rels_of_nonhomog_lift_of_comm_of_βψ_ψω :=
   { ⁅ {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀},
       {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} ⁆
     | (t₁ : F) (t₀ : F) (u₁ : F) (u₀ : F) (v₁ : F) (v₀ : F) }

def split_3_into_1_2 (i : ℕ) (hi : i ≤ 3) :=
  match i with
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (1, 2)

theorem correct_of_split_3_into_1_2 (i : ℕ) (hi : i ≤ 3) :
  (split_3_into_1_2 i hi).1 ≤ 1 ∧ (split_3_into_1_2 i hi).2 ≤ 2 := by
  simp only [split_3_into_1_2]
  split
  all_goals trivial

-- There's also an alternative definition for βψω

def rels_of_def_of_βψω :=
  { ⁅ {β, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1,
      {ψω, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 ⁆
      * {βψω, i, t}⁻¹
    | (i : ℕ) (hi : i ≤ βψω.height) (t : F) }

abbrev trivial_commutator_pairs : Set (B3SmallPosRoot × B3SmallPosRoot) :=
  {(β, βψ), (β, β2ψ), (ψ, β2ψ), (βψ, β2ψ), (β, ω), (ψ, ψω), (ω, ψω)}

abbrev single_commutator_pairs : Set ((ζ : B3SmallPosRoot) × (η : B3SmallPosRoot) × (θ : B3SmallPosRoot) × F ×' (θ.height = ζ.height + η.height))
   := {⟨ ψ, βψ, β2ψ, 2, (by simp only [height])⟩, ⟨ψ, ω, ψω, 2, (by simp only [height])⟩}

/-! # These are the self-commutation relations -/

abbrev mixed_commutes_roots : Set (B3SmallPosRoot) := {β, ψ, ω, βψ, ψω, β2ψ}

abbrev lin_roots : Set (B3SmallPosRoot) := {β, ψ, ω, βψ, ψω, β2ψ}

abbrev double_commutator_pairs : Set (DoubleSpanRootPair B3SmallPosRoot F) :=
    {⟨β, ψ, βψ, β2ψ, 1, 1, (by exact rfl), (by exact rfl)⟩}

-- lifted commutator of βψ and ψω
def lifted_sets (F : Type TR) [Field F] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot F)) := {
  rels_of_nonhomog_lift_of_comm_of_βψ_ψω
}

-- definition of βψω
def def_sets (F : Type TR) [Field F] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot F)) := {
  rels_of_def_of_βψω
}

def weakB3Small (F : Type TR) [Field F] := WeakChevalley.mk
  trivial_commutator_pairs
  single_commutator_pairs
  double_commutator_pairs
  mixed_commutes_roots
  lin_roots
  (lifted_sets F)
  (def_sets F)

/-! # Notation and macros -/

/- Instantiate the `declare_thms` macros from `WeakChevalley.lean`. -/

-- CC: TODO: Make this a macro to declare all at once for A3.
--     Something like: `declare_thms A3 weakB3Small F`

macro "declare_B3Small_triv_expr_thm" F:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_expr_thm weakB3Small $F $r₁ $r₂)

macro "declare_B3Small_triv_comm_of_root_pair_thms" F:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_comm_of_root_pair_thms weakB3Small $F $r₁ $r₂)

macro "declare_B3Small_single_expr_thms" F:term:arg r₁:term:arg r₂:term:arg r₃:term:arg n:num : command =>
  `(command| declare_single_expr_thms weakB3Small $F $r₁ $r₂ $r₃ $n)

macro "declare_B3Small_single_comm_of_root_pair_thms" F:term:arg r₁:term:arg r₂:term:arg r₃:term:arg n:num : command =>
  `(command| declare_single_comm_of_root_pair_thms weakB3Small $F $r₁ $r₂ $r₃ $n)

macro "declare_B3Small_lin_id_inv_thms" F:term:arg root:term:arg : command =>
  `(command| declare_lin_id_inv_thms weakB3Small $F $root)

macro "declare_B3Small_mixed_expr_thm" F:term:arg r:term:arg : command =>
  `(command| declare_mixed_expr_thm weakB3Small $F $r)

macro "declare_B3Small_mixed_comm_thms" F:term:arg r:term:arg : command =>
  `(command| declare_mixed_comm_thms weakB3Small $F $r)

-- r₁ is the larger root, as opposed to the above macros
macro "declare_B3Small_reflected_thm"
    F:term:arg v:term:arg r₁:term:arg r₂:term:arg r₃:term:arg
    "const" C:num
    "heights" n₁:num n₂:num n₃:num
    "to" n₄:num n₅:num n₆:num : command =>
  `(command| declare_reflected_thm weakB3Small $F $v $r₁ $r₂ $r₃ 0 $C $n₁ $n₂ $n₃ $n₄ $n₅ $n₆)

macro "declare_B3Small_triv_comm_reflected_thm"
    F:term:arg v:term:arg r₁:term:arg r₂:term:arg
    "heights" n₁:num n₂:num
    "to" n₃:num n₄:num : command =>
  `(command| declare_triv_comm_reflected_thm weakB3Small $F $v $r₁ $r₂ $n₁ $n₂ $n₃ $n₄)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" =>
  (weakB3Small F).pres_mk (free_mk_mk ζ i (by ht) t)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}'" h:max =>
  (weakB3Small F).pres_mk (free_mk_mk ζ i h t)

section forallNotation

set_option hygiene false

scoped notation "forall_i_t" h:max "," e =>
  ∀ ⦃i : ℕ⦄ (hi : i ≤ h) (t : F), e

scoped notation "forall_ij_tu" h₁:max h₂:max "," e =>
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ h₁) (hk : j ≤ h₂) (t u : F), e

scoped notation "forall_ik_tuv" h₁:max h₂:max "," e =>
  ∀ ⦃i k : ℕ⦄ (hi : i ≤ h₁) (hk : k ≤ h₂) (t u v : F), e

scoped notation "forall_ijk_tu" h₁:max h₂:max h₃:max "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ h₁) (hj : j ≤ h₂) (hk : k ≤ h₃) (t u : F), e

scoped notation "forall_ijk_tuv" h₁:max h₂:max h₃:max "," e =>
  ∀ ⦃i j k : ℕ⦄ (hi : i ≤ h₁) (hj : j ≤ h₂) (hk : k ≤ h₃) (t u v : F), e

end forallNotation

macro "hom_tac " rel:ident " [" intros:ident,* "]" : tactic => `(tactic|
  ( intros $intros*;
    apply WeakChevalley.helper;
    apply (weakB3Small _).lifted_helper $rel;
    simp only [weakB3Small, lifted_sets, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or, or_true];
    exists $intros,* ))

end Steinberg.B3Small

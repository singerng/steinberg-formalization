/-

LICENSE goes here.

-/

import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype

import Steinberg.Defs.Deg
import Steinberg.Defs.Commutator
import Steinberg.Defs.ReflDeg

import Steinberg.Upstream.FreeGroup

/-!

  File dox go here.

-/

namespace Steinberg

open Steinberg.Macro

variable {F : Type TR} [Field F]

/-! ### Defining the B3 small positive root system -/

inductive B3SmallPosRoot
  | β | ψ | ω | βψ | ψω | β2ψ | βψω
deriving Fintype, DecidableEq

namespace B3SmallPosRoot

@[reducible]
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

end B3SmallPosRoot

namespace B3SmallProof

open B3SmallPosRoot GradedGen ReflDeg

/-! ### Bundle together assumptions about the B3 small generators -/

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

-- Don't know yet which category does relation 8.2 fit into

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
def nonhomog_sets (F : Type TR) [Field F] : Set (Set (FreeGroupOnGradedGens B3SmallPosRoot F)) := {
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
  (nonhomog_sets F)
  (def_sets F)

/- Instantiate the `declare_thms` macros from `WeakChevalley.lean`. -/

-- CC: TODO: Make this a macro to declare all at once for A3.
--     Something like: `declare_thms A3 weakA3 R`

macro "declare_B3Small_triv_comm_of_root_pair_thms" r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_comm_of_root_pair_thms weakB3Small F $r₁ $r₂)

macro "declare_B3Small_single_comm_of_root_pair_thms" r₁:term:arg r₂:term:arg r₃:term:arg : command =>
  `(command| declare_single_comm_of_root_pair_thms weakB3Small F $r₁ $r₂ $r₃ 2)

macro "declare_B3Small_lin_id_inv_thms" root:term:arg : command =>
  `(command| declare_lin_id_inv_thms weakB3Small F $root)

macro "declare_B3Small_expr_as_thm" r₁:term:arg r₂:term:arg : command =>
  `(command| declare_expr_as_thm weakB3Small F $r₁ $r₂)

macro "declare_B3Small_mixed_comm_thms" r:term:arg : command =>
  `(command| declare_mixed_comm_thms weakB3Small F $r)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" =>
  (weakB3Small F).pres_mk (free_mk_mk ζ i (by
    try simp only [PosRootSys.height] at *
    try simp only [B3SmallPosRoot.height] at *; first | trivial | omega) t)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}'" h =>
  (weakB3Small F).pres_mk (free_mk_mk ζ i h t)

abbrev WeakChevalleyB3SmallGroup (F : Type TR) [Field F] :=
  PresentedGroup (weakB3Small F).all_rels

section UnpackingPresentation

declare_B3Small_triv_comm_of_root_pair_thms β βψ
declare_B3Small_triv_comm_of_root_pair_thms β β2ψ
declare_B3Small_triv_comm_of_root_pair_thms ψ β2ψ
declare_B3Small_triv_comm_of_root_pair_thms βψ β2ψ
declare_B3Small_triv_comm_of_root_pair_thms β ω
declare_B3Small_triv_comm_of_root_pair_thms ψ ψω
declare_B3Small_triv_comm_of_root_pair_thms ω ψω

declare_B3Small_single_comm_of_root_pair_thms ψ ω ψω
declare_B3Small_single_comm_of_root_pair_thms ψ βψ β2ψ

/-! ### Linearity theorems for specific roots -/
/-! ### Identity theorems : 8.25 - 8.30 -/
/-! ### Inverse theorems - 8.31 - 8.36 -/

declare_B3Small_lin_id_inv_thms β
declare_B3Small_lin_id_inv_thms ψ
declare_B3Small_lin_id_inv_thms ω
declare_B3Small_lin_id_inv_thms βψ
declare_B3Small_lin_id_inv_thms ψω
declare_B3Small_lin_id_inv_thms β2ψ

/-! ### Mixed-degree theorem for specific roots -/

declare_B3Small_mixed_comm_thms βψ
declare_B3Small_mixed_comm_thms ψω
declare_B3Small_mixed_comm_thms β2ψ

/-! ### Double commutator theorem -/

theorem comm_of_β_ψ : double_commutator_of_root_pair (weakB3Small F).pres_mk β ψ βψ β2ψ 1 1 (by rfl) (by rfl) :=
  (weakB3Small F).double_commutator_helper β ψ βψ β2ψ 1 1 (by rfl) (by rfl)
    (by rw [weakB3Small, trivial_commutator_pairs]; simp)

/-! ### Nonhomogeneous lift -/
theorem nonhomog_lift_of_comm_of_βψ_ψω :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : F),
    ⁅ {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀}
    , {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} ⁆
    = 1 := by
  intro t₁ t₀ u₁ u₀ v₁ v₀
  apply WeakChevalley.helper
  apply (weakB3Small F).nonhomog_helper rels_of_nonhomog_lift_of_comm_of_βψ_ψω
  · simp only [weakB3Small, nonhomog_sets, Set.mem_singleton_iff]
  · exists t₁, t₀, u₁, u₀, v₁, v₀

/-! ### Definition of missing root -/
theorem def_of_βψω :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ βψω.height) (t : F),
    ⁅ {β, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1
    , {ψω, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 ⁆
    = {βψω, i, t} := by
  intro t i hi
  apply WeakChevalley.helper
  apply (weakB3Small F).def_helper rels_of_def_of_βψω
  · simp only [weakB3Small, def_sets, Set.mem_singleton_iff]
  · exists t, i, hi

theorem refl_of_nonhomog :
  ∀ S ∈ nonhomog_sets F,
    ∀ r ∈ S, (weakB3Small F).pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [nonhomog_sets, Set.mem_singleton_iff, forall_eq, rels_of_nonhomog_lift_of_comm_of_βψ_ψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ t₁, t₀, u₁, u₀, v₁, v₀, rfl ⟩
  simp only [map_mul, map_commutatorElement, free_mk_mk, FreeGroup.map.of, refl_deg_of_gen, PosRootSys.height, height]
  simp_arith
  repeat rw [← free_mk_mk]
  rw [add_comm (t₁ * u₀), add_comm (u₁ * v₀)]
  rw [expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω, mul_assoc, mul_assoc,
    expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω, ← mul_assoc, ← mul_assoc,
    expr_βψ_βψ_as_βψ_βψ, expr_ψω_ψω_as_ψω_ψω]
  exact nonhomog_lift_of_comm_of_βψ_ψω t₀ t₁ u₀ u₁ v₀ v₁

-- def relations are preserved under reflection
theorem refl_of_def : ∀ S ∈ def_sets F, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S := by
  simp only [def_sets, Set.mem_singleton_iff, forall_eq, rels_of_def_of_βψω, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ i, hi, t, rfl ⟩
  simp only [map_mul, map_commutatorElement, split_3_into_1_2]
  exists (βψω.height - i), (by omega), t
  split
  all_goals (simp only; congr)

theorem b3small_valid : ReflDeg.refl_valid (weakB3Small F) :=
  ⟨refl_of_nonhomog, refl_of_def⟩

end UnpackingPresentation /- section -/

/-! ### 8.37 -/

theorem expand_βψ_as_ψ_β_ψ_β_ψ :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ ψ.height) (t u : F),
    {βψ, i + j, 2 * (t * u)} =
    {ψ, j, (-u)} * {β, i, t} * {ψ, j, 2 * u} * {β, i, (-t)} * {ψ, j, (-u)} := by
    intro i j hi hj t u
    -- start with relation 8.2
    have base := comm_of_β_ψ hi hj t (2 * u)
    -- commute β + 2 ψ and β + ψ
    rw [comm_left, comm_of_βψ_β2ψ, one_mul] at base
    have this : (1 * (t * (2 * u * (2 * u)))) = 2 * (u * (2 * (t * u))) := by group
    rw [this] at base
    have this : (1 * (t * (2 * u))) = 2 * (t * u) := by group
    rw [this] at base
    -- replace β + 2 ψ with a commutator of ψ and β + ψ elements
    have this : i + 2 * j = j + (i + j) := by group
    simp only [this] at base
    have this := @comm_of_ψ_βψ _ _ j (i + j) hj (
      by
      simp only [PosRootSys.height, height] at hi
      simp only [PosRootSys.height, height] at hj
      simp only [PosRootSys.height, height]
      omega
    ) u (2 * (t * u))
    rw [← this] at base
    -- expand the commutator, and cancel with the β + ψ element on the right
    conv at base =>
      rhs; rw [commutatorElement_def]
    rw [inv_mul_cancel_right] at base
    -- expanding the commutator on the LHS and conjugating by ψ elements gives the relation
    rw [commutatorElement_def] at base
    have base := congrArg (HMul.hMul {ψ, j, u}⁻¹) base
    conv at base =>
      rhs
      rw [mul_assoc, inv_mul_cancel_left]
    have base := congrArg (fun x => HMul.hMul x {ψ, j, u}) base
    dsimp at base
    conv at base =>
      rhs
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [inv_of_β, inv_of_ψ, inv_of_ψ] at base
    conv at base =>
      lhs
      rw [mul_assoc, mul_assoc, lin_of_ψ j hj (-(2 * u)) u]
    have this : -(2 * u) + u = -u := by group
    rw [this] at base
    exact id (Eq.symm base)

/-! ### 8.38 -/

theorem expand_β2ψ_as_ψ_βψ_ψ_βψ :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ 2 * ψ.height) (t u : F),
      {β2ψ, i + j, 2 * (t * u)} = {ψ, i, t} * {βψ, j, u} * {ψ, i, (-t)} *
      {βψ, j, (-u)} := by sorry

/-! ### Derive full commutator for βψ and ψω from nonhomogeneous lift -/

-- NS: this section should probably be abstracted for reuse

/- Commutator relation in the case (i,j) is not (0,2) or (2,0) (via the previous theorem). -/
private lemma homog_lift_of_comm_of_βψ_ψω (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
  ∀ (t u : F), ⁅ { βψ, i + j, t}, {ψω, j + k, u} ⁆ = 1 := by
    intro t u
    let t₁ : F := match i with
      | 1 => t
      | 0 => 0
    let t₀ : F := match i with
      | 1 => 0
      | 0 => t
    let u₁ : F := match j with
      | 1 => 1
      | 0 => 0
    let u₀ : F := match j with
      | 1 => 0
      | 0 => 1
    let v₁ : F := match k with
      | 1 => u
      | 0 => 0
    let v₀ : F := match k with
      | 1 => 0
      | 0 => u
    have hf_i : i ∈ [0,1] := mem_list_range_iff_le.mp hi
    have hf_j : j ∈ [0,1] := mem_list_range_iff_le.mp hj
    have hf_k : k ∈ [0,1] := mem_list_range_iff_le.mp hk
    have id₁ : {βψ, i + j, t} = {βψ, 2, t₁ * u₁} * {βψ, 1, t₁ * u₀ + t₀ * u₁} * {βψ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp only [t₀, t₁, u₀, u₁, v₀, v₁]
        simp only [add_zero, mul_zero, zero_mul, mul_one, zero_add]
        repeat rw [id_of_βψ]
        simp only [one_mul, mul_one]
      )
    )
    have id₂ : {ψω, j + k, u} = {ψω, 2, u₁ * v₁} * {ψω, 1, u₁ * v₀ + u₀ * v₁} * {ψω, 0, u₀ * v₀} := by (
      fin_cases hf_i, hf_j, hf_k
      all_goals (
        simp only [t₀, t₁, u₀, u₁, v₀, v₁]
        simp only [add_zero, mul_zero, zero_mul, one_mul, zero_add]
        repeat rw [id_of_ψω]
        simp only [one_mul, mul_one]
      )
    )
    rw [id₁, id₂, nonhomog_lift_of_comm_of_βψ_ψω]

private lemma image_of_homog_lift_of_comm_of_βψ_ψω {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ψω.height) :
  ((i, j) ∈ ij_jk_image) → ∀ (t u : F), ⁅ {βψ, i, t}, {ψω, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  have ⟨ ijk', ⟨ h_in_cube, h_f ⟩ ⟩ := this
  have ⟨ hi', hj', hk' ⟩ := mem_range_of_boolean_cube ijk' h_in_cube
  let ⟨ i', j', k' ⟩ := ijk'
  have h_f' : i = i' + j' ∧ j = j' + k' := by rw [← Prod.mk.injEq, ← h_f, f_ij_jk]
  rw [← homog_lift_of_comm_of_βψ_ψω i' j' k' hi' hj' hk' t u]
  simp only [h_f']

private lemma comm_of_βψ_ψω_20 : ∀ (t u : F), ⁅ {βψ, 2, t}, {ψω, 0, u} ⁆ = 1 := by
  intro t u
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {ψω, 1, u} _ ({βψ, 1, t + 1} * {βψ, 0, 1})
  mul_assoc_l
  rw [← nonhomog_lift_of_comm_of_βψ_ψω t 1 1 1 0 u]
  simp only [one_mul, mul_one, mul_zero, add_zero]
  rw [id_of_ψω] -- NS: maybe should be a simp lemma? we can decide...
  rw [one_mul]
  rw [← homog_lift_of_comm_of_βψ_ψω 1 1 0 (by trivial) (by trivial) (by trivial) t u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_βψ_ψω 0 1 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_βψ_ψω 0 0 1 (by trivial) (by trivial) (by trivial) 1 u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_βψ_ψω 1 0 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_βψ_ψω 0 0 0 (by trivial) (by trivial) (by trivial) 1 u]

-- symmetric to proof of `comm_of_βψ_ψω_20`
private lemma comm_of_βψ_ψω_02 : ∀ (t u : F), ⁅ {βψ, 0, t}, {ψω, 2, u} ⁆ = 1 := by
  sorry

theorem comm_of_βψ_ψω : trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψ ψω := by
  intro i j hi hj t u
  have : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ ((i, j) ∈ ij_jk_image) := by
    rw [ij_jk_image]
    simp only [PosRootSys.height] at *
    simp only [B3SmallPosRoot.height] at *
    simp -- should fix
    omega
  rcases this with hij | hij | hij
  ·
    let ⟨ hd_i, hd_j ⟩ := hij
    simp_rw [hd_i, hd_j]
    rw [← comm_of_βψ_ψω_02 t u]
  ·
    let ⟨ hd_i, hd_j ⟩ := hij
    simp_rw [hd_i, hd_j]
    rw [← comm_of_βψ_ψω_20 t u]
  ·
    apply image_of_homog_lift_of_comm_of_βψ_ψω hi hj
    exact hij

/-! ### Further useful identities (roughly GENERIC) -/

-- 8.39 a

theorem expr_ψ_ω_as_ω_ψω_ψ :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : F),
      {ψ, i, t} * {ω, j, u} = {ω, j, u} * {ψω, i + j, 2 * (t * u)} * {ψ, i, t} := by sorry

-- 8.39 b

theorem expr_ψ_ω_as_ω_ψ_ψω :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : F),
      {ψ, i, t} * {ω, j, u} = {ω, j, u} * {ψ, i, t} * {ψω, i + j, 2 * (t * u)} := by sorry

-- 8.40 a

theorem expr_β_ψ_as_ψ_βψ_β2ψ_β :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : F),
      {β, i, t} * {ψ, j, u} = {ψ, j, u} * {βψ, i + j, t * u} *
      {β2ψ, i + 2 * j, -(t * u^2)} * {β, i, t} := by sorry

-- 8.40 b

theorem expr_β_ψ_as_ψ_β_β2ψ_βψ :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ ω.height) (t u : F),
      {β, i, t} * {ψ, j, u} = {ψ, j, u}  * {β, i, t} * {β2ψ, i + 2 * j, -(t * u^2)}
      * {βψ, i + j, t * u} := by sorry

-- 8.41

theorem expr_ψ_β_as_βψ_β2ψ_β_ψ :
    ∀ {i j : ℕ} (hi : i ≤ ψ.height) (hj : j ≤ β.height) (t u : F),
      {ψ, j, u} * {β, i, t} =
      {βψ, i + j, -(t * u)} * {β2ψ, i + 2 * j, -(t * u^2)} * {β, i, t} *
      {ψ, j, u} := by sorry

/-! ### βψ and ψω commute -/

-- 8.42

theorem trivial_comm_of_βψ_ψω :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψ ψω := by sorry

/-! ### Establishing βψω -/

-- 8.43

theorem trivial_comm_of_β2ψ_ψω :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk β2ψ ψω := by sorry

-- 8.44

theorem Interchange :
    ∀ {i j k : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψ.height) (hk : k ≤ ω.height) (t u v : F),
      ⁅ {βψ, i + j, t * u}, {ω, k, v} ⁆ = ⁅ {β, i , t}, {ψω, j + k, 2 * (u * v)} ⁆ := by sorry

-- 8.46

theorem expr_βψω_as_βψ_ω_βψ_ω :
    ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ω.height) (t u : F),
      {βψω, i + j, 2 * (t * u)} = {βψ, i, t} * {ω, j, u} * {βψ, i, -t} *
      {ω, j, -u} := by sorry

-- 8.47

theorem expr_βψω_as_β_ψω_β_ψω :
    ∀ {i j : ℕ} (hi : i ≤ β.height) (hj : j ≤ ψω.height) (t u : F),
      {βψω, i + j, t * u} = {β, i, t} * {ψω, j, u} * {β, i, -t} * {ψω, j, -u} := by sorry

/-! ### Remaining commutation relations -/

-- 8.48

theorem trivial_comm_of_βψω_ω :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω ω := by sorry

-- 8.49

theorem trivial_comm_of_βψω_β :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω β := by sorry

-- 8.50

theorem trivial_comm_of_βψω_ψ :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω ψ := by sorry

-- 8.51

theorem trivial_comm_of_βψω_ψω :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω ψω := by sorry

-- 8.52

theorem trivial_comm_of_βψω_βψ :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω βψ := by sorry

-- 8.53

theorem trivial_comm_of_βψω_β2ψ :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk βψω β2ψ := by sorry

-- 8.54

theorem self_comm_of_βψω :
    mixed_commutes_of_root (weakB3Small F).pres_mk βψω := by sorry

-- 8.55

theorem lin_of_βψω : lin_of_root((weakB3Small F).pres_mk, βψω) := by sorry

-- 8.56

theorem inv_of_βψω : inv_of_root((weakB3Small F).pres_mk, βψω) := by sorry

-- 8.57 a

theorem expr_βψ_ω_as_ω_βψω_βψ :
    ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ω.height) (t u : F),
      {βψ, i, t} * {ω, j, u} = {ω, j, u} * {βψω, i + j, 2 * (t * u)} *
      {βψ, i, t} := by sorry

-- 8.57 b

theorem expr_βψ_ω_as_ω_βψ_βψω :
    ∀ {i j : ℕ} (hi : i ≤ βψ.height) (hj : j ≤ ω.height) (t u : F),
      {βψ, i, t} * {ω, j, u} = {ω, j, u} * {βψ, i, t} *
      {βψω, i + j, 2 * (t * u)} := by sorry

-- 8.58

theorem trivial_comm_of_β2ψ_ω :
    trivial_commutator_of_root_pair (weakB3Small F).pres_mk β2ψ ω := by sorry

end B3SmallProof

end Steinberg

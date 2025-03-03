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

In our group presentation, the generators are of the form `{ζ, t, i}`, where `ζ` is one of α, β, γ, αβ, or βγ; `t` is in `R`
(an arbitrary ring); and `i` is between 0 and height(`r`) inclusive. Such a generator corresponds to a unipotent matrix with a single homogeneous
entry, `tx^i`, in the `r` position. We consider a certain set of relations which these generators satisfy, and prove from these
all relations characterizing interactions of single-homogeneous-entry-above-diagonal unipotent matrices. (These, in turn,
form a canonical presentation of the entire group.)
-/

variable {R : Type TR} [Ring R]

/-! ### Defining the A3 positive root system -/

inductive A3PosRoot
  | α | β | γ | αβ | βγ | αβγ
deriving Fintype, DecidableEq

namespace A3PosRoot

@[reducible]
def height : A3PosRoot → Nat
  | α | β | γ => 1
  | αβ | βγ => 2
  | αβγ => 3

def toString : A3PosRoot → String
  | α => "α"
  | β => "β"
  | γ => "γ"
  | αβ => "α+β"
  | βγ => "β+γ"
  | αβγ => "α+β+γ"

instance : PosRootSys A3PosRoot where
  height := height
  toString := toString

end A3PosRoot

namespace A3Proof

open A3PosRoot GradedGen ReflDeg

/-! ### Bundle together assumptions about the A3 generators -/

/-
The specific relation arises from "nonhomogeneously lifting" the commutator of αβ and βγ elements. (There is no analogue
of this relation for other root-pairs, since all other present pairs lie in a common two-dimensional subspace.)
-/
def rels_of_nonhomog_lift_of_comm_of_αβ_βγ :=
  { ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀},
      {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} ⁆
    | (t₁ : R) (t₀ : R) (u₁ : R) (u₀ : R) (v₁ : R) (v₀ : R) }

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

def rels_of_def_of_αβγ :=
  { ⁅ {α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1,
      {βγ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 ⁆
      * {αβγ, i, t}⁻¹
    | (i : ℕ) (hi : i ≤ αβγ.height) (t : R) }

abbrev trivial_commutator_pairs : Set (A3PosRoot × A3PosRoot) :=
  {(α, γ), (α, αβ), (β, αβ), (β, βγ), (γ, βγ)}

abbrev single_commutator_pairs : Set ((ζ : A3PosRoot) × (η : A3PosRoot) × (θ : A3PosRoot) × R ×' (θ.height = ζ.height + η.height)) :=
  {⟨ α, β, αβ, 1, (by simp only [height])⟩, ⟨β, γ, βγ, 1, (by simp only [height])⟩}

abbrev double_commutator_pairs : Set ((ζ : A3PosRoot) × (η : A3PosRoot) × (θ₁ : A3PosRoot) × (θ₂ : A3PosRoot) × R × R ×' (θ₁.height = ζ.height + η.height)
  ×' (θ₂.height = ζ.height + 2 * η.height)) := {}

abbrev mixed_commutes_roots : Set (A3PosRoot) :=
  {α, β, γ, αβ, βγ}

abbrev lin_roots : Set (A3PosRoot) :=
  {α, β, γ, αβ, βγ}

-- lifted commutator of αβ and βγ
def nonhomog_sets (R : Type TR) [Ring R] : Set (Set (FreeGroupOnGradedGens A3PosRoot R)) :=
  { rels_of_nonhomog_lift_of_comm_of_αβ_βγ }

-- definition of αβγ
def def_sets (R : Type TR) [Ring R] : Set (Set (FreeGroupOnGradedGens A3PosRoot R)) :=
  { rels_of_def_of_αβγ }

def weakA3 (R : Type TR) [Ring R] := WeakChevalley.mk
  trivial_commutator_pairs
  single_commutator_pairs
  double_commutator_pairs
  mixed_commutes_roots
  lin_roots
  (nonhomog_sets R)
  (def_sets R)

/- Instantiate the `declare_thms` macros from `WeakChevalley.lean`. -/

-- CC: TODO: Make this a macro to declare all at once for A3.
--     Something like: `declare_thms A3 weakA3 R`

macro "declare_A3_triv_comm_of_root_pair_thms" r₁:term:arg r₂:term:arg : command =>
  `(command| declare_triv_comm_of_root_pair_thms weakA3 R $r₁ $r₂)

macro "declare_A3_single_comm_of_root_pair_thms" r₁:term:arg r₂:term:arg r₃:term:arg : command =>
  `(command| declare_single_comm_of_root_pair_thms weakA3 R $r₁ $r₂ $r₃ 1)

macro "declare_A3_lin_id_inv_thms" root:term:arg : command =>
  `(command| declare_lin_id_inv_thms weakA3 R $root)

macro "declare_A3_expr_as_thm" r₁:term:arg r₂:term:arg : command =>
  `(command| declare_expr_as_thm weakA3 R $r₁ $r₂)

macro "declare_A3_mixed_comm_thms" r:term:arg : command =>
  `(command| declare_mixed_comm_thms weakA3 R $r)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}" =>
  (weakA3 R).pres_mk (free_mk_mk ζ i (by
    try simp only [PosRootSys.height] at *
    try simp only [A3PosRoot.height] at *; first | trivial | omega) t)

set_option hygiene false in
/-- Shorthand for building free group elements from a root, degree, and ring element. -/
scoped notation (priority:=high) "{" ζ ", " i ", " t "}'" h =>
  (weakA3 R).pres_mk ({ζ, i, t}'h)

section UnpackingPresentation

declare_A3_triv_comm_of_root_pair_thms α γ
declare_A3_triv_comm_of_root_pair_thms α αβ
declare_A3_triv_comm_of_root_pair_thms β αβ
declare_A3_triv_comm_of_root_pair_thms β βγ
declare_A3_triv_comm_of_root_pair_thms γ βγ

declare_A3_single_comm_of_root_pair_thms α β αβ
declare_A3_single_comm_of_root_pair_thms β γ βγ

/-! ### Linearity theorems for specific roots -/

declare_A3_lin_id_inv_thms α
declare_A3_lin_id_inv_thms β
declare_A3_lin_id_inv_thms γ
declare_A3_lin_id_inv_thms αβ
declare_A3_lin_id_inv_thms βγ

/-! ### Mixed-degree theorem for specific roots -/

declare_A3_mixed_comm_thms αβ
declare_A3_mixed_comm_thms βγ

/-! ### Nonhomogeneous lift -/

theorem nonhomog_lift_of_comm_of_αβ_βγ :
  ∀ (t₁ t₀ u₁ u₀ v₁ v₀ : R),
    ⁅ {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀}
    , {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} ⁆
    = 1 := by
  intro t₁ t₀ u₁ u₀ v₁ v₀
  apply WeakChevalley.helper
  apply (weakA3 R).nonhomog_helper rels_of_nonhomog_lift_of_comm_of_αβ_βγ
  · simp only [weakA3, nonhomog_sets, Set.mem_singleton_iff]
  · exists t₁, t₀, u₁, u₀, v₁, v₀

/-! ### Definition of missing root -/
theorem def_of_αβγ :
  ∀ ⦃i : ℕ⦄ (hi : i ≤ αβγ.height) (t : R),
    ⁅ {α, (split_3_into_1_2 i hi).1, t}'(correct_of_split_3_into_1_2 i hi).1
    , {βγ, (split_3_into_1_2 i hi).2, 1}'(correct_of_split_3_into_1_2 i hi).2 ⁆
    = {αβγ, i, t} := by
  intro t i hi
  apply WeakChevalley.helper
  apply (weakA3 R).def_helper rels_of_def_of_αβγ
  · simp only [weakA3, def_sets, Set.mem_singleton_iff]
  · exists t, i, hi

theorem refl_of_nonhomog :
  ∀ S ∈ nonhomog_sets R,
    ∀ r ∈ S, (weakA3 R).pres_mk (FreeGroup.map refl_deg_of_gen r) = 1 := by
  simp only [nonhomog_sets, Set.mem_singleton_iff, forall_eq, rels_of_nonhomog_lift_of_comm_of_αβ_βγ, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ t₁, t₀, u₁, u₀, v₁, v₀, rfl ⟩
  simp only [map_mul, map_commutatorElement, free_mk_mk, FreeGroup.map.of, refl_deg_of_gen, PosRootSys.height, height]
  simp_arith
  repeat rw [← free_mk_mk]
  rw [add_comm (t₁ * u₀), add_comm (u₁ * v₀)]
  rw [expr_αβ_αβ_as_αβ_αβ, expr_βγ_βγ_as_βγ_βγ, mul_assoc, mul_assoc,
    expr_αβ_αβ_as_αβ_αβ, expr_βγ_βγ_as_βγ_βγ, ← mul_assoc, ← mul_assoc,
    expr_αβ_αβ_as_αβ_αβ, expr_βγ_βγ_as_βγ_βγ]
  exact nonhomog_lift_of_comm_of_αβ_βγ t₀ t₁ u₀ u₁ v₀ v₁

-- def relations are preserved under reflection
theorem refl_of_def : ∀ S ∈ def_sets R, ∀ r ∈ S, FreeGroup.map refl_deg_of_gen r ∈ S := by
  simp only [def_sets, Set.mem_singleton_iff, forall_eq, rels_of_def_of_αβγ, Set.mem_setOf_eq]
  intro r h
  rcases h with ⟨ i, hi, t, rfl ⟩
  simp only [map_mul, map_commutatorElement, split_3_into_1_2]
  exists (αβγ.height - i), (by omega), t
  split
  all_goals (simp only; congr)

theorem a3_valid : ReflDeg.refl_valid (R := R) (weakA3 R) :=
  ⟨refl_of_nonhomog, refl_of_def⟩

end UnpackingPresentation /- section -/

/-! ### Derive full commutator for αβ and βγ from nonhomogeneous lift -/

-- NS: this section should probably be abstracted for reuse

/- Commutator relation in the case (i,j) is not (0,2) or (2,0) (via the previous theorem). -/
private lemma homog_lift_of_comm_of_αβ_βγ (i j k : ℕ) (hi : i ≤ 1) (hj : j ≤ 1) (hk : k ≤ 1) :
  ∀ (t u : R), ⁅ { αβ, i + j, t}, {βγ, j + k, u} ⁆ = 1 := by
    intro t u
    let t₁ : R := match i with
      | 1 => t
      | 0 => 0
    let t₀ : R := match i with
      | 1 => 0
      | 0 => t
    let u₁ : R := match j with
      | 1 => 1
      | 0 => 0
    let u₀ : R := match j with
      | 1 => 0
      | 0 => 1
    let v₁ : R := match k with
      | 1 => u
      | 0 => 0
    let v₀ : R := match k with
      | 1 => 0
      | 0 => u
    have hf_i : i ∈ [0,1] := mem_list_range_iff_le.mp hi
    have hf_j : j ∈ [0,1] := mem_list_range_iff_le.mp hj
    have hf_k : k ∈ [0,1] := mem_list_range_iff_le.mp hk
    have id₁ : {αβ, i + j, t} = {αβ, 2, t₁ * u₁} * {αβ, 1, t₁ * u₀ + t₀ * u₁} * {αβ, 0, t₀ * u₀} := by (
      fin_cases hf_i, hf_j, hf_k
      <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
    )
    have id₂ : {βγ, j + k, u} = {βγ, 2, u₁ * v₁} * {βγ, 1, u₁ * v₀ + u₀ * v₁} * {βγ, 0, u₀ * v₀} := by (
      fin_cases hf_i, hf_j, hf_k
      <;> chev_simp [t₀, t₁, u₀, u₁, v₀, v₁]
    )
    rw [id₁, id₂, nonhomog_lift_of_comm_of_αβ_βγ]

private lemma image_of_homog_lift_of_comm_of_αβ_βγ {i j : ℕ} (hi : i ≤ αβ.height) (hj : j ≤ βγ.height)
    : ((i, j) ∈ ij_jk_image) → ∀ (t u : R), ⁅ {αβ, i, t}, {βγ, j, u} ⁆ = 1 := by
  intro h_in_image t u
  have : ∃ ijk' : ℕ × ℕ × ℕ, ijk' ∈ boolean_cube ∧ f_ij_jk ijk' = (i, j) := by
    rw [← Finset.mem_image, correct_of_ij_jk_image]; exact h_in_image
  rcases this with ⟨ ⟨i', j', k'⟩, ⟨ h_in_cube, h_f ⟩ ⟩
  rcases mem_range_of_boolean_cube _ h_in_cube with ⟨ hi', hj', hk' ⟩
  have h_f' : i = i' + j' ∧ j = j' + k' := by rw [← Prod.mk.injEq, ← h_f, f_ij_jk]
  rcases h_f' with ⟨ rfl, rfl ⟩
  rw [← homog_lift_of_comm_of_αβ_βγ i' j' k' hi' hj' hk' t u]

private lemma comm_of_αβ_βγ_20 : ∀ (t u : R), ⁅ {αβ, 2, t}, {βγ, 0, u} ⁆ = 1 := by
  intro t u
  apply @trivial_comm_from_embedded_comm_and_pairs _ _ {βγ, 1, u} _ ({αβ, 1, t + 1} * {αβ, 0, 1})
  grw [← nonhomog_lift_of_comm_of_αβ_βγ t 1 1 1 0 u]
  rw [← homog_lift_of_comm_of_αβ_βγ 1 1 0 (by trivial) (by trivial) (by trivial) t u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_αβ_βγ 0 1 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_αβ_βγ 0 0 1 (by trivial) (by trivial) (by trivial) 1 u]
  apply triv_comm_mul_left
  rw [← homog_lift_of_comm_of_αβ_βγ 1 0 0 (by trivial) (by trivial) (by trivial) (t+1) u]
  rw [← homog_lift_of_comm_of_αβ_βγ 0 0 0 (by trivial) (by trivial) (by trivial) 1 u]

-- symmetric to proof of `comm_of_αβ_βγ_20`
private lemma comm_of_αβ_βγ_02 : ∀ (t u : R), ⁅ {αβ, 0, t}, {βγ, 2, u} ⁆ = 1 := by
  intro t u
  have : ⁅ {αβ, 0, t}, {βγ, 2, u} ⁆ = ReflDeg.refl_symm a3_valid ⁅ {αβ, 2, t}, {βγ, 0, u} ⁆ := by
    rw [map_commutatorElement]
    trivial
  rw [this, comm_of_αβ_βγ_20, map_one]

theorem comm_of_αβ_βγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk αβ βγ := by
  intro i j hi hj t u
  have : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ ((i, j) ∈ ij_jk_image) := by
    rw [ij_jk_image]
    simp only [PosRootSys.height, height] at *
    simp -- should fix
    omega
  rcases this with ( ⟨ rfl, rfl ⟩ | ⟨rfl, rfl⟩ | hij )
  · rw [← comm_of_αβ_βγ_02 t u]
  · rw [← comm_of_αβ_βγ_20 t u]
  · exact image_of_homog_lift_of_comm_of_αβ_βγ hi hj hij _ _

/-! ### Further useful identities (roughly GENERIC) -/

/- Expand βγ as β⬝γ⬝β⬝γ. -/
theorem expand_βγ_as_β_γ_β_γ :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R),
      {βγ, i + j, t * u} = {β, i, t} * {γ, j, u} * {β, i, (-t)} * {γ, j, (-u)} := by
  intro i j hi hj t u
  have := comm_of_β_γ hi hj t u
  rw [one_mul] at this
  grw [← this, commutatorElement_def]

/- Rewrite α⬝β as αβ⬝β⬝α. -/
@[group_reassoc]
theorem expr_α_β_as_αβ_β_α :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ β.height) (t u : R),
      reorder_left({α, i, t}, {β, j, u}, {αβ, i + j, t * u}) := by
  intro i j hi hj t u
  have := comm_of_α_β hi hj t u
  rw [one_mul] at this
  grw [← this, commutatorElement_def]

/- Rewrite β⬝γ as βγ⬝γ⬝β. -/
@[group_reassoc]
theorem expr_β_γ_as_βγ_γ_β :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R),
      reorder_left({β, i, t}, {γ, j, u}, {βγ, i + j, t * u}) := by
  intro i j hi hj t u
  have := comm_of_β_γ hi hj t u
  rw [one_mul] at this
  grw [← this, commutatorElement_def]

/- Rewrite β⬝γ as γ⬝βγ⬝β. -/
@[group_reassoc]
theorem expr_β_γ_as_γ_βγ_β :
  ∀ ⦃i j : ℕ⦄ (hi : i ≤ β.height) (hj : j ≤ γ.height) (t u : R),
    reorder_mid({β, i, t}, {γ, j, u}, {βγ, i + j, t * u}) := by
  intro i j hi hj t u
  have := comm_of_β_γ hi hj t u
  rw [one_mul] at this
  rw [← this, comm_mid, inv_of_γ, comm_of_β_γ]
  grw [comm_of_β_γ]

declare_A3_expr_as_thm α γ
declare_A3_expr_as_thm α αβ
declare_A3_expr_as_thm β αβ
declare_A3_expr_as_thm γ βγ
declare_A3_expr_as_thm αβ βγ

/-! ### Interchange theorems between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms -/

/- Interchange between ⁅α, βγ⁆ and ⁅αβ, γ⁆, "trading" a single degree j : Deg 1 and scalar u : R. -/
theorem Interchange {i j k : ℕ} (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
    ∀ (t u v : R), ⁅ {α, i, t}, {βγ, j + k, u * v} ⁆ = ⁅ {αβ, i + j, t * u}, {γ, k, v} ⁆ := by
  intro t u v
  apply eq_comm_of_reorder_left
  have hij : i + j ≤ αβ.height := by simp only [height] at *; omega
  have hjk : j + k ≤ βγ.height := by simp only [height] at *; omega
  grw [expand_βγ_as_β_γ_β_γ hj hk,
    expr_α_β_as_αβ_β_α hi hj,
    expr_α_γ_as_γ_α hi hk,
    expr_α_β_as_αβ_β_α hi hj,
    mul_neg,
    expr_α_γ_as_γ_α hi hk,
    expr_β_γ_as_βγ_γ_β hj hk,
    expr_β_αβ_as_αβ_β hj hij,
    ← expr_γ_βγ_as_βγ_γ hk hjk,
    ← expr_αβ_βγ_as_βγ_αβ hij hjk,
    commutatorElement_def,
    expr_β_γ_as_βγ_γ_β hj hk,
    ← expr_γ_βγ_as_βγ_γ hk hjk]

/- Pass between ⁅α,βγ⁆ and ⁅αβ,γ⁆ forms (specializes `Interchange` to the case `u=1`). -/
theorem InterchangeTrans {i j k : ℕ} (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
    ∀ (t u : R), ⁅ {α, i, t}, {βγ, j + k, u} ⁆ = ⁅ {αβ, i + j, t}, {γ, k, u} ⁆ := by
  intro t u
  have := Interchange hi hj hk t 1 u
  rwa [one_mul, mul_one] at this

/- ⁅α,βγ⁆ forms depend only on product of coefficients. Applies `Interchange` twice. -/
theorem InterchangeRefl {i j k : ℕ} (hi : i ≤ α.height) (hj : j ≤ β.height) (hk : k ≤ γ.height) :
    ∀ (t u : R), ⁅ {α, i, t * u}, {βγ, j + k, 1} ⁆ = ⁅ {α, i, t}, {βγ, j + k, u} ⁆ := by
  intro t u
  nth_rewrite 2 [← mul_one u]
  rw [Interchange hi hj hk, InterchangeTrans hi hj hk]

/-! ### Commutator relations for (α,βγ) and (αβ,γ) via interchange relations -/

-- NS: Really need to figure out a more sane way to write this section.

-- height 0
private lemma comm_of_α_βγ_00 (t u : R) :
    ⁅ {α, 0, t}, {βγ, 0, u} ⁆ = {αβγ, 0, t * u} := by
  rw [← @InterchangeRefl _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]
  rw [← def_of_αβγ (by trivial) (t * u)]
  simp only [split_3_into_1_2]

private lemma comm_of_αβ_γ_00 (t u : R) :
    ⁅ {αβ, 0, t}, {γ, 0, u} ⁆ = {αβγ, 0, t * u} := by
  rw [← @InterchangeTrans _ _ 0 0 0 (by trivial) (by trivial) (by trivial)]
  rw [comm_of_α_βγ_00]

-- height 1
private lemma comm_of_α_βγ_01 (t u : R) :
    ⁅ {α, 0, t}, {βγ, 1, u} ⁆ = {αβγ, 1, t * u} := by
  rw [← @InterchangeRefl _ _ 0 0 1 (by trivial) (by trivial) (by trivial)]
  rw [← def_of_αβγ (by trivial) (t * u)]
  simp only [split_3_into_1_2]

private lemma comm_of_αβ_γ_10 (t u : R) : ⁅ {αβ, 1, t}, {γ, 0, u} ⁆ = {αβγ, 1, t * u} := by
  rw [← @InterchangeTrans _ _ 0 1 0 (by trivial) (by trivial) (by trivial)]
  simp only [add_zero, comm_of_α_βγ_01, zero_add, one_mul]

private lemma comm_of_α_βγ_10 (t u : R) : ⁅ {α, 1, t}, {βγ, 0, u} ⁆ = {αβγ, 1, t * u} := by
  rw [@InterchangeTrans _ _ 1 0 0 (by trivial) (by trivial) (by trivial),
        comm_of_αβ_γ_10]

private lemma comm_of_αβ_γ_01 (t u : R) : ⁅ {αβ, 0, t}, {γ, 1, u} ⁆ = {αβγ, 1, t * u} := by
  rw [← @InterchangeTrans _ _ 0 0 1 (by trivial) (by trivial) (by trivial),
        comm_of_α_βγ_01]

-- height 2
private lemma comm_of_α_βγ_11 (t u : R) : ⁅ {α, 1, t}, {βγ, 1, u} ⁆ = {αβγ, 2, t * u} := by
  rw [← @InterchangeRefl _ _ 1 0 1 (by trivial) (by trivial) (by trivial),
        ← def_of_αβγ (by trivial) (t * u)]
  simp only [split_3_into_1_2]

private lemma comm_of_αβ_γ_11 (t u : R) : ⁅ {αβ, 1, t}, {γ, 1, u} ⁆ = {αβγ, 2, t * u} := by
  rw [← @InterchangeTrans _ _ 1 0 1 (by trivial) (by trivial) (by trivial),
        comm_of_α_βγ_11]

private lemma comm_of_α_βγ_02 (t u : R) : ⁅ {α, 0, t}, {βγ, 2, u} ⁆ = {αβγ, 2, t * u} := by
  rw [@InterchangeTrans _ _ 0 1 1 (by trivial) (by trivial) (by trivial),
        comm_of_αβ_γ_11]

private lemma comm_of_αβ_γ_20 (t u : R) : ⁅ {αβ, 2, t}, {γ, 0, u} ⁆ = {αβγ, 2, t * u} := by
  rw [← @InterchangeTrans _ _ 1 1 0 (by trivial) (by trivial) (by trivial),
        comm_of_α_βγ_11]

-- height 3
private lemma comm_of_α_βγ_12 (t u : R) : ⁅ {α, 1, t}, {βγ, 2, u} ⁆ = {αβγ, 3, t * u} := by
  rw [← @InterchangeRefl _ _ 1 1 1 (by trivial) (by trivial) (by trivial),
        ← def_of_αβγ (by trivial) (t * u)]
  simp only [split_3_into_1_2]

private lemma comm_of_αβ_γ_21 (t u : R) : ⁅ {αβ, 2, t}, {γ, 1, u} ⁆ = {αβγ, 3, t * u} := by
  rw [← @InterchangeTrans _ _ 1 1 1 (by trivial) (by trivial) (by trivial),
        comm_of_α_βγ_12]

/- Commutator relation for α and βγ. -/
theorem comm_of_α_βγ : single_commutator_of_root_pair (weakA3 R).pres_mk α βγ αβγ 1
    (by simp only [PosRootSys.height] at *; simp only [A3PosRoot.height] at *) := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => simp only [comm_of_α_βγ_00 t u, add_zero, one_mul]
  | 0, 1 => simp only [comm_of_α_βγ_01 t u, zero_add, one_mul]
  | 0, 2 => simp only [comm_of_α_βγ_02 t u, zero_add, one_mul]
  | 1, 0 => simp only [comm_of_α_βγ_10 t u, add_zero, one_mul]
  | 1, 1 => simp only [comm_of_α_βγ_11 t u, Nat.reduceAdd, one_mul]
  | 1, 2 => simp only [comm_of_α_βγ_12 t u, Nat.reduceAdd, one_mul]

/- Commutator relation for αβ and γ. -/
theorem comm_of_αβ_γ : single_commutator_of_root_pair (weakA3 R).pres_mk αβ γ αβγ 1
    (by simp only [PosRootSys.height] at *; simp only [A3PosRoot.height] at *) := by
  intro i j hi hj t u
  match i, j with
  | 0, 0 => simp only [comm_of_αβ_γ_00 t u, add_zero, one_mul]
  | 1, 0 => simp only [comm_of_αβ_γ_10 t u, add_zero, one_mul]
  | 2, 0 => simp only [comm_of_αβ_γ_20 t u, add_zero, one_mul]
  | 0, 1 => simp only [comm_of_αβ_γ_01 t u, zero_add, one_mul]
  | 1, 1 => simp only [comm_of_αβ_γ_11 t u, Nat.reduceAdd, one_mul]
  | 2, 1 => simp only [comm_of_αβ_γ_21 t u, Nat.reduceAdd, one_mul]

/-! ### More rewriting theorems -/

/- Expand αβγ as α⬝βγ⬝α⬝βγ. -/
theorem expand_αβγ_as_α_βγ_α_βγ :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βγ.height) (t u : R),
      {αβγ, i + j, t * u} = {α, i, t} * {βγ, j, u} * {α, i, -t} * {βγ, j, -u} := by
  intro i j hi hj t u
  rw [← inv_of_α, ← inv_of_βγ, ← commutatorElement_def,
        ← one_mul (t * u), ← comm_of_α_βγ]

theorem expand_αβγ_as_α_βγ_α_βγ_one_mul :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βγ.height) (u : R),
      {αβγ, i + j, u} = {α, i, 1} * {βγ, j, u} * {α, i, -1} * {βγ, j, -u} := by
  intro i j hi hj u
  have := expand_αβγ_as_α_βγ_α_βγ hi hj 1 u
  rwa [one_mul] at this

theorem expand_αβγ_as_α_βγ_α_βγ_mul_one :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ α.height) (hj : j ≤ βγ.height) (t : R),
      {αβγ, i + j, t} = {α, i, t} * {βγ, j, 1} * {α, i, -t} * {βγ, j, -1} := by
  intro i j hi hj t
  have := expand_αβγ_as_α_βγ_α_βγ hi hj t 1
  rwa [mul_one] at this

/- Expand αβγ as αβ⬝γ⬝αβ⬝γ. -/
theorem expand_αβγ_as_αβ_γ_αβ_γ :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ γ.height) (t u : R),
      {αβγ, i + j, t * u} = {αβ, i, t} * {γ, j, u} * {αβ, i, -t} * {γ, j, -u} := by
  intro i j hi hj t u
  rw [← inv_of_αβ, ← inv_of_γ, ← commutatorElement_def, ← one_mul (t * u), ← comm_of_αβ_γ]

theorem expand_αβγ_as_αβ_γ_αβ_γ_one_mul :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ γ.height) (u : R),
      {αβγ, i + j, u} = {αβ, i, 1} * {γ, j, u} * {αβ, i, -1} * {γ, j, -u} := by
  intro i j hi hj u
  have := expand_αβγ_as_αβ_γ_αβ_γ hi hj 1 u
  rwa [one_mul] at this

theorem expand_αβγ_as_αβ_γ_αβ_γ_mul_one :
    ∀ ⦃i j : ℕ⦄ (hi : i ≤ αβ.height) (hj : j ≤ γ.height) (t : R),
      {αβγ, i + j, t} = {αβ, i, t} * {γ, j, 1} * {αβ, i, -t} * {γ, j, -1} := by
  intro i j hi hj t
  have := expand_αβγ_as_αβ_γ_αβ_γ hi hj t 1
  rwa [mul_one] at this

/-! ### Commutators of αβγ with other roots -/

/- α and αβγ commute. -/
/- NS: One should be able to prove this quite simply:  simple proof: we know αβγ is expressible as a product of αβ's and γ's (expand_αβγ_as_αβ_γ_αβ_γ), and we know that α's
   commute with αβ's (expr_α_αβ_as_αβ_α) and γ's (expr_α_γ_as_γ_α) -/
theorem comm_of_α_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk α αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height γ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expand_αβγ_as_αβ_γ_αβ_γ_one_mul hj₁ hj₂,
      expr_α_αβ_as_αβ_α hi hj₁,
      expr_α_γ_as_γ_α hi hj₂,
      expr_α_αβ_as_αβ_α hi hj₁,
      expr_α_γ_as_γ_α hi hj₂]

/- β and αβγ commute. -/
-- the only commutator proof where we have to do something 'interesting'
theorem comm_of_β_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk β αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height γ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expand_αβγ_as_αβ_γ_αβ_γ_one_mul hj₁ hj₂,
      expr_β_αβ_as_αβ_β hi hj₁,
      expr_β_γ_as_γ_βγ_β hi hj₂,
      expr_β_αβ_as_αβ_β hi hj₁,
      expr_β_γ_as_βγ_γ_β hi hj₂,
      ← expr_αβ_βγ_as_βγ_αβ hj₁ (by simp only [PosRootSys.height, height] at *; omega)]

/- γ and αβγ commute. -/
theorem comm_of_γ_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk γ αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose α.height βγ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expand_αβγ_as_α_βγ_α_βγ_one_mul hj₁ hj₂,
    ← expr_α_γ_as_γ_α hj₁ hi,
    expr_γ_βγ_as_βγ_γ hi hj₂,
    ← expr_α_γ_as_γ_α hj₁ hi,
    expr_γ_βγ_as_βγ_γ hi hj₂]

/- αβ and αβγ commute. -/
theorem comm_of_αβ_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk αβ αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose α.height βγ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expand_αβγ_as_α_βγ_α_βγ_one_mul hj₁ hj₂,
    ← expr_α_αβ_as_αβ_α hj₁ hi,
    expr_αβ_βγ_as_βγ_αβ hi hj₂,
    ← expr_α_αβ_as_αβ_α hj₁ hi,
    expr_αβ_βγ_as_βγ_αβ hi hj₂]

/- βγ and αβγ commute. -/
theorem comm_of_βγ_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk βγ αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose αβ.height γ.height j hj with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expand_αβγ_as_αβ_γ_αβ_γ_one_mul hj₁ hj₂,
    ← expr_αβ_βγ_as_βγ_αβ hj₁ hi,
    ← expr_γ_βγ_as_βγ_γ hj₂ hi,
    ← expr_αβ_βγ_as_βγ_αβ hj₁ hi,
    ← expr_γ_βγ_as_βγ_γ hj₂ hi]

declare_A3_expr_as_thm α αβγ
declare_A3_expr_as_thm β αβγ
declare_A3_expr_as_thm γ αβγ
declare_A3_expr_as_thm αβ αβγ
declare_A3_expr_as_thm βγ αβγ

/- αβγ commutes with itself. -/
theorem mixed_commutes_of_αβγ : trivial_commutator_of_root_pair (weakA3 R).pres_mk αβγ αβγ := by
  intro i j hi hj t u
  apply triv_comm_iff_commutes.mpr
  rcases decompose α.height βγ.height j (by trivial) with ⟨ j₁, j₂, ⟨ rfl, hj₁, hj₂ ⟩ ⟩
  grw [expand_αβγ_as_α_βγ_α_βγ_one_mul hj₁ hj₂,
    ← expr_α_αβγ_as_αβγ_α hj₁ hi,
    ← expr_βγ_αβγ_as_αβγ_βγ hj₂ hi,
    ← expr_α_αβγ_as_αβγ_α hj₁ hi,
    ← expr_βγ_αβγ_as_αβγ_βγ hj₂ hi]

/- Linearity for αβγ. -/
@[group_reassoc (attr := simp, chev_simps)]
theorem lin_of_αβγ : lin_of_root((weakA3 R).pres_mk, αβγ) := by
  intro i hi t u
  rcases decompose α.height βγ.height i (by trivial) with ⟨ i₁, i₂, ⟨ rfl, hi₁, hi₂ ⟩ ⟩
  have h_eq' : i₁ + i₂ ≤ PosRootSys.height αβγ := by omega
  grw [expand_αβγ_as_α_βγ_α_βγ_mul_one hi₁ hi₂,
    expr_βγ_αβγ_as_αβγ_βγ hi₂ h_eq',
    expr_α_αβγ_as_αβγ_α hi₁ h_eq',
    expr_βγ_αβγ_as_αβγ_βγ hi₂ h_eq',
    expand_αβγ_as_α_βγ_α_βγ_mul_one hi₁ hi₂,
    ← neg_add, add_comm u t,
    ← expand_αβγ_as_α_βγ_α_βγ hi₁ hi₂]

end A3Proof

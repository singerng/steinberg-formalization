/-
Copyright (c) 2025 The Steinberg Group
Released under the Apache License v2.0; see LICENSE for full text.
-/

import Steinberg.A3.Defs

namespace Steinberg.A3

open Steinberg A3 PartialChevalley PartialChevalleySystem ChevalleyGenerator A3PosRoot
  PartialChevalleyGroup

variable {R : Type TR} [Ring R] (RUnitTwo : IsUnit (2 : R))

def weak_define_ungraded (R : Type TR) [Ring R] (g : ChevalleyGenerator A3PosRoot R) : FreeGroup (ChevalleyGenerator A3PosRoot R) :=
  let ⟨ ζ, t ⟩ := g;
  match ζ with
  | αβγ => ⁅ {α, t}, {βγ, 1} ⁆
  | ζ => FreeGroup.of g

theorem weak_define_of_present_ungraded (R : Type TR) [Ring R] :
  ∀ {g : ChevalleyGenerator A3PosRoot R}, g.ζ ∈ weakA3System.present_roots → weak_define_ungraded R g = FreeGroup.of g := by
  intro g h_g_in_present
  rcases g with ⟨ ζ, t ⟩
  cases ζ
  all_goals simp only [weak_define_ungraded] -- this will close all present roots
  all_goals ( -- this will close the remaining (nonpresent) roots
    simp only [present_roots] at h_g_in_present
    contradiction
  )

theorem weak_define_is_projection_ungraded (R : Type TR) [Ring R] :
  ∀ {g : ChevalleyGenerator A3PosRoot R}, (FreeGroup.lift (weak_define_ungraded R)) (weak_define_ungraded R g) = weak_define_ungraded R g := by
  intro g
  rcases g with ⟨ ζ, t ⟩
  cases ζ
  all_goals simp only [weak_define_ungraded, FreeGroup.lift.of, map_commutatorElement]

def weakA3Ungraded (R : Type TR) [Ring R] := PartialChevalleyGroup.mk
  weakA3System
  (weak_define_ungraded R)
  (weak_define_of_present_ungraded R)
  (weak_define_is_projection_ungraded R)

set_option hygiene false in
/-- Shorthand for building group elements from a root and ring element. -/
scoped notation (priority:=high) "⸨" ζ ", " t "⸩" =>
  (weakA3Ungraded R).pres_mk {ζ, t}

-- Instantiate macros for ungraded case

macro "declare_A3_ungraded_lin_id_inv_thms" R:term:arg root:term:arg : command =>
  `(command| declare_ungraded_lin_id_inv_thms weakA3Ungraded $R $root)

macro "declare_A3_ungraded_triv_expr_thm" R:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_ungraded_triv_expr_thm weakA3Ungraded $R $r₁ $r₂)

macro "declare_A3_ungraded_triv_comm_of_root_pair_thms" R:term:arg r₁:term:arg r₂:term:arg : command =>
  `(command| declare_ungraded_triv_comm_of_root_pair_thms weakA3Ungraded $R $r₁ $r₂)

macro "declare_A3_ungraded_single_expr_thms" R:term:arg r₁:term:arg r₂:term:arg r₃:term:arg isNeg:num n:num : command =>
  `(command| declare_ungraded_single_expr_thms weakA3Ungraded $R $r₁ $r₂ $r₃ $isNeg $n)

macro "declare_A3_ungraded_single_comm_of_root_pair_thms" R:term:arg r₁:term:arg r₂:term:arg r₃:term:arg isNeg:num n:num : command =>
  `(command| declare_ungraded_single_comm_of_root_pair_thms weakA3Ungraded $R $r₁ $r₂ $r₃ $isNeg $n)

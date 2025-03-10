import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.FreeGroup.Basic

import Steinberg.Defs.RootSystem
import Steinberg.Macro.Group

/-!

  Chevalley stuff. TODO fill in docs.

-/

namespace Steinberg

open PosRootSys

variable {Φ : Type TΦ} [PosRootSys Φ]
         {R : Type TR} [Ring R]

/--
  Generators of the Chevalley subgroup corresponding to a positive root system
  over a ring with monomial entries.
-/
structure ChevalleyGenerator (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] where
  mk ::
  ζ : Φ
  t : R

/--
  Generators of the Chevalley subgroup corresponding to a positive root system
  over a ring with monomial entries.
-/
structure GradedChevalleyGenerator (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] where
  mk ::
  ζ : Φ
  i : ℕ
  hi :  i ≤ height ζ
  t : R


namespace ChevalleyGenerator

/-- Helper function to construct and inject a `ChevalleyGenerator`. -/
def free_mk (ζ : Φ) (t : R) : FreeGroup (ChevalleyGenerator Φ R) :=
  FreeGroup.of <| (mk ζ t)

set_option hygiene false in
/--
  Shorthand for building free group elements from a root, degree, and ring element.

  Note: To re-use this notation for specific `Chevalley`-like groups,
  re-define it for that group and set the priority higher.

  Then implement delaboration to use the `free_mk` delab here.
-/
scoped notation (priority:=1000) "{{" ζ ", " t "}}" =>
  free_mk ζ t

open Lean PrettyPrinter Delaborator SubExpr in
/--
  Delaborates `free_mk` to use the `{ }` notation defined above.

  Delaboration makes it so that the infoview uses the nice notation.
-/
@[delab free_mk]
def delab_free_mk : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``free_mk 8
  let ζ ← withNaryArg 4 delab
  let i ← withNaryArg 5 delab
  let t ← withNaryArg 7 delab
  `({ $(ζ):term, $(i):term, $(t):term })


theorem eq_of_R_eq (ζ : Φ) {t : R} (u : R) (h : t = u)
    : {{ζ, t}} = {{ζ, u}} := by
  congr 1

end ChevalleyGenerator

namespace GradedChevalleyGenerator

/-- Helper function to construct and inject a `GradedChevalleyGenerator`. -/
def free_mk (ζ : Φ) (i : ℕ) (hi : i ≤ height ζ) (t : R) : FreeGroup (GradedChevalleyGenerator Φ R) :=
  FreeGroup.of <| (mk ζ i hi t)

set_option hygiene false in
/--
  Shorthand for building free group elements from a root, degree, and ring element.

  Note: To re-use this notation for specific `Chevalley`-like groups,
  re-define it for that group and set the priority higher.

  Then implement delaboration to use the `free_mk` delab here.
-/
scoped notation (priority:=1000) "{" ζ ", " i ", " t "}" =>
  free_mk ζ i (by ht) t

/-- `free_mk` but with an explicit proof term provided. -/
scoped notation (priority:=1000) "{" ζ ", " i ", " t "}'" h:max =>
  free_mk ζ i h t

open Lean PrettyPrinter Delaborator SubExpr in
/--
  Delaborates `free_mk` to use the `{ }` notation defined above.

  Delaboration makes it so that the infoview uses the nice notation.
-/
@[delab free_mk]
def delab_free_mk : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' ``free_mk 8
  let ζ ← withNaryArg 4 delab
  let i ← withNaryArg 5 delab
  let t ← withNaryArg 7 delab
  `({ $(ζ):term, $(i):term, $(t):term })

/-- Injected group elements can commute on their root heights `i` and `j`.  -/
theorem h_add_comm (ζ : Φ) (i j : ℕ) (h : i + j ≤ height ζ) (t : R)
    : {ζ, i + j, t} = {ζ, j + i, t} := by
  congr 1
  exact add_comm i j

theorem h_add_assoc (ζ : Φ) (i j k : ℕ) (h : i + j + k ≤ height ζ) (t : R)
    : {ζ, i + j + k, t} = {ζ, i + (j + k), t} := by
  congr 1
  exact add_assoc i j k

theorem eq_of_h_eq (ζ : Φ) {i : ℕ} (j : ℕ) (hij : i = j)
    : ∀ {_ : i ≤ height ζ} {t : R}, {ζ, i, t} = {ζ, j, t} := by
  intros; congr 1

theorem eq_of_R_eq (ζ : Φ) {t : R} (u : R) (h : t = u)
    : ∀ {i : ℕ} {_ : i ≤ height ζ}, {ζ, i, t} = {ζ, i, u} := by
  intros; congr 1

theorem eq_of_hR_eq (ζ : Φ) {i : ℕ} (j : ℕ) (hij : i = j) {t : R} (u : R) (htu : t = u)
    : ∀ {_ : i ≤ height ζ}, {ζ, i, t} = {ζ, j, u} := by
  intros; congr 1

end GradedChevalleyGenerator

/-

Macros and other convenience keywords when doing proofs on groups.

-/

/- Tactic and metaprogramming imports -/
import Lean.Elab.Declaration
import Lean.Elab.Tactic.Rewrite
import Mathlib.Tactic.SimpRw
import Mathlib.Util.AddRelatedDecl
import Mathlib.Tactic.CategoryTheory.Reassoc

/- Mathlib mathematics imports -/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic

/-!

See:
  - Associating: `mul_assoc_l`, `mal`, `mul_assoc_r`, `mar`
  - Group rewrite: `grw`

-/

namespace Steinberg.Macro

open Mathlib.Tactic
open Lean Meta Elab Term Tactic Parser.Tactic PrettyPrinter

/-- Shorthand for `simp_rw [← mul_assoc]`, which applies the `mul_assoc` tactic to the left. -/
macro (name := mul_assoc_l) "mul_assoc_l" : tactic => `(tactic|
  simp_rw [← mul_assoc]
)

@[inherit_doc mul_assoc_l]
macro (name := mal) "mal" : tactic => `(tactic|
  mul_assoc_l
)

/-- Shorthand for `simp_rw [mul_assoc]`, which applies the `mul_assoc` tactic to the right. -/
macro (name := mul_assoc_r) "mul_assoc_r" : tactic => `(tactic|
  simp_rw [mul_assoc]
)

@[inherit_doc mul_assoc_r]
macro (name := mar) "mar" : tactic => `(tactic|
  mul_assoc_r
)

/- CC: Use these two theorems to generate an automatic new theorem from a commutative theorem. -/

private theorem mul_assoc' {G : Type u} [Semigroup G] {b c d e : G} (h : b * c = d * e) (a : G) :
    a * b * c = a * d * e := by
  rw [mul_assoc, h, ← mul_assoc]

private theorem add_assoc' {G : Type u} [AddSemigroup G] {b c d e : G} (h : b + c = d + e) (a : G) :
    a + b + c = a + d + e := by
  rw [add_assoc, h, ← add_assoc]

/--
  An empty list of `simp` lemmas and terms.

  CC: See `Mathlib.Tactic.CategoryTheory.Reassoc` for a list of potential
      relevant lemmas, but for category theory. The problem of using a lot
      of standard group theory lemmas is that they will simplify away
      `a * 1`, which we often don't want to do in our proofs. If we find
      that we *do* need some lemmas, add them here.
-/
def groupSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``mul_left_inj, ``mul_right_inj] e

/- CC: Use these two theorems if constructing a `mul_assoc` term directly without a hole. -/

private theorem mul_assoc'' {G : Type u} [Semigroup G] (b a c : G) :
    a * b * c = a * (b * c) := by
  rw [mul_assoc]

private theorem add_assoc'' {G : Type u} [AddSemigroup G] (b a c : G) :
    a + b + c = a + (b + c) := by
  rw [add_assoc]

/--
  An attribute to automatically generate a new theorem of the same name,
  plus a suffix of `_assoc`.

  Note: This is a copy of `reassocExpr` in `Mathlib.Tactic.CategoryTheory.Reassoc`.

  Essentially, theorems with this attribute automatically generate a proof
  of that same theorem, modulo associativity. See the `private theorems` above.

  Only theorems of the form `∀ ..., a * b = c` are allowed,
  where `*` is the group-theoretic binary operation.
-/
def reassocExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType groupSimp (← mkAppM ``mul_assoc' #[e])) e

syntax (name := group_reassoc) "group_reassoc" (" (" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `group_reassoc
  descr := "Attribute for generating reassociated versions of commutator lemmas"
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| group_reassoc $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`reassoc` can only be used as a global attribute"
    addRelatedDecl src "_assoc" ref stx? fun type value levels => do
      pure (← reassocExpr (← mkExpectedTypeHint value type), levels)
  | _ => throwUnsupportedSyntax
}

/-
  CC: It's very, very hard to get `(rwRule| )` to type check, since it expects
      a `term`, while most outputs of this function are `Term.app`, which for
      whatever reason is not a `term`. So we have to open the `.Compat`
      environment to extract coercions between the `TSyntax` kinds.
      Ideally, we wouldn't need to do this.
-/
open TSyntax.Compat in
/--
  Peers into a `Syntax` object and tries to add `_assoc` to the base theorem
  used in the term.

  For example, if the term is `add_comm h₁ h₂ a b`, then this function
  returns `add_comm_assoc h₁ h₂ a b`.
-/
partial def replaceWithAssocName (stx : Syntax) : Option (TSyntax `term) :=
  let k := stx.getKind
  if k == ``Lean.Parser.Term.app then
    let assocName :=
      match stx[0].getId with
      | Name.str n s => Name.mkStr n <| s ++ "_assoc"
      | x => x
    let appNode := mkNode ``Lean.Parser.Term.app #[mkIdent assocName, stx[1]]
    -- let appTerm := mkNode `term #[appNode]
    some <| appNode
  else if k == ``Lean.Parser.Term.proj then
    replaceWithAssocName stx[0]
  else if k == ``Lean.Parser.Term.paren then
    replaceWithAssocName stx[1]
  else
    none

/--
  A special group `rw` tactic that works well with the `group_reassoc`
  attribute for theorems.

  Like `rw`, `grw` takes a list of rewrite terms and applies them in order.
  If the rewrite fails, it reassociates the identified goal/expression
  to the left and tries again. If *that* fails, it tries to extract the
  base theorem name of the rewrite rule and add `_assoc` to it.

  Basically, if a rewrite rule has the form `a * b = c`, but the identified
  goal/expression has the form `(d * a) * b`, then `grw` will use the
  `group_reassoc`-generated theorem to replace `a * b` with `c` by using
  the assoc version of the theorem instead.

  CC: This tactic is a hack. There's no guarantee that the rewrite rule
      has the right form, nor that there exists a reassoc theorem. Another
      attempt of the tactic tried to extract the sub-expression to reassociate
      instead, but constructing the right `mul_assoc` proof term was hard.
-/
elab s:"grw " cfg:optConfig rws:rwRuleSeq l:(location)? : tactic => Elab.Tactic.focus do
  /-
    For each `rwRule` in the `rwRuleSeq`, let `rewrite` process the
    rewrite term to give us a term's `Syntax`. On that syntax,
    examine its type to get out the right expression.
  -/
  withRWRulesSeq s rws fun symm term => do
    match term with
    | `(term| $e:term) => do
      let cont : TacticM Unit := (do
        match replaceWithAssocName e with
        | none => evalTactic <| ← `(tactic| skip)
        | some assoc =>
          let rule := ← do if symm then `(rwRule| ← $assoc:term) else `(rwRule| $assoc:term)
          evalTactic <| ← `(tactic|
            (rw $cfg [$rule] $l ?; try rw $cfg [← mul_assoc] $l ?);
            (try simp only [mul_assoc, mul_right_inj] $l ?);
            (try simp only [← mul_assoc, mul_left_inj] $l ?)
          )
      )

      let rwTerm := ← do if symm then `(rwRule| ← $e:term) else `(rwRule| $e:term)
      (evalTactic <| ← `(tactic|
        -- CC: Try to re-associate and simplify common terms on the right, then the left
        -- CC: Make this a tactic?
        (try simp only [mul_assoc, mul_right_inj] $l ?);
        (try simp only [← mul_assoc, mul_left_inj] $l ?);
        first
        | rw $cfg [$rwTerm] $l ?
        | try simp only [← mul_assoc, ← add_assoc] $l ?
          rw $cfg [$rwTerm] $l ?
      ))
      <|>
      cont

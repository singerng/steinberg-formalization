/-

Macros and other convenience keywords when doing proofs on groups.

-/

import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Use
import Mathlib.Algebra.Group.Defs
import Lean.Elab.Tactic.Omega
import Init.Tactics
import Init.Data.List.Sublist
import Lean.Meta.MatchUtil
import Lean.PrettyPrinter.Delaborator.Basic
import Mathlib.Util.AddRelatedDecl
import Mathlib.Tactic.CategoryTheory.Reassoc -- <<< Kevin Buzzard's suggestion

namespace Steinberg.Macro

open Mathlib.Tactic
open Lean Meta Elab Tactic Parser.Tactic PrettyPrinter

/-- Shorthand for `simp_rw [← mul_assoc]`, which applies the `mul_assoc` tactic to the left. -/
macro (name := mul_assoc_l) "mul_assoc_l" : tactic => `(tactic|
  simp_rw [← mul_assoc]
)

/-- Shorthand for `simp_rw [mul_assoc]`, which applies the `mul_assoc` tactic to the right. -/
macro (name := mul_assoc_r) "mul_assoc_r" : tactic => `(tactic|
  simp_rw [mul_assoc]
)

private theorem mul_assoc' {G : Type u} [Semigroup G] {b c d : G} (h : b * c = d) (a : G) :
    a * b * c = a * d := by
  rw [mul_assoc, h]

private theorem add_assoc' {G : Type u} [AddSemigroup G] {b c d : G} (h : b + c = d) (a : G) :
    a + b + c = a + d := by
  rw [add_assoc, h]

def emptySimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [] e

/--
  A copy of `reassocExpr` in `Mathlib.Tactic.CategoryTheory.Reassoc`.

  Essentially, theorems with this attribute automatically generate a proof
  of that same theorem, modulo associativity. See the `private theorems` above.
-/
def reassocExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType emptySimp (← mkAppM ``mul_assoc' #[e])) e

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

/--
  Extracts the leftmost variable in an `HAdd` or `HMul` expression.
-/
def extractVarExpr (e : Expr) : Option Expr :=
  dbg_trace "extractVarExpr: given {e}"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, _]) => some x
  | (``HMul.hMul, #[_, _, _, _, x, _]) => some x
  | _ =>
    dbg_trace "The expression wasn't an add or a mul: {e}"
    none

/--
  Extracts the leftmost variable from a term that is a commutative operation.

  CC: For now, assume the expression is an equality, and the LHS is what we want.

  TODO: What if the expression has a `← ` in the rewrite rule?
-/
def examineRwExpr (e : Expr) (symm : Bool := false) : MetaM (Option Expr) := do
  --dbg_trace "examineRwExpr: given {e}"
  --let e ← instantiateMVars (← whnfR (← inferType e))
  --dbg_trace "examineRwExpr: instantiated {e}"
  match e with
  | .forallE _ _ b _ => examineRwExpr b
  | .app _ _ =>
    match_expr e with
    | Eq _ x y =>
      if symm then
        return extractVarExpr y
      else
        return extractVarExpr x
    | _ => return none
  | _ => return none

def examineRwTerm (stx : Syntax) (symm : Bool := false) : TacticM (Option Expr) := withMainContext do
  --dbg_trace "examineRwTerm: given {stx}"
  let e ← Term.withSynthesize <| withMainContext do
    let eTemp ← Term.elabTerm stx none true
    let localDecl ← instantiateMVars (← whnfR (← inferType eTemp))
    return localDecl
  examineRwExpr e symm


/--
  The main attempt at a `group_rewrite` tactic.

  The strategy is to try to apply each rewrite rule in order. If rewriting
  fails, try associating all the way to the left and try again. If *that*
  fails, assume that the rewrite rule is an fvar or expression of the form
  `a * b = c`, and extract the `Expr` corresponding to `a`. Give that to
  `mul_assoc _ a` and rewrite to associate the parentheses to be around
  `a` and a possible `b` term in the goal.

  Of course, we may be working with a `Ring` and not a `Group`, so
  also try that for `add_assoc` instead.

  The `mul_assoc'` and `add_assoc'` theorems above might be useful
  to place the second argument first, so as not to wrestle with holes
  when interfacing with `rewrite` directly and not through syntax.
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
      let cont (isMul : Bool) : TacticM Unit := (do
        let rwCfg ← elabRewriteConfig cfg
        let loc := expandOptLocation (mkOptionalNode l)
        match (← examineRwTerm term symm) with
        | none => evalTactic <| ← `(tactic| skip)
        | some ext =>
          dbg_trace "withRwRules: received {term}"
          dbg_trace "extended {ext}"
          dbg_trace "isConst {ext.isConst}"
          dbg_trace ""
          dbg_trace ext
          withLocation loc
            -- This is largely a copy of `rewriteLocalDecl`,
            -- except the expression has already been calculated
            (fun fvarId => withMainContext do
              let e ← if isMul then mkAppM ``mul_assoc' #[ext] else mkAppM ``add_assoc' #[ext]
              let localDecl ← fvarId.getDecl
              let rwResult ← Term.withSynthesize <| withMainContext do
                (← getMainGoal).rewrite localDecl.type e symm (config := rwCfg)
              let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
              replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)
            )

            -- This is largely a copy of `rewriteTarget`, except with the expression provided
            (Term.withSynthesize <| withMainContext do
              let e ← if isMul then mkAppM ``mul_assoc' #[ext] else mkAppM ``add_assoc' #[ext]
              let r ← (← getMainGoal).rewrite (← getMainTarget) e symm (config := rwCfg)
              let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
              replaceMainGoal (mvarId' :: r.mvarIds)
            )
            (throwTacticEx `grw · "did not find instance of the pattern in the current goal")
      )


      if symm then
        (evalTactic <| ← `(tactic|
            first
            | rw $cfg [← $e:term] $l ?
            | try simp only [← mul_assoc, ← add_assoc] $l ?
              rw $cfg [← $e:term] $l ?
          ))
          <|> cont true
          --<|> cont false
      else
        (evalTactic <| ← `(tactic|
            first
            | rw $cfg [$e:term] $l ?
            | try simp only [← mul_assoc, ← add_assoc] $l ?
              rw $cfg [$e:term] $l ?
          ))
          <|> cont true
          --<|> cont false

#exit
    evalTactic (←
      match term with
      | `(term| $e:term) => do
        dbg_trace "match: we got a term"
        let extractedTerm ← examineRwTerm e symm
        match extractedTerm with
        | none =>
          dbg_trace "match: no extracting"
          if symm then
            `(tactic|
                first
                | rw $cfg [← $e:term] $g ?
                | try simp only [← mul_assoc, ← add_assoc] $g ?
                  rw $cfg [← $e:term] $g ?)
          else
            `(tactic|
                first
                | rw $cfg [$e:term] $g ?
                | try simp only [← mul_assoc, ← add_assoc] $g ?
                  rw $cfg [← $e:term] $g ?
            )
        | some ext =>
          dbg_trace "match: got {ext}"
          let d ← delab ext
          dbg_trace "the delab is {d}"
          if symm then
            `(tactic|
                first
                | rw $cfg [← $e:term] $g ?
                | try simp only [← mul_assoc, ← add_assoc] $g ?
                  rw $cfg [← $e:term] $g ?
                | try simp only [← mul_assoc, ← add_assoc] $g ?
                  first
                  | rw $cfg [mul_assoc _ $d:term] $g ?
                  | rw $cfg [add_assoc _ $d:term] $g ?
                  rw $cfg [← $e:term] $g ?
            )
          else
            `(tactic|
                first
                | rw $cfg [$e:term] $g ?
                | try simp only [← mul_assoc, ← add_assoc] $g ?
                  rw $cfg [$e:term] $g ?
                | try simp only [← mul_assoc, ← add_assoc] $g ?
                  first
                  | rw [mul_assoc _ $d:term] $g ?
                  | rw [add_assoc _ $d:term] $g ?
                  rw [$e:term] $g ?
            )
    )

theorem testingtesting {a b c d e : Nat} : b + c = d → a + b + c + e = a + d + e := by
  intro h
  grw [h]
  /-first
  | rw [h]
  | try simp only [← mul_assoc, ← add_assoc]
    rw [h]
  | try simp only [← mul_assoc, ← add_assoc]
    first
    | rw [mul_assoc _ b]
    | rw [add_assoc _ b]
    rw [h] -/
  --grw [h]
  done

#exit

/-
def grwRewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config) : TacticM Unit := do
  let localDecl ← fvarId.getDecl

  dbg_trace "localDecl: {localDecl.type}"
  -- Take the rw term and see if you can extract an expr from it
  let e ← Term.withSynthesize <| Term.elabTerm stx none true

  -- Now see if it's of the right form, and gives an add or a mul
  let extracted ← examineRwExpr localDecl.type symm
  let res := match extracted with
  | none =>
    dbg_trace "No extraction from {localDecl.type}"
    5
  | some ext =>
    dbg_trace "Extracted {ext} from {localDecl.type}"
    6
  dbg_trace "{res}"

  rewriteLocalDecl stx symm fvarId config
  /-let e ← Term.withSynthesize <| Term.elabTerm term none
  let localDecl ← fvarId.getDecl
  (← getMainGoal).rewrite localDecl.type e symm (config := config) -/ -/

/-
syntax (name := grwSeq) "grw" optConfig rwRuleSeq (location)? : tactic

@[tactic grwSeq] def evalGrwSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (grwRewriteLocalDecl term symm · cfg)
      (rewriteTarget term symm cfg)
      (throwTacticEx `grw · "did not find instance of the pattern in the current goal") -/

def letsTryThisAgain (stx : TSyntax `Lean.Parser.Tactic.rwRule) (symm : Bool) : TacticM Unit := do
  let extracted : Option Expr := sorry
  match extracted with
  | none =>
    evalTactic <| ← `(tactic|
      first
      | rw [$stx]
      | simp only [← mul_assoc, ← add_assoc]; rw [$stx]
    )
  | some ext =>
    let delabed ← delab ext
    evalTactic <| ← `(tactic|
      first
      | rw [$stx]
      | simp only [← mul_assoc, ← add_assoc]; rw [$stx]
      | simp only [← mul_assoc, ← add_assoc]
        rw [mul_assoc _ $delabed, $stx]
    )

theorem testing {a b c d : Nat} : a + b = c → a + b + d = c + d → True := by
  intro h₁ h₂
  grw [h₁] at h₂
  done

def printerEval (rws : List (TSyntax `Lean.Parser.Tactic.rwRule)) (loc : Location) : TacticM Unit := do
  let rws ← rws.mapM (fun x => do
    match x with
    | `(rwRule| $t:term) =>
      Term.withSynthesize <| Term.elabTerm x none
    | `(rwRule| ← $t:term) =>
      Term.withSynthesize <| Term.elabTerm x none
    | _ => Macro.throwUnsupported)
  return ()


macro (name := printer) "printer" s:rwRuleSeq l:(location)? : tactic => do
  let loc := expandOptLocation (mkOptionalNode l)
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) => do
    let rwTerms := rs.getElems.toList
    dbg_trace "{rwTerms}"
    let mappedTerms ← rwTerms.mapM (fun (t : TSyntax `Lean.Parser.Tactic.rwRule) => do
      match t with
      | `(rwRule| $e:term) =>
        dbg_trace "rw term: {e}"
        --let e ← Term.withSynthesize <| Term.elabTerm e none
        return e
        -- TODO instantiate MVars?
        --examineRwExpr e
      | `(rwRule| ← $e:term) =>
        dbg_trace "rw term: ← {e}"
        return e
      | _ => Macro.throwUnsupported
    )

    `(tactic| try rfl)
  | __ => Macro.throwUnsupported

theorem simple {a b c : Nat} : a = b → b = c → c = a := by
  intro h₁ h₂
  printer [h₁, ← h₂]
  done

#exit

/--
  The `group rewrite` tactic.

  It functions much like `rw`, except that it tries to re-associate
  the terms in the goal to apply the next rewrite rule.

  CC: The `rw` macro has this as a match statement:
  ```
    `(rwRuleSeq| [$rs,*]%$rbrak)
  ```
  What is the function of $rbrak here? It's a syntax...
-/
macro (name := grw) "grw" s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$_) => do
    let rwTerms := rs.getElems.toList
    let loc := expandOptLocation (mkOptionalNode l)
    /-let rec processTerm (t : Term) : TacticM Unit := do
      let e ← Term.withSynthesize <| Term.elabTerm t none
      return toExpr (← instantiateMVars e)
      /-let termStr ← term.toString
      if termStr.startsWith "←" then
        `(tactic| rw [← $term] $(l)?)
      else
        `(tactic| rw [$term] $(l)?) -/ -/
    `(tactic| rw [$rs,*] $(l)?)
    --let rws ← evalGrw $[rwRuleSeqItem]*
    --`(tactic| $rws)
  | _ => Macro.throwUnsupported




-- CC: TODO omit later
private def eq_comm_mp {α : Sort u} {a b : α} := (@eq_comm _ a b).mp

def examineRwTerm (t : (TSyntax `Lean.Parser.Tactic.rwRule)) : TacticM (Option Expr) := do
  -- CC: Clean up
  match t with
  | `(term| $e:term) =>
    -- TODO instantiate MVars?
    let e ← Term.withSynthesize <| Term.elabTerm e none
    examineRwExpr e
  | `(term| ← $e:term) =>
    -- Bad branch
    let e ← Term.withSynthesize <| Term.elabTerm e none
    examineRwExpr e (symm := true)

def grwTactic (loc : Location) : List (TSyntax `Lean.Parser.Tactic.rwRule) → TacticM Unit
  | [] => do
    -- If we are out of rwRules, associate back to the left and finish
    evalTactic <| ← `(tactic|
      simp_rw [← mul_assoc, ← add_assoc]
    )
  | t :: ts => do
    -- Otheriwse, get out the hole variable, and try rewriting
    match (← examineRwTerm t) with
    | some x => do
      evalTactic <| ← `(tactic|
        simp_rw [← mul_assoc, ← add_assoc] $(loc)?;
        first
        | rw [$t] $(loc)?
        | rw [mul_assoc _ `x, $t] $(loc)?
        | rw [add_assoc _ `x, $t] $(loc)?
      )
    | none =>
      evalTactic <| ← `(tactic|
        simp_rw [← mul_assoc, ← add_assoc] $(loc)?;
        rw [$t] $(loc)?
      )
      grwTactic loc ts



#exit


#exit

#check ToExpr
def grwTactic : TacticM Unit := do
  liftMetaTactic fun g => do
    g.withContext do
      let hyps := (← getLocalHyps).toList

def extractFromCommE (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, _]) => some x
  | (``HMul.hMul, #[_, _, _, _, x, _]) => some x
  | _ => none

def extractFromCommT (t : Term) : Option Term :=
  match t. with
  | (``HAdd.hAdd, #[_, _, _, _, x, _]) => some x
  | (``HMul.hMul, #[_, _, _, _, x, _]) => some x
  | _ => none

elab (name := grw) s:"grw" rws:rwRuleSeq g:(location)? : tactic => Lean.Elab.Tactic.focus do
  withSimpRWRulesSeq s rws fun symm term => do
    evalTactic (← match term with
      | `(term| $e:term) =>
        if symm then
          `(tactic|
            first
            | rfl
            | rw [← $e:term] $(g)?
            | (simp_rw [← mul_assoc]; rw [← $e:term] $(g)?)
          )
        else
          `(tactic|
            first
            | rw [$e:term] $(g)?
          )
    )

#exit
/-

CC: 12/14 while Noah was on the bus:

It seems like the following kind of calculations:

  `rw [← h_xw, mul_assoc, ← h_yz, ← mul_assoc, mul_assoc x, ← h_yw, ← mul_assoc,
    mul_assoc, h_all, ← mul_assoc]`

tries to apply simple `(x * y) = (y * x)` commutativity theorems
to a goal, but if that fails, associativity needs to be adjusted.
Usually the terms are in the right order, but if e.g. `x` and `y`
are not grouped together, then `mul_assoc` can be applied to `x`.

Develop a macro/tactic that runs through a list of commutativity hypotheses
in order and tries to `rw` them. If that fails, `← mul_assoc` continually
until fixpoint, then apply `mul_assoc` to the term on the left in the
provided hyp in the second slot, like `mul_assoc _ x`.

Figure out how to run across a list of hyps.

-/

/-
macro (name := assoc_rw) "assoc_rw" [...] : tactic => `(tactic|
  mul_assoc_l
  simp_rw [l₁, mul_assoc]
  simp_rw [mul_assoc, ← mul_assoc]
) -/

def evalGrw : List Term → TacticM Unit
  | [] => `(tactic|
      skip
    )
  | t :: ts => do
    `(tactic|
      skip
    )


  done

syntax (name := grw) "grw" rwRuleSeq (location)? : tactic

macro (name := grw) "grw" s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rws,*]%$rbrak ) =>
    `(tactic| )
    let rws ← evalGrw $[rwRuleSeqItem]*
    `(tactic| $rws)
  | _ +> Macro.throwUnsupported

@[tactic grw] elab_rules : tactic
  | `(tactic| grw $[$terms:term],*) => do
    evalGrw `($terms)


elab (name := grwSyntax) "grw" rws:rwRuleSeq g:(location)? : tactic => do


#exit

@[builtin_tactic Lean.Parser.Tactic.omega]
def evalGrw : Tactic
  | `(tactic| grw $cfg:optConfig) => do
    let cfg ← elabOmegaConfig cfg
    omegaTactic cfg
  | _ => throwUnsupportedSyntax

elab s:"simp_rw " cfg:optConfig rws:rwRuleSeq g:(location)? : tactic => focus do
  evalTactic (← `(tactic| simp%$s $[$(getConfigItems cfg)]* (failIfUnchanged := false) only $(g)?))
  withSimpRWRulesSeq s rws fun symm term => do
    evalTactic (← match term with
    | `(term| $e:term) =>
      if symm then
        `(tactic| simp%$e $cfg only [← $e:term] $g ?)
      else
        `(tactic| simp%$e $cfg only [$e:term] $g ?))

    match n with
    | .fvar h =>
      if let some v ← h.getValue? then
        rewrite e (← mkEqReflWithExpectedType e
          (mkApp3 (.const ``Nat.cast [0]) (.const ``Int []) i v))
      else
        mkAtomLinearCombo e
    | _ => match n.getAppFnArgs with
    | (``Nat.succ, #[n]) => rewrite e (.app (.const ``Int.ofNat_succ []) n)

end Steinberg.Macro

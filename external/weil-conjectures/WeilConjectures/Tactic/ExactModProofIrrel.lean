/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `exact_mod_proof_irrel`

`exact_mod_proof_irrel h` closes the goal `G` using a hypothesis `h : H` when `H` and `G` differ
only by two proofs `c₁ c₂ : P` of the same proposition, occurring at different positions in `H`
and `G` (e.g. two elaborations of the same instance of a `Prop`-valued class, one of them an
auxiliary proof constant). Such terms are definitionally equal by proof irrelevance, but when they
occur deep inside the implicit arguments of large types, checking this definitional equality can
make the kernel unfold the surrounding definitions. The tactic instead abstracts `c₁` and `c₂` to
variables `x y : P` and transports `h` along the equation `x = y` with `Eq.rec`, so that the kernel
only has to compare syntactically equal terms.
-/

public meta section

namespace ExactModProofIrrel

open Lean Meta Elab Tactic

/-- Remove all metadata annotations from an expression. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun t ↦ if let .mdata _ b := t then some (stripMData b) else none

/-- The first pair of differing subterms of `a` and `b` (in a parallel traversal), if they are
proofs. -/
partial def firstProofDiff (a b : Expr) : MetaM (Option (Expr × Expr)) := do
  if a == b then return none
  match a, b with
  | .app fa xa, .app fb xb =>
    if let some r ← firstProofDiff fa fb then return some r
    firstProofDiff xa xb
  | .lam _ ta ba _, .lam _ tb bb _ =>
    if let some r ← firstProofDiff ta tb then return some r
    firstProofDiff ba bb
  | .forallE _ ta ba _, .forallE _ tb bb _ =>
    if let some r ← firstProofDiff ta tb then return some r
    firstProofDiff ba bb
  | .proj _ _ sa, .proj _ _ sb => firstProofDiff sa sb
  | _, _ =>
    if !a.hasLooseBVars && !b.hasLooseBVars then
      if (← isProof a) then return some (a, b)
    throwError "exact_mod_proof_irrel: the terms differ at{indentExpr a}\nand{indentExpr b}"

/-- Close the goal with `h`, whose type differs from the goal only by two proofs of the same
proposition. -/
def exactModProofIrrel (h : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let H := stripMData (← instantiateMVars (← inferType h))
    let G := stripMData (← instantiateMVars (← g.getType))
    let some (c₁, c₂) ← firstProofDiff H G | g.assign h; replaceMainGoal []; return
    let P ← inferType c₁
    let subst (e x y : Expr) : Expr :=
      e.replace fun t ↦ if t == c₁ then some x else if t == c₂ then some y else none
    let term ← withLocalDeclD `x P fun x ↦ do
      withLocalDeclD `y P fun y ↦ do
        let Hxx := subst H x x
        unless Hxx == subst G x x do
          throwError "exact_mod_proof_irrel: the hypothesis and the goal differ by more \
            than{indentExpr c₁}\nand{indentExpr c₂}"
        let motive ← withLocalDeclD `b P fun b ↦ do
          withLocalDeclD `hb (← mkEq x b) fun hb ↦ do
            mkLambdaFVars #[b, hb] (← mkArrow (subst H x b) (subst G x b))
        let refl ← withLocalDeclD `hx Hxx fun hx ↦ mkLambdaFVars #[hx] hx
        withLocalDeclD `hxy (← mkEq x y) fun hxy ↦ do
          mkLambdaFVars #[x, y, hxy]
            (mkAppN (mkConst ``Eq.rec [.zero, .zero]) #[P, x, motive, refl, y, hxy])
    let pf ← mkExpectedTypeHint (← mkEqRefl c₁) (← mkEq c₁ c₂)
    g.assign (mkAppN term #[c₁, c₂, pf, h])
    replaceMainGoal []

/-- `exact_mod_proof_irrel h` closes the goal with `h` when the type of `h` and the goal differ
only by two proofs of the same proposition, possibly at several positions. -/
elab "exact_mod_proof_irrel " h:term : tactic => withMainContext do
  exactModProofIrrel (← elabTerm h none)

end ExactModProofIrrel

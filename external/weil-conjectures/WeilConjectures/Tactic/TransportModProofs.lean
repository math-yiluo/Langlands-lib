/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `transport_mod_proofs`

`transport_mod_proofs h` closes the goal `G` using a term `h : H` when `H` and `G` differ only
by closed proofs (e.g. different elaborations of the same instance of a `Prop`-valued class, some
of them auxiliary proof constants), at any number of positions, and possibly with several
different proofs of the same proposition occurring both in `H` and in `G`.

It proceeds one difference at a time: at the first position where `H` and `G` differ, with proofs
`a` in `H` and `b` in `G`, it replaces every occurrence of `b` by `a`, both in `H` and in `G`,
casting `h` and the goal along `congrArg (fun x ↦ H[b := x]) (proof_irrel b a)` and its analogue
for `G`. Each cast only asks the kernel to compare syntactically equal terms and the types of the
two proofs `a` and `b`. Unlike `exact_mod_proofs`, which casts along a single motive abstracting
all the differing proofs at once and so asks the kernel to compare the types of the chosen
representatives with those of all other proofs of their class, this does not make the kernel
unfold the large types in which the proofs occur.
-/

public meta section

namespace TransportModProofs

open Lean Meta Elab Tactic

/-- Remove all metadata annotations from an expression. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun t ↦ if let .mdata _ b := t then some (stripMData b) else none

/-- The first pair of differing subterms of `a` and `b` in a parallel traversal: either a pair of
closed proofs, or a pair of other differing subterms. -/
partial def firstDiff (a b : Expr) : MetaM (Option (Expr × Expr)) := do
  if a == b then return none
  if !a.hasLooseBVars && !b.hasLooseBVars then
    if (← isProof a) then return some (a, b)
  match a, b with
  | .app fa xa, .app fb xb =>
    if let some r ← firstDiff fa fb then return some r
    firstDiff xa xb
  | .lam _ ta ba _, .lam _ tb bb _ =>
    if let some r ← firstDiff ta tb then return some r
    firstDiff ba bb
  | .forallE _ ta ba _, .forallE _ tb bb _ =>
    if let some r ← firstDiff ta tb then return some r
    firstDiff ba bb
  | .proj _ i sa, .proj _ j sb => if i == j then firstDiff sa sb else return some (a, b)
  | _, _ => return some (a, b)

/-- For proofs `b` and `a` of the same proposition, `e[b := a]` and a proof of `e = e[b := a]`. -/
def castProof (e b a : Expr) : MetaM (Expr × Expr) := do
  let motive ← withLocalDeclD `x (← inferType b) fun x ↦ do
    mkLambdaFVars #[x] (e.replace fun t ↦ if t == b then some x else none)
  let eq ← mkAppM ``congrArg #[motive, ← mkAppM ``proof_irrel #[b, a]]
  return (e.replace fun t ↦ if t == b then some a else none, eq)

/-- Close the goal with `h`, whose type differs from the goal only by closed proofs. -/
def transportModProofs (h : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let mut H := stripMData (← instantiateMVars (← inferType h))
    let mut G := stripMData (← instantiateMVars (← g.getType))
    let mut h := h
    -- the casts `G₀ = G₁`, `G₁ = G₂`, … of the goal
    let mut casts : Array (Expr × Expr × Expr) := #[]
    repeat
      let some (a, b) ← firstDiff H G | break
      unless !a.hasLooseBVars && !b.hasLooseBVars && (← isProof b) do
        throwError "transport_mod_proofs: the terms differ at{indentExpr a}\nand{indentExpr b}"
      let (H', eH) ← castProof H b a
      h := mkAppN (mkConst ``Eq.mp [← getLevel H]) #[H, H', eH, h]
      H := H'
      let (G', eG) ← castProof G b a
      casts := casts.push (G, G', eG)
      G := G'
    for (G₀, G₁, eG) in casts.reverse do
      h := mkAppN (mkConst ``Eq.mpr [← getLevel G₀]) #[G₀, G₁, eG, h]
    g.assign h
    replaceMainGoal []

/-- `transport_mod_proofs h` closes the goal with `h` when the type of `h` and the goal differ
only by closed proofs, at any number of positions. -/
elab "transport_mod_proofs " h:term : tactic => withMainContext do
  transportModProofs (← elabTerm h none)

end TransportModProofs

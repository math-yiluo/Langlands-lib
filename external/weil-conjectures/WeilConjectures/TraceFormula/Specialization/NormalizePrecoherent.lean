/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# Identifying the `Precoherent Profinite` proofs of a goal

Statements about `ℚ̄_ℓ`-coefficients elaborated in different contexts may carry different proofs
of `Precoherent Profinite` inside the `MonObj` instances `Sheaf.monObj_sheafCompose_obj` of the
condensed ring objects (an instance found by instance search, or the auxiliary proof
`ProEtale.pointLowerStar._proof_1` reached by unification). The unifier and the kernel unfold
instead of using proof irrelevance, and time out. The tactic `normalize_precoherent` replaces all
these proofs in the goal by the first one found, by `Subsingleton.elim`.

-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory

/-- Replace, inside the `MonObj` instances `Sheaf.monObj_sheafCompose_obj` of the goal, every
`Precoherent Profinite` proof by the first one found (the normalizer of the module
`PointExchangeOnComponentBdc`). -/
elab "normalize_precoherent" : tactic => do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.Meta.whnfR (← Lean.instantiateMVars (← goal.getType))
    let isInst (e : Lean.Expr) : Bool := e.isAppOf ``Sheaf.monObj_sheafCompose_obj
    let isProof (e : Lean.Expr) : Lean.MetaM Bool := do
      let some c := e.getAppFn.constName? | return false
      unless (← Lean.getConstInfo c).type.getForallBody.isAppOf ``Precoherent do return false
      return (← Lean.Meta.inferType e).isAppOf ``Precoherent
    let proofs ← IO.mkRef (#[] : Array Lean.Expr)
    Lean.Meta.forEachExpr target fun e ↦ do
      if isInst e then
        Lean.Meta.forEachExpr e fun e' ↦ do
          if ← isProof e' then
            unless (← proofs.get).contains e' do proofs.modify (·.push e')
    let some J := target.find? fun e ↦ isInst e | throwError "no `MonObj` instance found"
    let some hStd := (J.find? (·.isAppOfArity ``coherentTopology 3)).map (·.appArg!)
      | throwError "no coherent topology found"
    let hType ← Lean.Meta.inferType hStd
    let mut goal ← goal.replaceTargetDefEq target
    let mut target := target
    for p in ← proofs.get do
      if p != hStd then
        let motive ← Lean.Meta.withLocalDeclD `h hType fun h ↦ do
          Lean.Meta.mkLambdaFVars #[h] <| target.replace fun e ↦ if isInst e then
            some (e.replace fun e' ↦ if e' == p then some h else none) else none
        let eq ← Lean.Meta.mkAppM ``Subsingleton.elim #[hStd, p]
        let propEq ← Lean.Meta.mkAppM ``congrArg #[motive, eq]
        target := motive.beta #[hStd]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar target
        goal.assign (Lean.mkAppN (Lean.mkConst ``Eq.mp [.zero])
          #[Lean.mkApp motive hStd, Lean.mkApp motive p, propEq, next])
        goal := next.mvarId!
    Lean.Elab.Tactic.replaceMainGoal [goal]

end AlgebraicGeometry.ProEtale.CondensedRing

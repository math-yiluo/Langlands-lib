/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.NatIso
public import WeilConjectures.Tactic.FirstOrderApply

/-!

# Instantiating lemmas at large concrete composites by syntactic matching

The identities of the specialization of the class of a component
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specializesComponentClass_deformation`)
compose lemmas whose statements are huge composites of six-functor maps on bounded constructible
complexes. Their statements agree up to proof arguments, to unfolding of definitions and to
different spellings of the same objects (`x.obj` and `ι.obj x`, a projection of a definition and
the corresponding field). The elaborator's unifier compares such terms through proof irrelevance
and unfolding, which takes minutes or more; the kernel, which unfolds the composites around a
difference, does not finish either. The tactics of this file avoid both:

* `instantiate_by_match c [x := e, …] as h` instantiates a lemma `c`, matching the types of the
  given arguments against the binder types of `c` syntactically (`synMatch`: metavariables are
  assigned directly, proof arguments are skipped, reducible definitions and `(F ⋙ G).obj` are
  unfolded on demand, the unifier is only used on small subterms);
* `apply_by_match c [x := e, …]` closes the goal with an instance of `c`, matching also its
  conclusion against the goal.

The given proofs (and, for `apply_by_match`, the conclusion) are transported to the instantiated
types along congruence proofs whose leaves are small (`Mathlib.Tactic.FirstOrderApply.transport`),
and the instance is added as an auxiliary theorem over the variables it uses (`sealProofClosed`),
so that the kernel checks it on its own and only compares the small differing subterms.

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- `e.hom ≫ e.inv ≫ H(eqToHom h) = 𝟙` for a natural isomorphism `e : G ⋙ H ≅ F`. -/
lemma NatIso.hom_app_comp_inv_app_comp_map_eqToHom {C D E : Type*} [Category C] [Category D]
    [Category E] {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (e : G ⋙ H ≅ F) (X : C)
    (h : G.obj X = G.obj X) : e.hom.app X ≫ e.inv.app X ≫ H.map (eqToHom h) = 𝟙 _ := by
  simp

/-- `e.hom ≫ e.inv ≫ H(eqToHom h) = H(eqToHom h')` for a natural isomorphism `e : G ⋙ H ≅ F`. -/
lemma NatIso.hom_app_comp_inv_app_comp_map_eqToHom_eq {C D E : Type*} [Category C]
    [Category D] [Category E] {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E} (e : G ⋙ H ≅ F) (X : C)
    {Y : D} (h h' : G.obj X = Y) :
    e.hom.app X ≫ e.inv.app X ≫ H.map (eqToHom h) = H.map (eqToHom h') := by
  simp

end CategoryTheory

section SynMatch
open Lean Meta

/-- Unfold `e` until it is a composite `F ⋙ G`, if it becomes one within `fuel` steps: reducible
definitions are unfolded, and a projection of a definition is unfolded by unfolding the
definition one step. -/
meta partial def unfoldToComp (e : Expr) (fuel : Nat := 20) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let e ← whnfR e
  if e.isAppOf ``CategoryTheory.Functor.comp then return some e
  let some (s, mk) ← (do
      match e with
      | .proj n i s => return some (s, fun s' => Expr.proj n i s')
      | _ =>
        let some c := e.getAppFn.constName? | return none
        let some info ← getProjectionFnInfo? c | return none
        unless e.getAppNumArgs == info.numParams + 1 do return none
        return some (e.appArg!, fun s' => mkAppN e.getAppFn (e.getAppArgs.set! info.numParams s')) :
      MetaM (Option (Expr × (Expr → Expr))))
    | return none
  let some s' ← unfoldDefinition? (← whnfR s) | return none
  unfoldToComp (mk s') (fuel - 1)

/-- `isDefEq` with a budget of its own, failing with an error (instead of a timeout of the whole
declaration) when the budget is exhausted. -/
meta def isDefEqLimited (a b : Expr) (budget : Nat := 200000) : MetaM Bool := do
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context
      (fun c => { c with maxHeartbeats := budget * 1000 }) (isDefEq a b))
    fun _ => throwError m!"synMatch: isDefEq out of budget on {a.getAppFn} vs {b.getAppFn}"

mutual
/-- Syntactic first-order matching of a pattern `p` (with metavariables) against a term `t`,
reporting the path to the first conflict. -/
meta partial def synMatch (p t : Expr) : MetaM Unit := do
  try synMatchCore p t
  catch e =>
    let p' ← instantiateMVars p
    throwError m!"{e.toMessageData}\n<- {p'.getAppFn} /{p'.getAppNumArgs} vs {t.getAppFn}"

/-- The matching step of `synMatch`: metavariables of `p` are assigned without type check,
proof arguments are skipped, `(F ⋙ G).obj X` is unfolded one step, `ι.obj m` and `ι.map f` for the
inclusion `ι` of a full subcategory are matched against projections, reducible definitions are
unfolded, and the unifier is the last resort. -/
meta partial def synMatchCore (p t : Expr) : MetaM Unit := do
  let p ← instantiateMVars p
  if p == t then return
  let p' := p.consumeMData; let t' := t.consumeMData
  if let .mvar m := p' then
    unless ← m.isAssigned do
      m.assign t'
      return
  -- `(F ⋙ G).obj X` and `(F ⋙ G).map f` are `G.obj (F.obj X)` and `G.map (F.map f)`
  let compUnfold (e : Expr) : MetaM (Option Expr) := do
    if (e.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
        e.isAppOfArity ``CategoryTheory.Functor.map 8)
        && (e.getArg! 4).isAppOf ``Functor.comp then
      let some FG' ← unfoldDefinition? (e.getArg! 4) | return none
      let e' := mkAppN e.getAppFn (e.getAppArgs.set! 4 FG')
      let some e2 ← unfoldDefinition? e' | return none
      let r ← whnfCore e2
      return some r
    return none
  if let some p2 ← compUnfold p' then return ← synMatchCore p2 t'
  if let some t2 ← compUnfold t' then return ← synMatchCore p' t2
  -- `(𝟭 C).obj X` and `(𝟭 C).map f` are `X` and `f`
  let idUnfold (e : Expr) : Option Expr :=
    if (e.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
        e.isAppOfArity ``CategoryTheory.Functor.map 8) && (e.getArg! 4).isAppOf ``Functor.id then
      some e.appArg! else none
  if let some p2 := idUnfold p' then return ← synMatchCore p2 t'
  if let some t2 := idUnfold t' then return ← synMatchCore p' t2
  -- if `F.obj X` does not match `G.obj Y`, a functor `G` that unfolds (through projections of
  -- definitions) to a composite is unfolded
  if (p'.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
      p'.isAppOfArity ``CategoryTheory.Functor.map 8) && t'.isApp &&
      t'.getAppFn.constName? == p'.getAppFn.constName? && t'.getAppNumArgs == p'.getAppNumArgs then
    let s ← saveState
    try return ← synMatchStep p' t'
    catch e =>
      s.restore
      if let some G ← unfoldToComp (t'.getArg! 4) then
        if let some t2 ← compUnfold (mkAppN t'.getAppFn (t'.getAppArgs.set! 4 G)) then
          return ← synMatchCore p' t2
      -- the same on the side of the pattern, once its functor is known
      let Fp ← instantiateMVars (p'.getArg! 4)
      if Fp.hasMVar then throw e
      let some G ← unfoldToComp Fp | throw e
      let some p2 ← compUnfold (mkAppN p'.getAppFn (p'.getAppArgs.set! 4 G)) | throw e
      return ← synMatchCore p2 t'
  synMatchStep p' t'

/-- The structural step of `synMatchCore`. -/
meta partial def synMatchStep (p' t' : Expr) : MetaM Unit := do
  -- `ι.obj m` against a projection `Y.obj`, and `ι.map f` against a projection `g.hom`
  if p'.isApp && ((p'.getAppFn.isProj &&
      (p'.getAppFn.find? (·.isAppOf ``ObjectProperty.ι)).isSome) ||
      ((p'.isAppOf ``Prefunctor.obj || p'.isAppOf ``Prefunctor.map) &&
        ((p'.getArg! 4).find? (·.isAppOf ``ObjectProperty.ι)).isSome)) then
    do
      let arg := p'.appArg!
      let tStruct? : Option Expr ← do
        match t' with
        | .proj _ _ e => pure (some e)
        | _ =>
          if let some n := t'.getAppFn.constName? then
            if (← getProjectionFnInfo? n).isSome then pure (some t'.appArg!) else pure none
          else pure none
      if let some e := tStruct? then
        return ← synMatch arg e
  match p', t' with
  | .sort u, .sort v => discard <| isLevelDefEq u v
  | .const n us, .const n' vs =>
    if n == n' && us.length == vs.length then
      for (u, v) in us.zip vs do discard <| isLevelDefEq u v
      return
    throwError m!"synMatch: constants {p'} vs {t'}"
  | .forallE _ d b _, .forallE _ d' b' _ => synMatch d d'; synMatch b b'
  | .lam _ d b _, .lam _ d' b' _ => synMatch d d'; synMatch b b'
  | .proj s i e, .proj s' i' e' =>
    if s == s' && i == i' then synMatch e e' else throwError m!"synMatch: projections"
  | .proj _ i e, _ =>
    if let some n := t'.getAppFn.constName? then
      if let some info ← getProjectionFnInfo? n then
        if info.i == i && t'.getAppNumArgs == info.numParams + 1 then
          return ← synMatch e t'.appArg!
    let t2 ← whnfR t'
    if t2 != t' then return ← synMatch p' t2
    if ← isDefEqLimited p' t' then return
    throwError m!"synMatch conflict (proj):\n{p'}\nvs\n{t'}"
  | _, _ =>
    if p'.isApp && t'.isApp && p'.getAppNumArgs == t'.getAppNumArgs then
      let fp := p'.getAppFn; let ft := t'.getAppFn
      let ok ← (do synMatch fp ft; pure true) <|> pure false
      if ok then
        let ps := p'.getAppArgs; let ts := t'.getAppArgs
        let mut deferred : Array Nat := #[]
        for i in [0:ps.size] do
          if ← (do try isProof ts[i]! catch _ => pure false) then
            let pi ← instantiateMVars ps[i]!
            if let .mvar m := pi.consumeMData then
              unless ← m.isAssigned do m.assign ts[i]!
            continue
          -- an argument whose pattern still has metavariables is retried after the others
          let s ← saveState
          try synMatch ps[i]! ts[i]!
          catch e =>
            s.restore
            unless (← instantiateMVars ps[i]!).hasExprMVar do
              throwError m!"{e.toMessageData} [arg {i}]"
            deferred := deferred.push i
        for i in deferred do
          try synMatch ps[i]! ts[i]!
          catch e => throwError m!"{e.toMessageData} [deferred arg {i}]"
        return
    let p2 ← whnfR p'
    if p2 != p' then return ← synMatch p2 t'
    let t2 ← whnfR t'
    if t2 != t' then return ← synMatch p' t2
    let p3 ← whnf p'
    if p3 != p' then
      if ← (do synMatch p3 t'; pure true) <|> pure false then return
    if ← isDefEqLimited p' t' then return
    throwError m!"synMatch conflict:\n{p'}\nvs\n{t'}"

end
end SynMatch

open Lean Meta in
/-- Add `pf : ty` as an auxiliary theorem, abstracted over the free variables it depends on
(closed under dependencies), and return its application to them. The kernel then checks `pf` on
its own; unlike `Mathlib.Tactic.FirstOrderApply.sealProof`, the statement does not carry the
whole local context (whose types are large here). -/
meta def sealProofClosed (ty pf : Expr) : MetaM Expr := do
  let ty ← instantiateMVars ty
  let pf ← instantiateMVars pf
  let mut todo := (collectFVars (collectFVars {} ty) pf).fvarIds
  let mut seen : Std.HashSet FVarId := {}
  while !todo.isEmpty do
    let fv := todo.back!
    todo := todo.pop
    if seen.contains fv then continue
    seen := seen.insert fv
    let d ← fv.getDecl
    todo := todo ++ (collectFVars (if let some v := d.value? then collectFVars {} v else {})
      (← instantiateMVars d.type)).fvarIds
  let lctx ← getLCtx
  let fvars := (seen.toArray.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index).map mkFVar
  let type ← instantiateMVars (← mkForallFVars fvars ty)
  let value ← instantiateMVars (← mkLambdaFVars fvars pf)
  let lps := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let name ← mkAuxDeclName (kind := `_match_seal)
  addDecl (.thmDecl { name, levelParams := lps, type, value })
  return mkAppN (mkConst name (lps.map mkLevelParam))
    (fvars.filter fun e => !(lctx.get! e.fvarId!).isLet)

open Lean Meta in
/-- The instance `e mvs` of a lemma, its propositional arguments transported to the instantiated
binder types along congruence proofs (`Mathlib.Tactic.FirstOrderApply.transport`), and its
conclusion. The kernel then only compares the small subterms where the types differ, instead of
unfolding the large terms around them. -/
meta def transportedApp (e : Expr) (mvs : Array Expr) : MetaM (Expr × Expr) := do
  let e ← instantiateMVars e
  let mut ty ← inferType e
  let mut vals : Array Expr := #[]
  for m in mvs do
    unless ty.isForall do ty ← whnf ty
    let d := ty.bindingDomain!
    let v ← instantiateMVars m
    let v ← if ← isProp d then
        Mathlib.Tactic.FirstOrderApply.transport v (← instantiateMVars (← inferType v)) d
      else pure v
    vals := vals.push v
    ty := ty.bindingBody!.instantiate1 v
  return (mkAppN e vals, ty)

open Lean Meta Elab Tactic in
/-- `instantiate_by_match c [x := e, …] as h`: instantiate the lemma `c`, matching the types of
the given arguments syntactically (`synMatch`), and add the result as `h`. -/
elab "instantiate_by_match " c:ident " [" args:(ident ":=" term),* "] " "as " h:ident : tactic =>
  withMainContext do
  let cst ← realizeGlobalConstNoOverload c
  let e ← mkConstWithFreshMVarLevels cst
  let ty ← inferType e
  let mut names : Array Name := #[]
  let mut t := ty
  while t.isForall do
    names := names.push t.bindingName!
    t := t.bindingBody!
  let (mvs, _, concl) ← forallMetaTelescope ty
  for a in args.getElems do
    let nm := a.raw[0].getId
    let some idx := names.findIdx? (· == nm) | throwError m!"no binder {nm}"
    let ety ← instantiateMVars (← inferType mvs[idx]!)
    let v ← elabTerm a.raw[2] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    synMatch ety (← inferType v)
    (mvs[idx]!).mvarId!.assign v
  let pf ← instantiateMVars (mkAppN e mvs)
  if pf.hasExprMVar then
    let mut un : Array Name := #[]
    for i in [0:mvs.size] do
      unless ← mvs[i]!.mvarId!.isAssigned do un := un.push names[i]!
    throwError m!"unassigned arguments remain: {un}"
  let (pf, concl) ← transportedApp e mvs
  let g ← getMainGoal
  let (_, g') ← (← g.assert h.getId concl
    (← sealProofClosed concl pf)).intro1P
  replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- `apply_by_match c [x := e, …]`: instantiate the lemma `c`, matching the types of the given
arguments and then its conclusion against the goal syntactically (`synMatch`), and close the goal
with the instance. The identification of the conclusion with the goal is left to the kernel. -/
elab "apply_by_match " c:ident " [" args:(ident ":=" term),* "]" : tactic =>
  withMainContext do
  let cst ← realizeGlobalConstNoOverload c
  let e ← mkConstWithFreshMVarLevels cst
  let ty ← inferType e
  let mut names : Array Name := #[]
  let mut t := ty
  while t.isForall do
    names := names.push t.bindingName!
    t := t.bindingBody!
  let (mvs, _, concl) ← forallMetaTelescope ty
  for a in args.getElems do
    let nm := a.raw[0].getId
    let some idx := names.findIdx? (· == nm) | throwError m!"no binder {nm}"
    let ety ← instantiateMVars (← inferType mvs[idx]!)
    let v ← elabTerm a.raw[2] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    synMatch ety (← inferType v)
    (mvs[idx]!).mvarId!.assign v
  synMatch concl (← getMainTarget)
  let pf ← instantiateMVars (mkAppN e mvs)
  if pf.hasExprMVar then
    let mut un : Array Name := #[]
    for i in [0:mvs.size] do
      unless ← mvs[i]!.mvarId!.isAssigned do un := un.push names[i]!
    throwError m!"unassigned arguments remain: {un}"
  let (pf, concl) ← transportedApp e mvs
  let g ← getMainGoal
  let target ← instantiateMVars (← g.getType)
  let pf ← Mathlib.Tactic.FirstOrderApply.transport pf concl target
  g.assign (← sealProofClosed target pf)
  replaceMainGoal []

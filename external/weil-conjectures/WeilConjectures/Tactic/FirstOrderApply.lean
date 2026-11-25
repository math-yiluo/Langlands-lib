/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Tactic.Basic

/-!

# First-order instantiation of lemmas

`fo_have h := lemma using a₁, …, aₙ` and `fo_apply lemma using a₁, …, aₙ` instantiate the
implicit arguments of `lemma` by *first-order matching* of the types of its explicit hypotheses
against the types of the given terms `aᵢ` (and, for `fo_apply`, of its conclusion against the
goal), instead of by unification.

On large terms (for instance composites of derived functors), the unifier may unfold definitions
as soon as two subterms are not syntactically equal, even when they only differ by proofs or by
the instance path of an instance, and then run out of heartbeats. First-order matching assigns a
metavariable of the pattern directly to the corresponding subterm, compares applications with
the same head argument by argument, accepts any two proofs (proof irrelevance), and only falls
back to `isDefEq` on the smallest subterms where the two sides differ. Explicit arguments
are matched before implicit ones; an implicit argument which does not match yet is retried once
the others are matched.

The kernel then still has to identify the types of the given proofs with the instantiated
hypotheses, which may again unfold large definitions. So the given proofs (and, for `fo_apply`,
the conclusion) are transported along congruence proofs of `HEq A B` built along the common
structure of `A` and `B` (`heqProofAux`), whose leaves are small; arguments `rfl` and `HEq.rfl`
are proved the same way. Finally, a proof without remaining goals is added as an auxiliary
theorem (`sealProof`), so that the kernel checks it on its own.

-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.FirstOrderApply

/-- The equations `h : α = β` inside a pattern `cast h x` met by `foMatch` against a term which is
not a cast (assigned at the end of `foInstantiate`, by congruence). -/
initialize castEqs : IO.Ref (Array (MVarId × Expr × Expr)) ← IO.mkRef #[]

/-- First-order matching of a pattern `p` (containing unassigned metavariables) against `e`. The
`cache` records the pairs already matched; failures on implicit arguments are recorded in
`defer`, to be retried once the other arguments are matched. -/
partial def foMatchAux (cache : IO.Ref (Std.HashSet (Expr × Expr))) (p e : Expr)
    (bound : Array FVarId) (defer : IO.Ref (Array (Expr × Expr))) : MetaM Bool := do
  let p := p.consumeMData
  let e := e.consumeMData
  if p == e then return true
  if (← cache.get).contains (p, e) then return true
  if !p.isMVar then
    if ← isProof e then return true
  let fallback : MetaM Bool := do
    if ← isProof e then return true
    isDefEq p e
  -- a pattern `cast h x` against a term which is not a cast: match `x`, and take `h := rfl`
  if p.isAppOfArity ``cast 4 && !e.isAppOfArity ``cast 4 then
    let args := p.getAppArgs
    if ← foMatchAux cache args[3]! e bound defer then
      let h := (← instantiateMVars args[2]!).consumeMData
      if let .mvar hm := h then
        unless ← hm.isAssigned do
          castEqs.modify (·.push (hm, args[0]!, args[1]!))
      return true
    else return false
  let r ← do
    match p with
    | .mvar m =>
      if ← m.isAssigned then
        let v ← instantiateMVars p
        if v == e then pure true else foMatchAux cache v e bound defer
      else if ← m.isDelayedAssigned then
        fallback
      else if !bound.isEmpty && (← bound.anyM fun x => exprDependsOn e x) then
        fallback
      else
        m.assign e
        pure true
    | .forallE n d₁ b₁ bi =>
      match e with
      | .forallE _ d₂ b₂ _ =>
        if ← foMatchAux cache d₁ d₂ bound defer then
          withLocalDecl n bi (← instantiateMVars d₂) fun x => do
            foMatchAux cache (b₁.instantiate1 x) (b₂.instantiate1 x) (bound.push x.fvarId!) defer
        else pure false
      | _ => fallback
    | .app .. =>
      let fp := p.getAppFn
      let fe := e.getAppFn
      let ap := p.getAppArgs
      let ae := e.getAppArgs
      let sameHead : Bool := ap.size == ae.size && match fp, fe with
        | .const n₁ l₁, .const n₂ l₂ => n₁ == n₂ && l₁.length == l₂.length
        | .fvar f₁, .fvar f₂ => f₁ == f₂
        | _, _ => false
      if sameHead then
        let n0 := (← defer.get).size
        let ok ← commitWhen do
          for (u, v) in fp.constLevels!.zip fe.constLevels! do
            unless ← isLevelDefEq u v do return false
          let finfo ← getFunInfoNArgs fp ap.size
          let isExpl (i : Nat) : Bool :=
            if h : i < finfo.paramInfo.size then finfo.paramInfo[i].binderInfo.isExplicit
            else true
          -- the explicit arguments first
          let order := (List.range ap.size).filter isExpl ++
            ((List.range ap.size).filter (fun i => !isExpl i)).reverse
          for i in order do
            unless ← foMatchAux cache ap[i]! ae[i]! bound defer do
              if !isExpl i && bound.isEmpty then
                defer.modify (·.push (ap[i]!, ae[i]!))
              else return false
          return true
        if ok then pure true else
          defer.modify (·.shrink n0)
          fallback
      else if p.isAppOfArity `CategoryTheory.Functor.map 8 &&
          e.isAppOf `CategoryTheory.InducedCategory.Hom.hom then
        -- `P.ι.map f` against `g.hom`
        let F ← instantiateMVars (p.getArg! 4)
        if F.isAppOfArity `CategoryTheory.ObjectProperty.ι 3 then
          foMatchAux cache (p.getArg! 7) e.appArg! bound defer
        else fallback
      else if fp.isConst && fe.isConst then
        let unfoldAbbrev (x : Expr) : MetaM (Option Expr) := do
          let .const n _ := x.getAppFn | return none
          unless ← isReducible n do return none
          if (← getProjectionFnInfo? n).isSome then return none
          if (← isInstance n) then return none
          unfoldDefinition? x
        if let some p' ← unfoldAbbrev p then foMatchAux cache p' e bound defer
        else if let some e' ← unfoldAbbrev e then foMatchAux cache p e' bound defer
        else fallback
      else fallback
    | .sort u => match e with
      | .sort v => isLevelDefEq u v
      | _ => fallback
    | .const n₁ l₁ => match e with
      | .const n₂ l₂ =>
        if n₁ == n₂ && l₁.length == l₂.length then
          (l₁.zip l₂).allM fun (u, v) => isLevelDefEq u v
        else fallback
      | _ => fallback
    | _ => fallback
  if r then cache.modify (·.insert (p, e))
  return r

/-- First-order matching of a pattern `p` (containing unassigned metavariables) against `e`. -/
def foMatch (p e : Expr) : MetaM Bool := do
  let cache ← IO.mkRef {}
  let defer ← IO.mkRef #[]
  unless ← foMatchAux cache p e #[] defer do return false
  for _round in [:3] do
    let ds ← defer.get
    if ds.isEmpty then return true
    defer.set #[]
    for (p, e) in ds do
      let p ← instantiateMVars p
      unless p == e do
        unless ← foMatchAux cache p e #[] defer do return false
  return (← defer.get).isEmpty

/-- Elaborate a lemma name to its constant (with fresh universe metavariables), keeping all its
binders; other terms are elaborated as usual. -/
def elabLemma (f : Term) : TacticM Expr := do
  if f.raw.isIdent then
    if let some c := (← resolveGlobalName f.raw.getId).head? then
      if c.2.isEmpty then return ← mkConstWithFreshMVarLevels c.1
  elabTerm f none

/-- Normalize the head of an object `F.obj X` for `F` a composite, an inclusion `P.ι` or `𝟭`, and
of a morphism `P.ι.map f` to `f.hom`. -/
partial def normObj (e : Expr) : MetaM Expr := do
  if e.isAppOfArity `CategoryTheory.Functor.obj 6 then
    let F := e.getArg! 4
    let x := e.getArg! 5
    if F.isAppOfArity `CategoryTheory.Functor.comp 8 then
      let .const _ ls := F.getAppFn | return e
      let [vC, vD, vE, uC, uD, uE] := ls | return e
      let cs := F.getAppArgs
      let inner := mkAppN (mkConst `CategoryTheory.Functor.obj [vC, vD, uC, uD])
        #[cs[0]!, cs[1]!, cs[2]!, cs[3]!, cs[6]!, x]
      return ← normObj (mkAppN (mkConst `CategoryTheory.Functor.obj [vD, vE, uD, uE])
        #[cs[2]!, cs[3]!, cs[4]!, cs[5]!, cs[7]!, inner])
    if F.isAppOfArity `CategoryTheory.ObjectProperty.ι 3 then
      return ← mkAppM `CategoryTheory.ObjectProperty.FullSubcategory.obj #[x]
    if F.isAppOfArity `CategoryTheory.Functor.id 2 then
      return x
  if e.isAppOfArity `CategoryTheory.Functor.map 8 then
    let F := e.getArg! 4
    if F.isAppOfArity `CategoryTheory.ObjectProperty.ι 3 then
      try return ← mkAppM `CategoryTheory.InducedCategory.Hom.hom #[e.getArg! 7]
      catch _ => return e
  return e

/-- A cheap test for two terms to be definitionally equal: equal up to proofs, to `normObj` and
to the unfolding of head constants. -/
partial def plausibleEq (a b : Expr) (fuel : Nat := 64) : MetaM Bool := do
  if a == b then return true
  if fuel == 0 then return false
  if (← isProof a) then return (← isProof b)
  if a.isAppOfArity ``cast 4 then return ← plausibleEq (a.getArg! 3) b (fuel - 1)
  if b.isAppOfArity ``cast 4 then return ← plausibleEq a (b.getArg! 3) (fuel - 1)
  let a ← normObj a
  let b ← normObj b
  if a == b then return true
  let fa := a.getAppFn
  let fb := b.getAppFn
  let as := a.getAppArgs
  let bs := b.getAppArgs
  if fa == fb && as.size == bs.size then
    for i in [:as.size] do
      unless ← plausibleEq as[i]! bs[i]! (fuel - 1) do return false
    return true
  let unf (x : Expr) : MetaM (Option Expr) := do
    let .const n _ := x.getAppFn | return none
    unless ← isReducible n do return none
    if (← getProjectionFnInfo? n).isSome then return none
    unfoldDefinition? x
  if let some a' ← unf a then return ← plausibleEq a' b (fuel - 1)
  if let some b' ← unf b then return ← plausibleEq a b' (fuel - 1)
  -- one delta step of a non-reducible head, if it produces the head of the other side
  let unf1 (x : Expr) (target : Expr) : MetaM (Option Expr) := do
    let .const n _ := x.getAppFn | return none
    if (← getProjectionFnInfo? n).isSome then return none
    let some x' ← unfoldDefinition? x | return none
    let x' := x'.headBeta
    if x'.getAppFn.constName? == target.getAppFn.constName? then return some x'
    return none
  if let some a' ← unf1 a b then return ← plausibleEq a' b (fuel - 1)
  if let some b' ← unf1 b a then return ← plausibleEq a b' (fuel - 1)
  return false

/-- A proof of `HEq a b` for two definitionally equal terms, by congruence along their common
structure; the leaves are closed by `HEq.refl` (definitional unfolding at the leaves only) or by
proof irrelevance. -/
partial def heqProofAux (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) (a b : Expr) :
    MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if let some p := (← cache.get)[(a, b)]? then return p
  let a ← normObj a
  let b ← normObj b
  let r ← do
    if (← isProof a) && (← isProof b) then
      pure (mkApp4 (mkConst ``proof_irrel_heq) (← inferType a) (← inferType b) a b)
    else if b.isAppOfArity ``cast 4 then
      -- `HEq a (cast h x)` from `HEq a x` and `cast_heq h x`
      let x := b.getArg! 3
      let h₁ ← heqProofAux cache a x
      let h₂ ← mkHEqSymm (← mkAppM ``cast_heq #[b.getArg! 2, x])
      mkHEqTrans h₁ h₂
    else if a.isAppOfArity ``cast 4 then
      let x := a.getArg! 3
      let h₁ ← mkAppM ``cast_heq #[a.getArg! 2, x]
      let h₂ ← heqProofAux cache x b
      mkHEqTrans h₁ h₂
    else if a.isForall && b.isForall &&
        (← isProp a) && (← isProp b) then
      -- `forall_congr` along the bodies
      let α := a.bindingDomain!
      let u ← getLevel α
      let h ← withLocalDecl a.bindingName! a.binderInfo α fun x => do
        let pa := a.bindingBody!.instantiate1 x
        let pb := b.bindingBody!.instantiate1 x
        let h ← heqProofAux cache pa pb
        let h := mkApp4 (mkConst ``eq_of_heq [1]) (mkSort 0) pa pb h
        mkLambdaFVars #[x] h
      let p := mkLambda a.bindingName! a.binderInfo α a.bindingBody!
      let q := mkLambda b.bindingName! b.binderInfo α b.bindingBody!
      let e := mkApp4 (mkConst ``forall_congr [u]) α p q h
      pure (mkApp3 (mkConst ``heq_of_eq [1]) (mkSort 0) a b |>.app e)
    else
      let fa := a.getAppFn
      let fb := b.getAppFn
      let as := a.getAppArgs
      let bs := b.getAppArgs
      let finfo ← getFunInfoNArgs fa as.size
      -- descend only if the explicit arguments are plausibly definitionally equal
      let argsOk : MetaM Bool := do
        for i in [:as.size] do
          let x := as[i]!
          let y := bs[i]!
          if x == y then continue
          if h : i < finfo.paramInfo.size then
            unless finfo.paramInfo[i].binderInfo.isExplicit do continue
          if (← isProof x) then continue
          let x' ← normObj x
          let y' ← normObj y
          let hd (e : Expr) : Option Name := match e.getAppFn with
            | .const n _ => some n
            | _ => none
          if (hd x').isSome && hd x' == hd y' && x'.getAppNumArgs == y'.getAppNumArgs then
            continue
          unless ← plausibleEq x y do
            return false
        return true
      let sameHead : MetaM Bool := do
        if fa == fb then return true
        match fa, fb with
        | .const n₁ l₁, .const n₂ l₂ =>
          if n₁ == n₂ && l₁.length == l₂.length then
            (l₁.zip l₂).allM fun (u, v) => isLevelDefEq u v
          else return false
        | _, _ => return false
      let ok ← if as.size == bs.size && as.size > 0 then
          (do if ← sameHead then argsOk else pure false) else pure false
      if ok then
        let lem ← match fa with
          | .const n ls => do
            match ← mkHCongrWithArityForConst? n ls as.size with
            | some l => pure l
            | none => mkHCongrWithArity fa as.size
          | _ => mkHCongrWithArity fa as.size
        let mut args : Array Expr := #[]
        for i in [:as.size] do
          let h ← heqProofAux cache as[i]! bs[i]!
          let h ← if lem.argKinds[i]? == some .eq then
              (if as[i]! == bs[i]! then mkEqRefl as[i]! else do
                let α ← inferType as[i]!
                let u ← getLevel α
                pure (mkApp4 (mkConst ``eq_of_heq [u]) α as[i]! bs[i]! h))
            else pure h
          args := args.push as[i]! |>.push bs[i]! |>.push h
        pure (mkAppN lem.proof args)
      else
        mkHEqRefl a
  cache.modify (·.insert (a, b) r)
  return r

/-- Transport a proof `a : A` to `B`, along `heqProofAux` (if `A` and `B` differ). -/
def transport (a A B : Expr) : MetaM Expr := do
  if A == B then return a
  let h ← heqProofAux (← IO.mkRef {}) A B
  return mkApp4 (mkConst ``Eq.mp [.zero]) A B
    (mkApp4 (mkConst ``eq_of_heq [1]) (mkSort 0) A B h) a

/-- A proof of `l = r` (or `HEq l r`) for definitionally equal `l` and `r`, by congruence along
their common structure (`heqProofAux`), so that the kernel only compares the small subterms which
differ. -/
def congrProof (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  if let some (α, l, r) := ty.eq? then
    if l == r then return some (← mkEqRefl l)
    let h ← heqProofAux (← IO.mkRef {}) l r
    let u ← getLevel α
    return some (mkApp4 (mkConst ``eq_of_heq [u]) α l r h)
  if let some (_, l, _, r) := ty.heq? then
    return some (← heqProofAux (← IO.mkRef {}) l r)
  return none

/-- Instantiate the explicit hypotheses of `fe` by the terms `args` (in order: `_` leaves the
hypothesis open, `rfl` and `HEq.rfl` prove it by congruence), after matching the conclusion against
`target?` if given. The implicit arguments are found by first-order matching; the given proofs and
the conclusion are transported to the instantiated types along congruence proofs. Returns the
instantiated proof and the remaining hypotheses. -/
def foInstantiate (fe : Expr) (args : Array Term) (target? : Option Expr) :
    TacticM (Expr × Array MVarId) := do
  castEqs.set #[]
  let fty ← inferType fe
  let (mvs, bis, concl) ← forallMetaTelescopeReducing fty
  if let some target := target? then
    unless ← foMatch concl target do
      throwError "fo_apply: the conclusion{indentExpr concl}\ndoes not match the goal"
  -- the explicit binders, with the given terms
  let mut given : Array (Nat × Nat) := #[]
  let mut refls : Array Nat := #[]
  let mut tacs : Array (Nat × Nat) := #[]
  let mut lates : Array (Nat × Term) := #[]
  let mut newGoals : Array MVarId := #[]
  let mut k := 0
  for i in [:mvs.size] do
    if bis[i]! == .default then
      if h : k < args.size then
        let isBy : Bool := args[k].raw.isOfKind ``Lean.Parser.Term.byTactic ||
          (args[k].raw.isOfKind ``Lean.Parser.Term.paren &&
            args[k].raw[1].isOfKind ``Lean.Parser.Term.byTactic)
        if isBy then
          tacs := tacs.push (i, k)
        else if args[k].raw.isOfKind ``Lean.Parser.Term.app &&
            args[k].raw[0].isIdent && args[k].raw[0].getId == `fo_late then
          lates := lates.push (i, ⟨args[k].raw[1][0]⟩)
        else if args[k].raw.isOfKind ``Lean.Parser.Term.hole then
          newGoals := newGoals.push mvs[i]!.mvarId!
        else if args[k].raw.isIdent &&
            (args[k].raw.getId == `rfl || args[k].raw.getId == `HEq.rfl) then
          refls := refls.push i
        else
          given := given.push (i, k)
        k := k + 1
      else
        newGoals := newGoals.push mvs[i]!.mvarId!
  -- elaborate the given terms; match the proofs first, then the data
  let mut elabd : Array (Nat × Nat × Expr × Bool) := #[]
  for (i, k') in given do
    let a ← elabTerm args[k']! none
    elabd := elabd.push (i, k', a, ← isProof a)
  for pass in [true, false] do
    for (i, k', a, isPf) in elabd do
      if isPf == pass then
        let ty ← instantiateMVars (← inferType mvs[i]!)
        let aty ← instantiateMVars (← inferType a)
        unless ← foMatch ty aty do
          throwError "fo_apply: could not match argument {k' + 1} of type{indentExpr aty}"
        if !isPf then mvs[i]!.mvarId!.assign a
  for i in [:mvs.size] do
    if bis[i]! == .instImplicit then
      unless ← mvs[i]!.mvarId!.isAssigned do
        mvs[i]!.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType mvs[i]!)))
  -- the equations of the casts, by congruence
  for (m, α, β) in ← castEqs.get do
    unless ← m.isAssigned do
      let some p ← congrProof (← mkEq (← instantiateMVars α) (← instantiateMVars β)) | pure ()
      m.assign p
  -- reflexivity arguments, by congruence
  for i in refls do
    let some p ← congrProof (← inferType mvs[i]!)
      | throwError "fo_apply: `rfl` for a hypothesis which is not an equation"
    mvs[i]!.mvarId!.assign p
  -- transport the given proofs to the instantiated hypotheses
  for (i, _, a, isPf) in elabd do
    if isPf then
      let B ← instantiateMVars (← inferType mvs[i]!)
      let A ← instantiateMVars (← inferType a)
      mvs[i]!.mvarId!.assign (← transport a A B)
  -- the hypotheses given by tactic blocks
  for (i, kt) in tacs do
    let v ← elabTermEnsuringType args[kt]! (← instantiateMVars (← inferType mvs[i]!))
    Term.synthesizeSyntheticMVarsNoPostponing
    mvs[i]!.mvarId!.assign (← instantiateMVars v)
  -- the hypotheses given by `fo_late t`: transported, without matching
  for (i, t) in lates do
    let a ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let a ← instantiateMVars a
    let B ← instantiateMVars (← inferType mvs[i]!)
    if B.hasMVar then
      throwError "fo_apply: the hypothesis given by `fo_late` is not determined{indentExpr B}"
    mvs[i]!.mvarId!.assign (← transport a (← instantiateMVars (← inferType a)) B)
  let goals ← newGoals.filterM fun g => return !(← g.isAssigned)
  let pf ← instantiateMVars (mkAppN fe mvs)
  match target? with
  | some target => return (← transport pf (← instantiateMVars (← inferType pf)) target, goals)
  | none => return (pf, goals)

/-- Add `pf : ty` as an auxiliary theorem, abstracted over the local context, and return its
application to the local context. The kernel then checks `pf` on its own, and the proof using it
only refers to the auxiliary theorem. (`mkAuxTheorem` computes a minimal closure instead, which
is very slow on large terms.) -/
def sealProof (ty pf : Expr) : MetaM Expr := do
  -- the local hypotheses `pf` and `ty` depend on, closed under dependencies
  let lctx ← getLCtx
  let mut needed := (collectFVars (collectFVars {} ty) pf).fvarSet
  for d in lctx.decls.toArray.reverse do
    if let some d := d then
      if needed.contains d.fvarId then
        needed := (collectFVars { fvarSet := needed } d.type).fvarSet
  let fvars := lctx.foldl (init := #[]) fun acc d =>
    if needed.contains d.fvarId && !d.isLet then acc.push d.toExpr else acc
  let type ← instantiateMVars (← mkForallFVars fvars ty)
  let value ← instantiateMVars (← mkLambdaFVars fvars pf)
  let lps := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let name ← mkAuxDeclName (kind := `_fo_seal)
  addDecl (.thmDecl { name, levelParams := lps, type, value })
  return mkAppN (mkConst name (lps.map mkLevelParam)) fvars

/-- `fo_have h := lemma using a₁, …, aₙ` adds `h : (the conclusion of lemma)`, where the
explicit hypotheses of `lemma` are the `aᵢ` (`_` for a hypothesis left as a new goal) and the
implicit arguments are found by first-order matching of the types. -/
elab "fo_have " h:ident " := " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let fe ← elabLemma f
    let (pf, newGoals) ← foInstantiate fe args.getElems none
    let ty ← instantiateMVars (← inferType pf)
    let pf ← instantiateMVars pf
    let pf ← if newGoals.isEmpty && !pf.hasMVar then sealProof ty pf else pure pf
    let g' ← (← getMainGoal).assert h.getId ty pf
    let (_, g'') ← g'.intro1P
    replaceMainGoal (g'' :: newGoals.toList)

/-- `fo_apply lemma using a₁, …, aₙ` closes the goal by `lemma`, matching its conclusion against
the goal and its explicit hypotheses against the `aᵢ` first-order (`_` for a hypothesis left as
a new goal). -/
elab "fo_apply " f:term:max " using " args:term,* : tactic =>
  withMainContext do
    let g ← getMainGoal
    let fe ← elabLemma f
    let (pf, newGoals) ← foInstantiate fe args.getElems (some (← instantiateMVars (← g.getType)))
    let pf ← instantiateMVars pf
    let pf ← if newGoals.isEmpty && !pf.hasMVar then
      sealProof (← instantiateMVars (← g.getType)) pf else pure pf
    g.assign pf
    replaceMainGoal newGoals.toList

end Mathlib.Tactic.FirstOrderApply

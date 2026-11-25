/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Tactic.FirstOrderApply

/-!

# Closing a goal by a definitionally equal hypothesis, kernel-friendly

`transport_exact h` closes the goal by `h` when the type of `h` and the goal are definitionally
equal but spelled differently (for instance objects of a full subcategory against their ambient
forms, inside large composites of derived functors). The kernel may unfold such large terms in
the wrong order and run out of heartbeats on `exact h`, even though each pair of differing
subterms is definitionally equal in milliseconds.

As in `Mathlib.Tactic.FirstOrderApply.transport`, `h` is transported along a congruence proof of
`HEq A B` built along the common structure of its type `A` and the goal `B`, whose leaves are
closed by `HEq.refl` and are small; the proof is then added as an auxiliary theorem
(`Mathlib.Tactic.FirstOrderApply.sealProof`). The difference is in the descent: two applications
with the same head are compared argument by argument as soon as each pair of explicit arguments
is plausibly equal (`Mathlib.Tactic.FirstOrderApply.plausibleEq`) *or* definitionally equal
within a small heartbeat budget. This keeps the leaves small when an explicit argument is an
object spelled in two ways (e.g. `α.app E` against `α.app E'`), where `HEq.refl` on the whole
application would make the kernel unfold `α`.

-/

public meta section

open Lean Meta Elab Tactic Mathlib.Tactic.FirstOrderApply

namespace Mathlib.Tactic.TransportExact

/-- Whether `x` and `y` are definitionally equal, within a small heartbeat budget. -/
def isDefEqBounded (x y : Expr) : MetaM Bool :=
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := 200000 * 1000 }) do
      Core.withCurrHeartbeats (withNewMCtxDepth (isDefEq x y)))
    (fun _ => pure false)

/-- A proof of `HEq a b` for two definitionally equal terms, by congruence along their common
structure; the leaves are closed by `HEq.refl` or by proof irrelevance. -/
partial def heqProof (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) (a b : Expr) :
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
    else
      let fa := a.getAppFn
      let fb := b.getAppFn
      let as := a.getAppArgs
      let bs := b.getAppArgs
      let finfo ← getFunInfoNArgs fa as.size
      -- descend if the explicit arguments are plausibly or cheaply definitionally equal
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
          if ← plausibleEq x y then continue
          unless ← isDefEqBounded x y do return false
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
          let h ← heqProof cache as[i]! bs[i]!
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

/-- `transport_exact h` closes the goal by `h`, whose type is definitionally equal to the goal,
along a congruence proof with small leaves, added as an auxiliary theorem. -/
elab "transport_exact " h:term : tactic => withMainContext do
  let g ← getMainGoal
  let a ← elabTerm h none
  let A ← instantiateMVars (← inferType a)
  let B ← instantiateMVars (← g.getType)
  let pf ← if A == B then pure a else do
    let e ← heqProof (← IO.mkRef {}) A B
    pure (mkApp4 (mkConst ``Eq.mp [.zero]) A B
      (mkApp4 (mkConst ``eq_of_heq [1]) (mkSort 0) A B e) a)
  let pf ← instantiateMVars pf
  if pf.hasExprMVar then throwError "transport_exact: the proof has unassigned metavariables"
  g.assign (← sealProof B pf)
  replaceMainGoal []

/-- `transport_rfl` closes a goal `l = r` with `l` and `r` definitionally equal but spelled
differently, along a congruence proof with small leaves, added as an auxiliary theorem. -/
elab "transport_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let B ← instantiateMVars (← g.getType)
  let some (α, l, r) := (← whnfR B).eq? | throwError "transport_rfl: the goal is not an equation"
  let e ← heqProof (← IO.mkRef {}) l r
  let u ← getLevel α
  let pf ← instantiateMVars (mkApp4 (mkConst ``eq_of_heq [u]) α l r e)
  g.assign (← sealProof B pf)
  replaceMainGoal []

end Mathlib.Tactic.TransportExact

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `exact_mod_proofs`

`exact_mod_proofs h` closes the goal `G` using a term `h : H` when, at every position where `H`
and `G` differ, both subterms are closed proofs (e.g. different elaborations of the same instance
of a `Prop`-valued class, some of them auxiliary proof constants), or closed definitionally equal
terms (e.g. two paths to the same data-carrying instance), which are left to the kernel. Unlike
`exact_mod_proof_irrel`, any number of distinct proofs may occur.

The proofs are definitionally equal by proof irrelevance, but when they occur deep inside the
implicit arguments of large types, checking this definitional equality can make the unifier and
the kernel unfold the surrounding definitions. The tactic instead chooses a representative `r` in
each class of proofs identified by the differences, and casts both `h` and the goal along the
motives `fun z⃗ ↦ H[c⃗ := z⃗]` and `fun z⃗ ↦ G[c⃗ := z⃗]` (all the other proofs `c` replaced
simultaneously) and the equations `c = r` (closed by `rfl`, checked by proof irrelevance on the
proofs alone). The two casted types differ only at the definitionally equal non-proof terms, if
any.

The variant `cast_proofs h` casts the goal along `proof_irrel` one pair of differing proofs at a
time, at exactly the positions where they differ. Its motives stay close to the goal itself, so
the kernel check stays cheap even with thousands of differing positions, where the single
simultaneous cast of `exact_mod_proofs` can exhaust the kernel.
-/

public meta section

namespace ExactModProofs

open Lean Meta Elab Tactic

/-- Remove all metadata annotations from an expression. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun t ↦ if let .mdata _ b := t then some (stripMData b) else none

/-- The pairs of minimal differing subterms of `a` and `b`, in a parallel traversal, which are
required to be closed; pairs of proofs are recorded, pairs of other terms are required to be
definitionally equal (they are compared by the kernel in the end). -/
partial def proofDiffs (a b : Expr) (acc : Array (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := do
  if a == b then return acc
  let leaf : MetaM (Array (Expr × Expr)) := do
    if !a.hasLooseBVars && !b.hasLooseBVars then
      if (← isProof a) then return acc.push (a, b)
      if (← isDefEq a b) then return acc
    throwError "exact_mod_proofs: the terms differ at{indentExpr a}\nand{indentExpr b}"
  match a, b with
  | .app .., .app .. =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if as.size != bs.size || (fa != fb && !(fa.isLambda && fb.isLambda)) then return ← leaf
    let mut acc ← if fa == fb then pure acc else proofDiffs fa fb acc
    for i in [:as.size] do
      acc ← proofDiffs as[i]! bs[i]! acc
    return acc
  | .lam _ ta ba _, .lam _ tb bb _ => proofDiffs ba bb (← proofDiffs ta tb acc)
  | .forallE _ ta ba _, .forallE _ tb bb _ => proofDiffs ba bb (← proofDiffs ta tb acc)
  | .letE _ ta va ba _, .letE _ tb vb bb _ =>
    proofDiffs ba bb (← proofDiffs va vb (← proofDiffs ta tb acc))
  | .proj _ i sa, .proj _ j sb => if i == j then proofDiffs sa sb acc else leaf
  | _, _ => leaf

/-- The representative of `e` for the identifications `rep`. -/
partial def find (rep : Std.HashMap Expr Expr) (e : Expr) : Expr :=
  match rep[e]? with
  | some e' => if e' == e then e else find rep e'
  | none => e

/-- Replace every occurrence of `cs[i]` in `e` by `zs[i]` (outermost occurrences first). -/
def replaceAll (e : Expr) (cs zs : Array Expr) : Expr :=
  e.replace fun t ↦ (cs.idxOf? t).map fun i ↦ zs[i]!

/-- The proof of `m cs[0] … cs[n-1] = m rs[0] … rs[n-1]`, for proofs `cs[i]`, `rs[i]` of the
propositions `Ps[i]` and `m : Ps[0] → … → Ps[n-1] → Prop`, by `congr` and proof irrelevance. -/
def congrProofs (m : Expr) (cs rs Ps : Array Expr) : MetaM Expr := do
  let mut e ← mkEqRefl m
  for i in [:cs.size] do
    -- the type `Ps[i+1] → … → Ps[n-1] → Prop` of the partial applications after step `i`
    let β := (Ps.extract (i + 1) Ps.size).foldr (fun P b ↦ mkForall `x .default P b) (.sort .zero)
    let α := Ps[i]!
    let f₁ := mkAppN m (cs.extract 0 i)
    let f₂ := mkAppN m (rs.extract 0 i)
    let eqi ← mkExpectedTypeHint (← mkEqRefl cs[i]!) (← mkEq cs[i]! rs[i]!)
    e := mkAppN (mkConst ``congr [.zero, .succ .zero]) #[α, β, f₁, f₂, cs[i]!, rs[i]!, e, eqi]
  return e

/-- Close the goal with `h`, whose type differs from the goal only by proofs. -/
def exactModProofs (h : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let H := stripMData (← instantiateMVars (← inferType h))
    let G := stripMData (← instantiateMVars (← g.getType))
    let diffs ← proofDiffs H G #[]
    -- identify the proofs of each pair
    let mut rep : Std.HashMap Expr Expr := {}
    for (a, b) in diffs do
      let ra := find rep a
      let rb := find rep b
      if ra != rb then rep := rep.insert rb ra
    let cs := rep.toArray.filterMap fun (c, _) ↦ if find rep c == c then none else some c
    if cs.isEmpty then
      g.assign h
      replaceMainGoal []
      return
    let rs := cs.map (find rep)
    let Ps ← cs.mapM fun c ↦ inferType c
    -- the motives `fun z ↦ H[cs := z]` and `fun z ↦ G[cs := z]`
    let (mH, mG) ← withLocalDeclsDND (Ps.map (`z, ·)) fun zs ↦ do
      return (← mkLambdaFVars zs (replaceAll H cs zs), ← mkLambdaFVars zs (replaceAll G cs zs))
    let eH ← congrProofs mH cs rs Ps
    let eG ← congrProofs mG cs rs Ps
    let h' := mkAppN (mkConst ``Eq.mp [.zero]) #[mkAppN mH cs, mkAppN mH rs, eH, h]
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkAppN mG rs).headBeta
    g.assign (mkAppN (mkConst ``Eq.mpr [.zero]) #[mkAppN mG cs, mkAppN mG rs, eG, g'])
    g'.mvarId!.assign h'
    replaceMainGoal []

/-- `exact_mod_proofs h` closes the goal with `h` when the type of `h` and the goal differ only
by closed proofs, at any number of positions, and by closed definitionally equal terms. -/
elab "exact_mod_proofs " h:term : tactic => withMainContext do
  exactModProofs (← elabTerm h none)

/-- The pairs of outermost differing closed proofs of `a` and `b`, in a parallel traversal; where
the two terms have different shapes, the subterms are required to be closed and definitionally
equal (they are compared by the kernel in the end). -/
partial def proofPairs (a b : Expr) (acc : Array (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := do
  if a == b then return acc
  if !a.hasLooseBVars && !b.hasLooseBVars && (← isProof a) then return acc.push (a, b)
  let leaf : MetaM (Array (Expr × Expr)) := do
    if !a.hasLooseBVars && !b.hasLooseBVars then
      if (← withReducible (isDefEq a b)) then return acc
      if (← isDefEq a b) then return acc
    throwError "cast_proofs: the terms differ at{indentExpr a}\nand{indentExpr b}"
  match a, b with
  | .app .., .app .. =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if as.size != bs.size || (fa != fb && !(fa.isLambda && fb.isLambda)) then return ← leaf
    try
      let mut acc ← if fa == fb then pure acc else proofPairs fa fb acc
      for i in [:as.size] do
        acc ← proofPairs as[i]! bs[i]! acc
      return acc
    catch _ => leaf
  | .lam _ ta ba _, .lam _ tb bb _ => proofPairs ba bb (← proofPairs ta tb acc)
  | .forallE _ ta ba _, .forallE _ tb bb _ => proofPairs ba bb (← proofPairs ta tb acc)
  | .letE _ ta va ba _, .letE _ tb vb bb _ =>
    proofPairs ba bb (← proofPairs va vb (← proofPairs ta tb acc))
  | .proj _ i sa, .proj _ j sb => if i == j then proofPairs sa sb acc else leaf
  | _, _ => leaf

/-- Replace in `g` the positions where `g` has `b` and the parallel term `h` has `a` by `z`. -/
partial def abstractPair (g h a b z : Expr) : Expr :=
  if g == h then g
  else if g == b && h == a then z
  else match g, h with
  | .app fg ag, .app fh ah => g.updateApp! (abstractPair fg fh a b z) (abstractPair ag ah a b z)
  | .lam _ tg bg _, .lam _ th bh _ =>
    g.updateLambdaE! (abstractPair tg th a b z) (abstractPair bg bh a b z)
  | .forallE _ tg bg _, .forallE _ th bh _ =>
    g.updateForallE! (abstractPair tg th a b z) (abstractPair bg bh a b z)
  | .letE _ tg vg bg _, .letE _ th vh bh _ =>
    g.updateLet! (abstractPair tg th a b z) (abstractPair vg vh a b z)
      (abstractPair bg bh a b z) false
  | .proj _ i sg, .proj _ j sh => if i == j then g.updateProj! (abstractPair sg sh a b z) else g
  | _, _ => g

/-- Close the goal with `h`, whose type differs from the goal only by closed proofs (and closed
definitionally equal terms), by casting the goal along `proof_irrel`, one pair of differing
proofs at a time. -/
def castProofs (h : Expr) : TacticM Unit := do
  let mut g ← getMainGoal
  let H := stripMData (← instantiateMVars (← inferType h))
  let mut G := stripMData (← instantiateMVars (← g.getType))
  g ← g.replaceTargetDefEq G
  -- casting along a pair may expose new pairs inside the types of the proofs
  for _ in [:20] do
    let diffs ← proofPairs H G #[]
    if diffs.isEmpty then break
    let mut pairs : Array (Expr × Expr) := #[]
    for p in diffs do
      unless pairs.contains p do pairs := pairs.push p
    for (a, b) in pairs do
      let Pb ← inferType b
      -- the motive `fun z ↦ G[b := z]`, at the positions where `H` has `a`
      let motive ← withLocalDeclD `z Pb fun z ↦ mkLambdaFVars #[z] (abstractPair G H a b z)
      let eq := mkApp3 (mkConst ``proof_irrel) Pb b a
      let propEq := mkAppN (mkConst ``congrArg [.zero, .succ .zero])
        #[Pb, .sort .zero, b, a, motive, eq]
      let G' := motive.beta #[a]
      let next ← mkFreshExprSyntheticOpaqueMVar G'
      g.assign (mkAppN (mkConst ``Eq.mpr [.zero]) #[G, G', propEq, next])
      g := next.mvarId!
      G := G'
  g.assign h
  replaceMainGoal []

/-- `cast_proofs h` closes the goal with `h` when the type of `h` and the goal differ only by
closed proofs, at any number of positions, and by closed definitionally equal terms. Unlike
`exact_mod_proofs`, the goal is cast along one pair of differing proofs at a time, which keeps
the motives small for the kernel. -/
elab "cast_proofs " h:term : tactic => withMainContext do
  castProofs (← elabTerm h none)

end ExactModProofs

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenBridgeWord

/-! A factor identity used in proper/open transport. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem component_word
    {A B C D H : Type*} [Category A] [Category B] [Category C] [Category D] [Category H]
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ H) (Q : H ⥤ D)
    (S T : A ⥤ H) (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ≅ T)
    (p : T ⋙ Q ≅ F) (e : F ≅ G) (M : A) :
    (Functor.associator K P I ≪≫ Functor.isoWhiskerLeft K c ≪≫
      (Functor.associator K J Q).symm ≪≫ Functor.isoWhiskerRight r Q ≪≫
      Functor.isoWhiskerRight d Q ≪≫ p ≪≫ e).hom.app M =
      c.hom.app (K.obj M) ≫ Q.map (r.hom.app M) ≫ Q.map (d.hom.app M) ≫
        p.hom.app M ≫ e.hom.app M := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
    Category.id_comp]

private theorem component_word_map
    {A B C D H : Type*} [Category A] [Category B] [Category C] [Category D] [Category H]
    (K : A ⥤ B) (P : B ⥤ C) (I : C ⥤ D) (J : B ⥤ H) (Q : H ⥤ D)
    (S T : A ⥤ H) (F G : A ⥤ D)
    (c : P ⋙ I ≅ J ⋙ Q) (r : K ⋙ J ≅ S) (d : S ⟶ T) (hd : IsIso d)
    (p : T ⋙ Q ≅ F) (e : F ≅ G) (M : A) :
    (Functor.associator K P I ≪≫ Functor.isoWhiskerLeft K c ≪≫
      (Functor.associator K J Q).symm ≪≫ Functor.isoWhiskerRight r Q ≪≫
      Functor.isoWhiskerRight (@asIso _ _ _ _ d hd) Q ≪≫ p ≪≫ e).hom.app M =
      c.hom.app (K.obj M) ≫ Q.map (r.hom.app M) ≫ Q.map (d.app M) ≫
        p.hom.app M ≫ e.hom.app M := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
    Category.id_comp, asIso_hom]

private meta partial def wordCongruence (x y : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let x := x.consumeMData
  let y := y.consumeMData
  if x == y then return ← Lean.Meta.mkHEqRefl x
  if (← Lean.Meta.isProof x) && (← Lean.Meta.isProof y) then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[x, y]
  if x.getAppFn == y.getAppFn && x.isApp && x.getAppNumArgs == y.getAppNumArgs then
    let xs := x.getAppArgs
    let ys := y.getAppArgs
    let thm ← Lean.Meta.mkHCongrWithArity x.getAppFn xs.size
    let mut args := #[]
    for a in xs, b in ys, kind in thm.argKinds do
      let h ← wordCongruence a b
      match kind with
      | .eq => args := args ++ #[a, b, ← Lean.Meta.mkEqOfHEq h]
      | .heq => args := args ++ #[a, b, h]
      | _ => throwError "Unexpected congruence argument"
    let h := Lean.mkAppN thm.proof args
    if (← Lean.Meta.inferType h).isHEq then return h
    return ← Lean.Meta.mkHEqOfEq h
  return ← Lean.Meta.mkHEqRefl x

private theorem intrinsic_word
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : ProEtale.SemilinearProperOpen.Derived C τ U) :
    (ProEtale.SemilinearProperOpen.lambda C τ k r p i h).hom.app M =
      (ProEtale.SemilinearProperOpen.cartesianConjugate C τ p i).hom.app
        ((ProEtale.SemilinearProperOpen.J C τ k).obj M) ≫
      (ProEtale.SemilinearProperOpen.R C τ (pullback.snd p i)).map
        ((ProEtale.SemilinearProperOpen.restrictFactor C τ k r p i h).hom.app M) ≫
      (ProEtale.SemilinearProperOpen.R C τ (pullback.snd p i)).map
        ((ProEtale.SemilinearProperOpen.openToS C τ
          (ProEtale.StrictTower.squareLift k r p i h)).app M) ≫
      (ProEtale.SemilinearProperOpen.sComp C τ
        (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i)).hom.app M ≫
      (eqToIso (congrArg (ProEtale.SemilinearProperOpen.R C τ)
        (pullback.lift_snd k r h))).hom.app M := by
  delta ProEtale.SemilinearProperOpen.lambda
  have test := (component_word_map
    (ProEtale.SemilinearProperOpen.J C τ k) (ProEtale.SemilinearProperOpen.R C τ p)
    (ProEtale.SemilinearProperOpen.P C τ i)
    (ProEtale.SemilinearProperOpen.P C τ (pullback.fst p i))
    (ProEtale.SemilinearProperOpen.R C τ (pullback.snd p i))
    (ProEtale.SemilinearProperOpen.J C τ (ProEtale.StrictTower.squareLift k r p i h))
    (ProEtale.SemilinearProperOpen.R C τ (ProEtale.StrictTower.squareLift k r p i h))
    (ProEtale.SemilinearProperOpen.R C τ
      (ProEtale.StrictTower.squareLift k r p i h ≫ pullback.snd p i))
    (ProEtale.SemilinearProperOpen.R C τ r)
    (ProEtale.SemilinearProperOpen.cartesianConjugate C τ p i)
    (ProEtale.SemilinearProperOpen.restrictFactor C τ k r p i h)
    (ProEtale.SemilinearProperOpen.openToS C τ (ProEtale.StrictTower.squareLift k r p i h))
    (ProEtale.SemilinearProperOpen.openToS_isIso C τ
      (ProEtale.StrictTower.squareLift k r p i h))
    (ProEtale.SemilinearProperOpen.sComp C τ
      (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i))
    (eqToIso (congrArg (ProEtale.SemilinearProperOpen.R C τ)
      (pullback.lift_snd k r h))) M)
  run_tac Lean.Elab.Tactic.withMainContext do
    let x ← Lean.instantiateMVars (← Lean.Meta.inferType
      (← Lean.Elab.Term.elabTerm (Lean.mkIdent `test) none))
    let y ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let e ← Lean.Meta.mkEqOfHEq (← wordCongruence x y)
    let t ← Lean.Elab.Term.elabTerm (Lean.mkIdent `test) none
    let result ← Lean.Meta.mkAppM ``Eq.mp #[e, t]
    Lean.Elab.Tactic.closeMainGoal `exact result

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  Functor.leftAdjoint ProEtale.SemilinearProperOpen.R ProEtale.SemilinearProperOpen.J
  ProEtale.SemilinearProperOpen.P cartesianConjugate restrictFactor
  ProEtale.SemilinearProperOpen.cartesianConjugate ProEtale.SemilinearProperOpen.restrictFactor
  ProEtale.SemilinearProperOpen.openToS ProEtale.SemilinearProperOpen.sComp
  Compositors.pushComp
attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheaf integralCoefficientSheafTransition
  WeilConjectures.SemilinearSections.systemRing
  WeilConjectures.SemilinearSections.ringPresheaf WeilConjectures.SemilinearSections.rings
  sheafCompose ProEtale.SemilinearProperOpen.derived RingHom.ulift
  SemilinearSections.moduleAbelian SemilinearSections.hasDerived coefficientSequenceHasDerived
  CommRingCat.hasForgetToRingCat

-- The two presentations have the same concrete objects and morphisms.
-- Use its functor laws to transport compositions before evaluating their factors.
def nativeToSystem (W : Scheme.{u}) :
    ProEtale.SemilinearProperOpen.Derived (scalarRings l E) (scalarTransitions l E) W ⥤
      System l E W where
  obj M := M
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

-- State the unfolding for a free equality, so that its proof is never reduced.
/-- The integral-system equality transport is the image of the native one.
Source: blueprint def-sf-integral-system-native-bridge-data. -/
theorem nativeREq_eq_native {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (M : System l E X) :
    nativeREq l E h M = (nativeToSystem l E Y).map
      ((eqToIso (congrArg (ProEtale.SemilinearProperOpen.R
        (scalarRings l E) (scalarTransitions l E)) h)).hom.app M) := by
  cases h
  unfold nativeREq
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  rfl

-- Retain evaluation equations explicitly: reducing their right sides by
-- conversion can unfold the derived-image functors before the other side.
-- Preserve the type written in the equality instead of inferring it again
-- from an endpoint whose native derived-category presentation differs.
private meta def bridgeOfEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  unless ty.isEq do throwError "expected equality"
  return Lean.mkAppN (Lean.mkConst ``heq_of_eq ty.getAppFn.constLevels!)
    (ty.getAppArgs.push h)

private meta def bridgeSymm (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, β, b) := ty.heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``HEq.symm ty.getAppFn.constLevels!) #[α, β, a, b, h]

private meta def bridgeTrans (h k : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, β, b) := ty.heq? | throwError "expected HEq"
  let some (_, _, γ, c) := (← Lean.Meta.inferType k).heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``HEq.trans ty.getAppFn.constLevels!)
    #[α, β, γ, a, b, c, h, k]

private meta def bridgeToEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, _, b) := ty.heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq ty.getAppFn.constLevels!) #[α, a, b, h]

private meta def checkedReduction (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let α ← Lean.Meta.inferType a
  let level ← Lean.Meta.getLevel α
  let type := Lean.mkApp3 (Lean.mkConst ``Eq [level]) α a b
  let value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [level]) α a
  let h ← Lean.Meta.mkAuxTheorem type value
    (zetaDelta := true) (kind? := `_wordReduction)
  bridgeOfEq h

private meta def bridgeReduction (F e : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let reduced (e' : Lean.Expr) : Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
    return some (e', ← checkedReduction e e')
  let field (index : Nat) (value : Lean.Expr) := do
    -- The native arrow fields are x, y, z, w, n, and g.
    -- Build the image under F explicitly: some fields are typed through the
    -- integral-system aliases, so their type is not unified with the native one.
    let value ← if #[24, 25, 26, 27, 28, 30].contains index then do
      let fty ← Lean.instantiateMVars (← Lean.Meta.inferType F)
      let vty ← Lean.instantiateMVars (← Lean.Meta.inferType value)
      unless fty.isAppOfArity ``CategoryTheory.Functor 4 &&
          vty.isAppOfArity ``Quiver.Hom 4 do
        throwError "unexpected bridge field type {vty}"
      let fa := fty.getAppArgs
      let va := vty.getAppArgs
      pure (Lean.mkAppN (Lean.mkConst ``CategoryTheory.Functor.map fty.getAppFn.constLevels!)
        #[fa[0]!, fa[1]!, fa[2]!, fa[3]!, F, va[2]!, va[3]!, value])
      else pure value
    reduced value
  -- The equality transport is compared through its free-equality equation,
  -- so the kernel never reduces the transported equality.
  let transport (v : Lean.Expr) : Lean.MetaM Lean.Expr := do
    let h := Lean.mkAppN (Lean.mkConst ``nativeREq_eq_native v.getAppFn.constLevels!)
      v.getAppArgs
    let rhs := (← Lean.Meta.inferType h).getAppArgs.back!
    return Lean.mkAppN rhs.getAppFn (rhs.getAppArgs.set! 4 F)
  if e.isAppOf ``nativeREq then
    let h := Lean.mkAppN (Lean.mkConst ``nativeREq_eq_native e.getAppFn.constLevels!)
      e.getAppArgs
    return some (← transport e, ← bridgeOfEq h)
  if e.isAppOf ``CategoryTheory.Functor.map && e.getAppNumArgs == 8 then
    let v := e.appArg!
    if e.getAppArgs[4]! == F && v.isAppOf ``nativeREq then
      let h := Lean.mkAppN (Lean.mkConst ``nativeREq_eq_native v.getAppFn.constLevels!)
        v.getAppArgs
      return some (← transport v, ← bridgeTrans (← checkedReduction e v) (← bridgeOfEq h))
  if let .letE _ _ v body _ := e then return ← reduced (body.instantiate1 v)
  if e.headBeta != e then return ← reduced e.headBeta
  if let some e' ← e.reduceProjStruct? then return ← reduced e'
  if let .proj typeName index major := e then
    if typeName == ``BridgeWord then
      let major ← if major.isAppOf ``properOpenBridgeWord then
        Lean.Meta.unfoldDefinition? major (ignoreTransparency := true) else pure (some major)
      if let some major := major then
        if major.isAppOf ``BridgeWord.mk then return ← field index major.getAppArgs[index + 2]!
  if e.getAppFn.isConst then
    if let some info ← Lean.getProjectionFnInfo? e.getAppFn.constName! then
      let es := e.getAppArgs
      if es.size == info.numParams + 1 then
        let major := es.back!
        if major.isAppOf ``properOpenBridgeWord then
          if let some major ← Lean.Meta.unfoldDefinition? major (ignoreTransparency := true) then
            return ← field info.i major.getAppArgs[info.numParams + info.i]!
  if e.isAppOf ``Functor.obj then
    let es := e.getAppArgs
    let G := es[es.size - 2]!
    if G == F then return ← reduced es.back!
    if G.isAppOf ``Functor.comp then
      let h ← Lean.Meta.mkAppOptM ``Functor.comp_obj
        ((G.getAppArgs.map some) ++ #[some es.back!])
      return some ((← Lean.Meta.inferType h).getAppArgs.back!, ← bridgeOfEq h)
  return none

private meta partial def bridgeCongruence (F : Lean.Expr)
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (congrCache : IO.Ref (Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem))
    (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← Lean.Meta.mkHEqRefl a
  if let some h := (← cache.get).get? (a, b) then return h
  let compute : Lean.MetaM Lean.Expr := do
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
    if let some (a', ha) ← bridgeReduction F a then
      return ← bridgeTrans ha (← bridgeCongruence F cache congrCache a' b)
    if let some (b', hb) ← bridgeReduction F b then
      return ← bridgeTrans (← bridgeCongruence F cache congrCache a b') (← bridgeSymm hb)
    if a.getAppFn == b.getAppFn && a.isApp && a.getAppNumArgs == b.getAppNumArgs then
      let aa := a.getAppArgs
      let bb := b.getAppArgs
      -- Keep category parameters generic while constructing congruence.
      -- Check each generic congruence once, before specializing its categories.
      let key := (a.getAppFn, aa.size)
      let ct ← match (← congrCache.get).get? key with
        | some ct => pure ct
        | none => do
          let ct ← Lean.Meta.withLCtx {} {} <|
            Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
          let proof ← Lean.Meta.mkAuxTheorem ct.type ct.proof (kind? := `_wordCongruence)
          let ct := { ct with proof := proof }
          congrCache.modify fun m => m.insert key ct
          pure ct
      let mut args := #[]
      for i in [:aa.size] do
        let h ← bridgeCongruence F cache congrCache aa[i]! bb[i]!
        let h ← if ct.argKinds[i]! == .eq then bridgeToEq h else pure h
        args := args ++ #[aa[i]!, bb[i]!, h]
      let h := Lean.mkAppN ct.proof args
      return ← if (← Lean.Meta.inferType h).isHEq then pure h else bridgeOfEq h
    if (← Lean.Meta.inferType a).getAppFn.isConstOf ``Quiver then
      let value ← if b.containsConst (· == ``catToReflQuiver) then
        Lean.Meta.mkHEqRefl b else Lean.Meta.mkHEqRefl a
      return ← Lean.Meta.mkAuxTheorem (← Lean.Meta.mkHEq a b) value
        (zetaDelta := true) (kind? := `_quiverProjection)
    let nativeAlias (e : Lean.Expr) : Bool :=
      e.isAppOf ``ProEtale.SemilinearProperOpen.Derived ||
        e.isAppOf ``ProEtale.SemilinearProperOpen.Modules ||
        e.isAppOf ``ProEtale.SemilinearProperOpen.derived ||
        e.isAppOf ``SemilinearSections.ring || e.isAppOf ``SemilinearSections.systemRing ||
        e.isAppOf ``SemilinearSections.moduleAbelian || e.isAppOf ``SemilinearSections.hasDerived
    if a.isAppOf ``ProEtale.StrictTower.squareLift then
      return ← checkedReduction a b
    if b.isAppOf ``ProEtale.StrictTower.squareLift then
      return ← bridgeSymm (← checkedReduction b a)
    if nativeAlias a then return ← checkedReduction a b
    if nativeAlias b then
      return ← bridgeSymm (← checkedReduction b a)
    -- The integral-system aliases and their category instances agree with the
    -- native data by definition.
    let integralAlias (e : Lean.Expr) : Bool :=
      [``nativeR, ``nativeJ, ``nativeOpen, ``nativeComp, ``nativeREq].any e.isAppOf
    if integralAlias a || (← Lean.Meta.isClass? (← Lean.Meta.inferType a)).isSome then
      return ← checkedReduction a b
    if integralAlias b then return ← bridgeSymm (← checkedReduction b a)
    throwError "Different bridge expressions: {a} versus {b}"
  let h ← compute
  let ty ← Lean.Meta.mkHEq a b
  let h ← if (← Lean.Meta.inferType h) == ty then pure h else
    Lean.Meta.mkAuxTheorem ty h (zetaDelta := true) (kind? := `_bridgeCongruence)
  cache.modify fun m => m.insert (a, b) h
  return h

/-- The chosen and intrinsic lambda components expand into their factors.
Source: Stacks 0F7B and blueprint fix-prop-coherence.

Proof: Unfold the two lambda definitions. Components of an isomorphism composite are
the composites of its components. Whiskering on the left is evaluation, and
whiskering on the right maps the component through the direct functor.
Associator components are identities. Removing them gives each displayed
five-factor word. Finally unfold the actual diagram fields. This calculation
uses no canonical-bridge compatibility square.
(blueprint: lem-sf-integral-system-lambda-word-expansions). -/
theorem lambdaWord_expansions (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : System l E U) :
    let d := properOpenBridgeWord l E o c a b k r p i h M
    (d.f = d.a ≫ d.b ≫ d.c ≫ d.d ≫ d.e) ∧
      (d.g = d.x ≫ d.y ≫ d.z ≫ d.w ≫ d.n) := by
  constructor
  · delta properOpenBridgeWord properOpenLambda
    with_reducible exact (component_word
      (Operations.shriek l E o k) (Operations.push l E o p) (pull l E i)
      (pull l E (pullback.fst p i)) (Operations.push l E o (pullback.snd p i))
      (Operations.shriek l E o (ProEtale.StrictTower.squareLift k r p i h))
      (Operations.push l E o (ProEtale.StrictTower.squareLift k r p i h))
      (Operations.push l E o
        (ProEtale.StrictTower.squareLift k r p i h ≫ pullback.snd p i))
      (Operations.push l E o r)
      (cartesianConjugate l E o c a p i) (restrictFactor l E o c a k r p i h)
      (a.clopen (ProEtale.StrictTower.squareLift k r p i h))
      (c.pushComp l E (ProEtale.StrictTower.squareLift k r p i h) (pullback.snd p i))
      (eqToIso (congrArg (Operations.push l E o) (pullback.lift_snd k r h))) M)
  · have hn := intrinsic_word (scalarRings l E) (scalarTransitions l E) k r p i h M
    let F := nativeToSystem l E W
    have hs := congrArg (fun f => F.map f) hn
    simp only [Functor.map_comp] at hs
    run_tac Lean.Elab.Tactic.withMainContext do
      let F ← Lean.Elab.Term.elabTerm (Lean.mkIdent `F) none
      let hs ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hs) none
      let x ← Lean.instantiateMVars (← Lean.Meta.inferType hs)
      let y ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
      let congrCache ← IO.mkRef
        ({} : Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem)
      let h ← bridgeToEq (← bridgeCongruence F cache congrCache x y)
      let result ← Lean.Meta.mkAppM ``Eq.mp #[h, hs]
      Lean.Elab.Tactic.closeMainGoal `exact result

end WeilConjectures.IntegralSystemRealization

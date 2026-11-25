/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralCompactSupportDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing

/-! # Total-derived normalization of a single boundary refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport
set_option synthInstance.maxSize 2048

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory
attribute [local instance 2000] CategoryTheory.scalarTensor4 CategoryTheory.scalarTensor12
  CategoryTheory.scalarTensor23 CategoryTheory.scalarTensorColimits
  CategoryTheory.scalarFlipTensorColimits CategoryTheory.Mod.hasFunctorialFlatResolution
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
attribute [local irreducible] HasDerivedCategory.standard

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar openImmersionLowerShriek
  derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  localizing localizingClosureProEtale CategoryTheory.localizingClosure
  compactificationRefinementComponent localizingRefinementMap
  pushComp refinementDerivedLowerStarComp
  Adjunction.ofNatIsoRight upperStarComp

section Coefficients

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable (k : Type u) [Field k]

private theorem conjugate_left_transport
    {C D : Type*} [Category C] [Category D]
    {L L' M M' : C ⥤ D} {R S : D ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (e : L ≅ L') (f : M ≅ M') (t : M' ⟶ L') :
    conjugateEquiv (a.ofNatIsoLeft e) (b.ofNatIsoLeft f) t =
      conjugateEquiv a b (f.hom ≫ t ≫ e.inv) := by
  apply NatTrans.ext
  funext K
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]

private theorem comp_left_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L L' : C ⥤ D} {M M' : D ⥤ E} {R : D ⥤ C} {S : E ⥤ D}
    (a : L ⊣ R) (b : M ⊣ S) (e : L ≅ L') (f : M ≅ M') :
    (a.ofNatIsoLeft e).comp (b.ofNatIsoLeft f) =
      (a.comp b).ofNatIsoLeft
        (Functor.isoWhiskerLeft L f ≪≫ Functor.isoWhiskerRight e M') := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext K
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  have h : e.hom.app K ≫ b.unit.app (L'.obj K) ≫
      S.map (f.hom.app (L'.obj K)) =
      b.unit.app (L.obj K) ≫ S.map (f.hom.app (L.obj K)) ≫
        S.map (M'.map (e.hom.app K)) := by
    calc
      _ = b.unit.app (L.obj K) ≫ S.map (M.map (e.hom.app K)) ≫
          S.map (f.hom.app (L'.obj K)) := by
        simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
          congrArg (fun z ↦ z ≫ S.map (f.hom.app (L'.obj K)))
            (b.unit.naturality (e.hom.app K))
      _ = _ := by rw [← S.map_comp, f.hom.naturality, S.map_comp]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ a.unit.app K ≫ R.map z) h

private theorem transport_restriction
    {A B C : Type*} [Category A] [Category B] [Category C]
    {P P' : A ⥤ C} {R R' : A ⥤ B} {S S' : B ⥤ C}
    (e : P ≅ P') (f : R ≅ R') (g : S ≅ S')
    (t : P ≅ R ⋙ S) (q : P' ≅ R' ⋙ S')
    (ht : t = e ≪≫ q ≪≫ Functor.isoWhiskerRight f.symm S' ≪≫
      Functor.isoWhiskerLeft R g.symm)
    {K : A} {N : B} (v : R.obj K ⟶ N) :
    e.inv.app K ≫ t.hom.app K ≫ S.map v =
      q.hom.app K ≫ S'.map (f.inv.app K ≫ v) ≫ g.inv.app N := by
  rw [ht]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← g.inv.naturality]
  simp only [Functor.map_comp, Category.assoc]

private theorem normalized_transport
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Jd : C ⥤ A} {Jc : C ⥤ B} {Pd Pd₀ : A ⥤ C} {Pc Pc₀ : B ⥤ C}
    (a : Jd ⊣ Pd) (b : Jc ⊣ Pc) (e : Pd₀ ≅ Pd) (g : Pc₀ ≅ Pc)
    {R : B ⥤ A} (K : C) (m : Jd.obj K ⟶ R.obj (Jc.obj K))
    (r : Pd.obj (R.obj (Jc.obj K)) ⟶ Pc.obj (Jc.obj K))
    (r₀ : Pd₀.obj (R.obj (Jc.obj K)) ⟶ Pc₀.obj (Jc.obj K))
    (ht : e.inv.app _ ≫ r₀ = r ≫ g.inv.app _)
    (hn : a.unit.app K ≫ Pd.map m ≫ r = b.unit.app K) :
    (a.ofNatIsoRight e.symm).homEquiv _ _ m ≫ r₀ =
      (b.ofNatIsoRight g.symm).unit.app K := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  simp only [Iso.symm_hom, Category.assoc]
  rw [ht, Adjunction.homEquiv_unit]
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc] using
    congrArg (fun z ↦ z ≫ g.inv.app (Jc.obj K)) hn

private theorem iso_composition_transport
    {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : C}
    (a : A₀ ≅ A₁) (b : A₁ ≅ A₂) (c : A₃ ≅ A₂)
    (d : A₂ ≅ A₄) (e : A₄ ≅ A₅) (f : A₅ ≅ A₆) :
    (a ≪≫ b ≪≫ c.symm) ≪≫ (c ≪≫ d ≪≫ e ≪≫ f) =
      a ≪≫ (b ≪≫ d) ≪≫ e ≪≫ f := by
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

private theorem conjugate_compositor_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L L' : C ⥤ D} {M M' : D ⥤ E} {N N' : C ⥤ E}
    {R : D ⥤ C} {S : E ⥤ D} {T : E ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T)
    (e : L ≅ L') (f : M ≅ M') (g : N ≅ N')
    (t : N ≅ L ⋙ M) (q : N' ≅ L' ⋙ M')
    (ht : t = g ≪≫ q ≪≫ Functor.isoWhiskerRight e.symm M' ≪≫
      Functor.isoWhiskerLeft L f.symm)
    (a' : L' ⊣ R) (b' : M' ⊣ S) (c' : N' ⊣ T)
    (ha : a.ofNatIsoLeft e = a') (hb : b.ofNatIsoLeft f = b')
    (hc : c.ofNatIsoLeft g = c') :
    conjugateEquiv (a.comp b) c t.hom = conjugateEquiv (a'.comp b') c' q.hom := by
  rw [← ha, ← hb, ← hc, comp_left_transport, conjugate_left_transport, ht]
  congr 1

private theorem isIso_of_comparison_comp
    {C : Type*} [Category C] {A B D E : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ E) (e : E ≅ D)
    [IsIso g] [IsIso h] (hc : h ≫ e.hom = f ≫ g) : IsIso f := by
  have : IsIso (f ≫ g) := hc ▸ (inferInstance : IsIso (h ≫ e.hom))
  exact IsIso.of_isIso_comp_right f g

private theorem inverse_comparison_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) (G : C ⥤ D) (H I : C ⥤ E)
    (κ : G ⋙ F ≅ H) (κ' : H ≅ G ⋙ F) (τ : H ≅ I) (δ : H ⟶ I)
    {M : C} {N : D} (e : N ≅ G.obj M)
    (hκ : κ.hom = κ'.inv) (hτ : τ.hom = δ) :
    (((κ ≪≫ τ).symm.app M) ≪≫ F.mapIso e.symm).inv =
      F.map e.hom ≫ κ'.inv.app M ≫ δ.app M := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv,
    Iso.trans_hom, NatTrans.comp_app, hκ, hτ]

-- Build conversion proofs before evaluating derived functors on objects.
-- Every auxiliary equality and every congruence theorem is checked by the kernel.

private meta def conversionOfEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  unless ty.isEq do throwError "expected equality"
  return Lean.mkAppN (Lean.mkConst ``heq_of_eq ty.getAppFn.constLevels!)
    (ty.getAppArgs.push h)

private meta def conversionToEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, _, b) := ty.heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq ty.getAppFn.constLevels!) #[α, a, b, h]

private meta def conversionSymm (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, β, b) := ty.heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``HEq.symm ty.getAppFn.constLevels!) #[α, β, a, b, h]

private meta def conversionTrans (h k : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ty ← Lean.Meta.inferType h
  let some (α, a, β, b) := ty.heq? | throwError "expected HEq"
  let some (_, _, γ, c) := (← Lean.Meta.inferType k).heq? | throwError "expected HEq"
  return Lean.mkAppN (Lean.mkConst ``HEq.trans ty.getAppFn.constLevels!)
    #[α, β, γ, a, b, c, h, k]

private meta def smallConversion (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let α ← Lean.Meta.inferType a
  let level ← Lean.Meta.getLevel α
  let ty := Lean.mkApp3 (Lean.mkConst ``Eq [level]) α a b
  let value := Lean.mkApp2 (Lean.mkConst ``Eq.refl [level]) α a
  let h ← Lean.Meta.mkAuxTheorem ty value
    (zetaDelta := true) (kind? := `_instanceConversion)
  conversionOfEq h

private meta def representationReduction (e : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let reduced (e' : Lean.Expr) := do
    return some (e', ← smallConversion e e')
  if let .letE _ _ v body _ := e then return ← reduced (body.instantiate1 v)
  if e.headBeta != e then return ← reduced e.headBeta
  if let some e' ← e.reduceProjStruct? then return ← reduced e'
  if e.isAppOf ``Functor.obj then
    let es := e.getAppArgs
    let F := es[es.size - 2]!
    let rule? := if F.isAppOf ``Functor.comp then some ``Functor.comp_obj else
      if F.isAppOf ``Functor.id then some ``Functor.id_obj else none
    if let some rule := rule? then
      let h ← Lean.Meta.mkAppOptM rule ((F.getAppArgs.map some) ++ #[some es.back!])
      return some ((← Lean.Meta.inferType h).getAppArgs.back!, ← conversionOfEq h)
  if e.isAppOf ``Functor.map then
    let es := e.getAppArgs
    let F := es[4]!
    let rule? := if F.isAppOf ``Functor.comp then some ``Functor.comp_map else
      if F.isAppOf ``Functor.id then some ``Functor.id_map else none
    if let some rule := rule? then
      let h ← Lean.Meta.mkAppOptM rule
        ((F.getAppArgs.map some) ++ (es.extract 5 es.size).map some)
      return some ((← Lean.Meta.inferType h).getAppArgs.back!, ← conversionOfEq h)
  return none

private meta def instanceConversion
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (congrCache : IO.Ref (Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem)) :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, _, _ => throwError "conversion depth exhausted"
  | fuel + 1, a, b => do
    let a := a.consumeMData
    let b := b.consumeMData
    if a == b then return ← Lean.Meta.mkHEqRefl a
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let some (a', h) ← representationReduction a then
        return ← conversionTrans h (← instanceConversion cache congrCache fuel a' b)
      if let some (b', h) ← representationReduction b then
        return ← conversionTrans (← instanceConversion cache congrCache fuel a b')
          (← conversionSymm h)
      let isAlias (e : Lean.Expr) :=
        [``AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.Ambient,
         ``AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.pull,
         ``AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.push,
         ``AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.extend,
         ``AlgebraicGeometry.ProEtale.moduleDerivedPullback,
         ``AlgebraicGeometry.ProEtale.moduleDerivedPushforward].any e.isAppOf
      if isAlias a then
        if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
          return ← conversionTrans (← smallConversion a a')
            (← instanceConversion cache congrCache fuel a' b)
      if isAlias b then
        if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
          return ← conversionTrans (← instanceConversion cache congrCache fuel a b')
            (← conversionSymm (← smallConversion b b'))
      let sameHead := a.getAppFn == b.getAppFn ||
        (a.getAppFn.isConst && b.getAppFn.isConst &&
          a.getAppFn.constName! == b.getAppFn.constName!)
      if sameHead && a.isApp && a.getAppNumArgs == b.getAppNumArgs then
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let key := (a.getAppFn, aa.size)
        let ct ← match (← congrCache.get).get? key with
          | some ct => pure ct
          | none => do
            let ct ← Lean.Meta.withLCtx {} {} <|
              Lean.Meta.mkHCongrWithArity a.getAppFn aa.size
            let proof ← Lean.Meta.mkAuxTheorem ct.type ct.proof
              (kind? := `_genericInstanceCongruence)
            let ct := { ct with proof := proof }
            congrCache.modify fun m => m.insert key ct
            pure ct
        let mut args := #[]
        for i in [:aa.size] do
          let h ← try instanceConversion cache congrCache fuel aa[i]! bb[i]!
            catch ex => throwError "argument {i} of {a.getAppFn}: {ex.toMessageData}"
          let h ← if ct.argKinds[i]! == .eq then conversionToEq h else pure h
          args := args ++ #[aa[i]!, bb[i]!, h]
        let h := Lean.mkAppN ct.proof args
        return ← if (← Lean.Meta.inferType h).isHEq then pure h else conversionOfEq h
      if (← Lean.Meta.isClass? (← Lean.Meta.inferType a)).isSome ||
          (← Lean.Meta.isClass? (← Lean.Meta.inferType b)).isSome then
        return ← smallConversion a b
      if a.getAppFn.isConst && b.getAppFn.isConst &&
          a.getAppFn.constName! == b.getAppFn.constName! then
        return ← smallConversion a b
      -- The remaining leaves are definitionally equal functions or universe instances.
      return ← smallConversion a b
    let h ← compute
    let ty ← Lean.Meta.mkHEq a b
    let h ← if (← Lean.Meta.inferType h) == ty then pure h else
      Lean.Meta.mkAuxTheorem ty h (zetaDelta := true) (kind? := `_instanceCongruence)
    cache.modify fun m => m.insert (a, b) h
    return h

private theorem total_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    leftDerivedUpperStarComp Λ a b =
      leftDerivedUpperStarIsoMapDerivedCategory Λ (a ≫ b) ≪≫
        Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ a b) ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ b).symm
          (upperStar Λ a).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (pull Λ b)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ a).symm := by
  unfold leftDerivedUpperStarComp Functor.leftDerivedFunctorNatIso
    Functor.leftDerivedFunctorCompIso leftDerivedUpperStarIsoMapDerivedCategory
  exact iso_composition_transport _ _ _ _ _ _

private theorem total_push_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (pushComp Λ a b).hom = (refinementDerivedLowerStarComp Λ a b).inv := by
  have h := conjugate_compositor_transport
    (derivedUpperStarLowerStarAdjunction Λ b)
    (derivedUpperStarLowerStarAdjunction Λ a)
    (derivedUpperStarLowerStarAdjunction Λ (a ≫ b))
    (leftDerivedUpperStarIsoMapDerivedCategory Λ b)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ a)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ (a ≫ b))
    (leftDerivedUpperStarComp Λ a b)
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ a b)) (total_comp Λ a b)
    (upperStarLowerStarAdjunction Λ b).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ a).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ (a ≫ b)).mapDerivedCategoryRightDerivedAdjunction
    (refinementAdjunction_eq Λ b) (refinementAdjunction_eq Λ a)
    (refinementAdjunction_eq Λ (a ≫ b))
  unfold pushComp
  exact h.trans (refinementComp_conjugate Λ a b).symm

private theorem total_triangle {X Y Z : Scheme.{u}} (j : X ⟶ Z) (i : X ⟶ Y)
    (r : Y ⟶ Z) (h : i ≫ r = j) :
    (eqToIso (congrArg (fun g : X ⟶ Z ↦ pull Λ g) h.symm) ≪≫
      leftDerivedUpperStarComp Λ i r) =
      leftDerivedUpperStarIsoMapDerivedCategory Λ j ≪≫
        (Functor.mapDerivedCategoryNatIso
          (eqToIso (congrArg (upperStar Λ) h.symm) ≪≫ upperStarComp Λ i r) ≪≫
          (Functor.mapDerivedCategoryCompIso (upperStar Λ r) (upperStar Λ i)).symm) ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ r).symm
          (upperStar Λ i).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (pull Λ r)
          (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm := by
  subst j
  simpa only [eqToIso_refl, Iso.refl_trans, Functor.mapDerivedCategoryTriangleIso] using
    total_comp Λ i r

private theorem total_triangle_restriction {W A B : Scheme.{u}}
    (j : W ⟶ B) (i : W ⟶ A) (r : A ⟶ B) (h : i ≫ r = j)
    (K : Ambient Λ B) (M : Ambient Λ A) (v : (pull Λ r).obj K ⟶ M) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app K ≫
        (eqToIso (congrArg (fun g : W ⟶ B ↦ pull Λ g) h.symm) ≪≫
          leftDerivedUpperStarComp Λ i r).hom.app K ≫
        (pull Λ i).map v =
      (Functor.mapDerivedCategoryNatIso
          (eqToIso (congrArg (upperStar Λ) h.symm) ≪≫ upperStarComp Λ i r) ≪≫
        (Functor.mapDerivedCategoryCompIso (upperStar Λ r) (upperStar Λ i)).symm).hom.app
          K ≫
        (upperStar Λ i).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ r).inv.app K ≫
            v) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ i).inv.app M := by
  exact transport_restriction
    (A := Ambient Λ B) (B := Ambient Λ A) (C := Ambient Λ W)
    (P := pull Λ j) (P' := (upperStar Λ j).mapDerivedCategory)
    (R := pull Λ r) (R' := (upperStar Λ r).mapDerivedCategory)
    (S := pull Λ i) (S' := (upperStar Λ i).mapDerivedCategory)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ r)
    (leftDerivedUpperStarIsoMapDerivedCategory Λ i)
    (eqToIso (congrArg (fun g : W ⟶ B ↦ pull Λ g) h.symm) ≪≫
      leftDerivedUpperStarComp Λ i r)
    (Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ) h.symm) ≪≫ upperStarComp Λ i r) ≪≫
      (Functor.mapDerivedCategoryCompIso (upperStar Λ r) (upperStar Λ i)).symm)
    (total_triangle Λ j i r h)
    (K := K) (N := M) v

private theorem total_restriction_component {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (M : Ambient Λ c.Z) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ d.i).inv.app ((push Λ r.hom).obj M) ≫
        (eqToIso (congrArg (fun g : X ⟶ d.Z ↦ pull Λ g) r.i_hom.symm) ≪≫
          leftDerivedUpperStarComp Λ c.i r.hom).hom.app ((push Λ r.hom).obj M) ≫
        (pull Λ c.i).map ((derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app M) =
      (refinementOpenRestriction Λ r).app M ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ c.i).inv.app M := by
  simpa only [refinementOpenRestriction, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc] using
    total_triangle_restriction Λ d.i c.i r.hom r.i_hom
      ((push Λ r.hom).obj M) M
      ((derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app M)

private theorem total_restriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Ambient Λ X) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ d.i).inv.app _ ≫
        refinementRestriction Λ r K =
      (refinementOpenRestriction Λ r).app ((extend Λ c.i).obj K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ c.i).inv.app _ := by
  unfold refinementRestriction
  have test := total_restriction_component Λ r ((extend Λ c.i).obj K)
  run_tac Lean.Elab.Tactic.withMainContext do
    let test ← Lean.Elab.Term.elabTerm (Lean.mkIdent `test) none
    let x ← Lean.instantiateMVars (← Lean.Meta.inferType test)
    let y ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let congrCache ← IO.mkRef
      ({} : Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem)
    let h ← conversionToEq (← instanceConversion cache congrCache 512 x y)
    let result ← Lean.Meta.mkAppM ``Eq.mp #[h, test]
    Lean.Elab.Tactic.closeMainGoal `exact result

/-- The proper-open refinement map on Loc is invertible and its normalization transports
from the exact open adjunction to the total-derived open adjunction.

Source: blueprint proposition-construction-independence-rf-shriek--7, clauses (1)--(3), and
lem-sfb-total-derived-normalized-comparisons, inverse-component step.
(blueprint: lem-sfb-boundary-refinement-total-normalization).

Proof: use the supplied Loc(Dctf) membership of K (the caller obtains it from
Loc(Dbc) by the equality of localizing closures). Dominate the source compactification
by a common dense refinement with itself.
The localizing refinement maps for that refinement and its composite with r are
invertible by boundary vanishing; their composition law cancels the first to prove
invertibility of the map for r. Take e to be the isomorphism of that canonical map.
Transport localizingRefinementMap_normalized along the canonical isomorphism between
termwise and total pullback. Naturality cancels the transport factors, giving the
unit equation displayed here. Identify pushComp with the inverse recorded derived
pushforward compositor by conjugating the pullback compositor under the derived
adjunctions. Expand the inverse of refinementIso: its three factors are Rp_* of e,
the inverse compositor, and the pushforward equality transport, exactly the factors
of compactificationRefinementComponent. No density of c or d is used, and empty
opens and zero objects satisfy the same equations. -/
theorem integral_boundaryRefinement_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hadm : IsLocalizingAdmissibleCoefficient ℓ Λ)
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Spaces k} (f : X ⟶ Y) (c d : Compactifications k f)
    (r : c.obj.Refinement d.obj)
    (hb : r.hom ⁻¹ᵁ d.obj.i.opensRange = c.obj.i.opensRange)
    (K : (localizing Λ X.obj.left).FullSubcategory)
    (hK : localizingClosureProEtale Λ X.obj.left K.obj) :
    ∃ e : (extend Λ d.obj.i).obj K.obj ≅
        (push Λ r.hom).obj ((extend Λ c.obj.i).obj K.obj),
      (openAdjunction Λ d.obj.i).homEquiv _ _ e.hom ≫
          refinementRestriction Λ r K.obj = (openAdjunction Λ c.obj.i).unit.app K.obj ∧
      HEq (refinementIso Λ r K.obj e).inv
        (compactificationRefinementComponent Λ
          (⟨ObjectProperty.homMk r, hb⟩ :
            (⟨c⟩ : Compactification.BoundaryCompactification f.hom.left) ⟶ ⟨d⟩) K.obj) := by
  classical
  have : IsSeparated X.obj.hom := X.property.1
  have : LocallyOfFiniteType X.obj.hom := X.property.2.1
  have : QuasiCompact X.obj.hom := X.property.2.2
  have : IsSeparated Y.obj.hom := Y.property.1
  have : LocallyOfFiniteType Y.obj.hom := Y.property.2.1
  have : QuasiCompact Y.obj.hom := Y.property.2.2
  have : IsSeparated (X.obj.left ↘ Spec (.of k)) := X.property.1
  have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of k)) := X.property.2.1
  have : QuasiCompact (X.obj.left ↘ Spec (.of k)) := X.property.2.2
  have : IsSeparated (Y.obj.left ↘ Spec (.of k)) := Y.property.1
  have : LocallyOfFiniteType (Y.obj.left ↘ Spec (.of k)) := Y.property.2.1
  have : QuasiCompact (Y.obj.left ↘ Spec (.of k)) := Y.property.2.2
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  have : CompactSpace Y.obj.left := QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  have : QuasiSeparatedSpace X.obj.left := quasiSeparatedSpace_of_quasiSeparated X.obj.hom
  have : QuasiSeparatedSpace Y.obj.left := quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
  have hft : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
    rw [Over.w f.hom]
    infer_instance
  have hsep : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
    rw [Over.w f.hom]
    infer_instance
  have : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp _ Y.obj.hom
  have : IsSeparated f.hom.left := IsSeparated.of_comp _ Y.obj.hom
  have : QuasiCompact f.hom.left :=
    QuasiCompact.of_comp (f := f.hom.left) (g := Y.obj.hom)
  let r' : (⟨c⟩ : Compactification.BoundaryCompactification f.hom.left) ⟶ ⟨d⟩ :=
    ⟨ObjectProperty.homMk r, hb⟩
  have h := Compactification.exists_common_dense_refinement.{u, u} f.hom.left c.obj c.obj
  let w : Compactification.BoundaryCompactification f.hom.left :=
    ⟨⟨Compactification.inf c.obj c.obj, h.2.2.1⟩⟩
  let a : w ⟶ (⟨c⟩ : Compactification.BoundaryCompactification f.hom.left) :=
    ⟨ObjectProperty.homMk (Compactification.infFst c.obj c.obj),
      h.2.2.2.2.2.2.2.2.2.2.2.1⟩
  have ha : IsIso (localizingRefinementMap Λ a K.obj) :=
    refinementMap_isIso Λ ℓ hadm k (c := ⟨c⟩) (d := w) h.2.2.2.1 a K.obj hK
  have hra : IsIso (localizingRefinementMap Λ (a ≫ r') K.obj) :=
    refinementMap_isIso Λ ℓ hadm k (c := ⟨d⟩) (d := w) h.2.2.2.1 (a ≫ r') K.obj hK
  have hc := localizingRefinementMap_comp Λ r' a K.obj
  have hr : IsIso (localizingRefinementMap Λ r' K.obj) :=
    isIso_of_comparison_comp (localizingRefinementMap Λ r' K.obj)
      ((lowerStar Λ r.hom).rightDerivedFunctor.map (localizingRefinementMap Λ a K.obj))
      (localizingRefinementMap Λ (a ≫ r') K.obj)
      ((refinementDerivedLowerStarComp Λ a.hom.hom.hom r.hom).app
        ((extend Λ w.obj.obj.i).obj K.obj)) hc
  let e : (extend Λ d.obj.i).obj K.obj ≅
      (push Λ r.hom).obj ((extend Λ c.obj.i).obj K.obj) :=
    asIso (localizingRefinementMap Λ r' K.obj)
  refine ⟨e, ?_, ?_⟩
  · exact normalized_transport (Pd₀ := pull Λ d.obj.i) (Pc₀ := pull Λ c.obj.i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ d.obj.i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.i)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ d.obj.i)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.i)
      K.obj e.hom _ _ (total_restriction Λ r K.obj)
      (localizingRefinementMap_normalized Λ r' K.obj)
  · apply heq_of_eq
    unfold refinementIso compactificationRefinementComponent
    exact inverse_comparison_transport
      (C := Ambient Λ c.obj.Z) (D := Ambient Λ d.obj.Z) (E := Ambient Λ Y.obj.left)
      (M := (extend Λ c.obj.i).obj K.obj) (N := (extend Λ d.obj.i).obj K.obj)
      (push Λ d.obj.g) (push Λ r.hom) (push Λ (r.hom ≫ d.obj.g)) (push Λ c.obj.g)
      (pushComp Λ r.hom d.obj.g) (refinementDerivedLowerStarComp Λ r.hom d.obj.g)
      (eqToIso (congrArg (fun g : c.obj.Z ⟶ Y.obj.left ↦ push Λ g) r.hom_g))
      (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ r.hom_g)).hom e
      (total_push_comp Λ r.hom d.obj.g) (derive_eqToIso Λ r.hom_g).symm

end Coefficients
end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

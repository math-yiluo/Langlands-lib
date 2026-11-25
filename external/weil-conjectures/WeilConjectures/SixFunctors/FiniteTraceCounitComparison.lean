/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfDiagonalKernelIntegrals
public import WeilConjectures.SixFunctors.ProjectiveLineTraceModel
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence

/-! # Comparing proper kernel and inverse-projection counits

Proper projection coherence, tensor symmetry and the unitors identify the kernel
counit with the specified ordinary inverse-projection counit, component by component.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  SfDiagonalKernel.unit SfDiagonalKernel.counit

open MonoidalCategory in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordered_counit_comparison
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalCategory D] [BraidedCategory D]
    (F G : C ⥤ D) (c : F ≅ G) (B U : C) (K : D)
    (p : F.obj B ⊗ K ≅ F.obj (B ⊗ U))
    (p' : G.obj B ⊗ K ≅ G.obj (B ⊗ U))
    (s : G.obj B ⟶ 𝟙_ D)
    (hp : p.hom ≫ c.hom.app (B ⊗ U) = (c.hom.app B ▷ K) ≫ p'.hom) :
    F.map (β_ B U).inv ≫ p.inv ≫ ((c.hom.app B ≫ s) ▷ K) ≫ (λ_ K).hom =
      c.hom.app (U ⊗ B) ≫ ((G.map (β_ B U).inv ≫ p'.inv) ≫
        (β_ K (G.obj B)).inv) ≫ (K ◁ s) ≫ (ρ_ K).hom := by
  have hc : p.inv ≫ (c.hom.app B ▷ K) = c.hom.app (B ⊗ U) ≫ p'.inv := by
    apply (cancel_epi p.hom).1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc, hp]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc p.inv, hc]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map _), c.hom.naturality]
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_inv_naturality_left_assoc s K]
  simp only [braiding_inv_tensorUnit_right, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordered_counit_derived
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (X Y : Scheme.{u})
    (F G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) (c : F ≅ G)
    (B U : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (p : ((derivedTensor C Y).obj (F.obj B)).obj K ≅
      F.obj (((derivedTensor C X).obj B).obj U))
    (p' : ((derivedTensor C Y).obj (G.obj B)).obj K ≅
      G.obj (((derivedTensor C X).obj B).obj U))
    (s : G.obj B ⟶ derivedTensorUnit C Y)
    (hp : p.hom ≫ c.hom.app (((derivedTensor C X).obj B).obj U) =
      ((derivedTensor C Y).map (c.hom.app B)).app K ≫ p'.hom) :
    F.map (((derivedTensorSymmetry C X).inv.app B).app U) ≫ p.inv ≫
        ((derivedTensor C Y).map (c.hom.app B ≫ s)).app K ≫
        (derivedTensorLeftUnitor C Y K).hom =
      c.hom.app (((derivedTensor C X).obj U).obj B) ≫
        ((G.map (((derivedTensorSymmetry C X).inv.app B).app U) ≫ p'.inv) ≫
        (((derivedTensorSymmetry C Y).inv.app K).app (G.obj B))) ≫
        ((derivedTensor C Y).obj K).map s ≫ (derivedTensorRightUnitor C Y K).hom := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology C)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Y.smallEtaleTopology C)
  exact ordered_counit_comparison F G c B U K p p' s hp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordered_counit_modules
    (A : Type (u + 1)) [CommRing A] (X Y : Scheme.{u})
    (F G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) (c : F ≅ G)
    (B U : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (p : ((derivedTensor (ModuleCat.{u + 1} A) Y).obj (F.obj B)).obj K ≅
      F.obj (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj U))
    (p' : ((derivedTensor (ModuleCat.{u + 1} A) Y).obj (G.obj B)).obj K ≅
      G.obj (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj U))
    (s : G.obj B ⟶ derivedTensorUnit (ModuleCat.{u + 1} A) Y)
    (hp : p.hom ≫ c.hom.app (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj U) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map (c.hom.app B)).app K ≫ p'.hom) :
    F.map (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app B).app U) ≫ p.inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map (c.hom.app B ≫ s)).app K ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y K).hom =
      c.hom.app (((derivedTensor (ModuleCat.{u + 1} A) X).obj U).obj B) ≫
        ((G.map (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app B).app U) ≫ p'.inv) ≫
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).inv.app K).app (G.obj B))) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map s ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom := by
  exact ordered_counit_derived (ModuleCat.{u + 1} A) X Y F G c B U K p p' s hp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem unitLeftUnitor_app
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (Y : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (derivedTensorUnitLeftUnitor C Y).hom.app K = (derivedTensorLeftUnitor C Y K).hom := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensorTrace_app
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (Y : Scheme.{u})
    {B : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)}
    (τ : B ⟶ (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf Y.smallEtaleTopology C).obj (MonoidalCategoryStruct.tensorUnit C)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (ordinaryDerivedTensorTrace C Y τ).app K =
      ((derivedTensor C Y).obj K).map (τ ≫ (singleFunctorObjUnitIso C Y).hom) ≫
        (derivedTensorRightUnitor C Y K).hom := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] derivedTensor singleFunctorObjUnitIso
  rightDerivedLowerShriekOfCompactification

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kernelCounit_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    {B : DerivedCategoryModule A X} (D : TraceDiagonalDatum A q B)
    (K : DerivedCategoryModule A Y) :
    (SfDiagonalKernel.counit A D).app K =
      (projectionIso A q B).inv.app K ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map D.trace).app K ≫
        (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom.app K := by
  rw [SfDiagonalKernel.counit]
  rfl

section FrozenCounit

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finiteP1TraceCounit_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X)
    (τ : (ordinaryFinitePushforward A q).obj B ⟶ ordinaryFiniteUnit A Y)
    (K : DerivedCategoryModule A Y) :
    letI := isIso_finiteP1Projection A q B
    (finiteP1TraceCounit A q B τ).app K =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app
        ((ordinaryFiniteTwistedPullback A q B).obj K) ≫
      (inv (ordinaryFiniteProjectionNatTrans A q B)).app K ≫
        (ordinaryFiniteTensorTrace A Y τ).app K := by
  with_unfolding_all exact Eq.refl _

end FrozenCounit

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finiteTensorTrace_app
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    {B : DerivedCategoryModule A Y} (τ : B ⟶ ordinaryFiniteUnit A Y)
    (K : DerivedCategoryModule A Y) :
    (ordinaryFiniteTensorTrace A Y τ).app K =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        (τ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom) ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom := by
  exact tensorTrace_app (ModuleCat.{u + 1} A) Y τ K

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def star_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((ordinaryFinitePushforward A q).obj B)).obj K ≅
    (ordinaryFinitePushforward A q).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
        ((ordinaryFinitePullback A q).obj K)) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper A isAddTorsion_of_finite q
  let f := ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app B).app K
  let p := asIso f
  exact p

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem star_component_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (star_component A q B K).hom =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app B).app K := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def compact_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [HasCompactification q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj B)).obj K ≅
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
        ((ordinaryFinitePullback A q).obj K)) :=
  (projectionIso A q B).app K

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compact_component_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [HasCompactification q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (compact_component A q B K).hom =
      ((projectionMap (ModuleCat.{u + 1} A) q).app B).app K := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compact_component_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [HasCompactification q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (projectionIso A q B).inv.app K = (compact_component A q B K).inv := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem inverse_app_eq
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (f : F ⟶ G) [IsIso f] (K : C) (p : F.obj K ≅ G.obj K) (hp : p.hom = f.app K) :
    (inv f).app K = p.inv := by
  rw [NatIso.isIso_inv_app]
  apply IsIso.inv_eq_of_hom_inv_id
  rw [← hp]
  exact p.hom_inv_id

private meta def unfoldInstanceBoundary (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  if let .fvar id := e then
    if let some v := (← id.getDecl).value? then return some v
  if let .letE _ _ v b _ := e then return some (b.instantiate1 v)
  let names : List Lean.Name := [``DerivedCategoryModule, ``presentedFiniteP1Trace,
    `AlgebraicGeometry.Etale.SfP1Transport.trace, ``ordinaryFiniteTwistedPullback,
    ``derivedTensorRight, ``ordinaryFiniteP1SplittingTarget, ``derivedTensorUnit,
    ``ordinaryFinitePullback, ``CoordinateTrace.pull, ``ordinaryFinitePushforward,
    ``ordinaryFiniteTensor, ``rightDerivedLowerShriek]
  if let some n := e.getAppFn.constName? then
    if names.contains n then
      return ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e)
  if e.getAppFn.isConstOf ``Functor.obj then
    let args := e.getAppArgs
    if args.size ≥ 2 && (args[args.size - 2]!).getAppFn.isConstOf ``Functor.id then
      return some (← Lean.Meta.withTransparency .all (Lean.Meta.whnf e))
  return none

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem whiskering_object
    {C₁ C₂ D₁ D₂ E : Type*} [Category C₁] [Category C₂] [Category D₁]
    [Category D₂] [Category E]
    (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (T : D₁ ⥤ D₂ ⥤ E)
    (B : C₁) (K : C₂) :
    (((((Functor.whiskeringLeft₂ E).obj F₁).obj F₂).obj T).obj B).obj K =
      (T.obj (F₁.obj B)).obj (F₂.obj K) := rfl

-- Use explicit objectwise formulas before comparing different functor presentations.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem flipped_object
    {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D ⥤ E) (B : D) (K : C) :
    (T.flip.obj B).obj K = (T.obj K).obj B := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem composite_object
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (K : C) : (F ⋙ G).obj K = G.obj (F.obj K) := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem twisted_object
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (ordinaryFiniteTwistedPullback A q B).obj K =
      ((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A q).obj K)).obj B := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_right_object
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (Y : Scheme.{u})
    (B K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (derivedTensorRight C Y B).obj K = ((derivedTensor C Y).obj K).obj B := rfl

private meta def objectBoundaryProof (e : Lean.Expr) :
    Lean.MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if e.getAppFn.isConstOf ``Iso.hom then
    let aa := e.getAppArgs
    let iso := aa[aa.size - 1]!
    if iso.getAppFn.constName? == some ``star_component then
      let bb := iso.getAppArgs
      let pf ← Lean.Meta.mkAppM ``star_component_hom
        #[bb[0]!, bb[bb.size - 4]!, bb[bb.size - 2]!, bb[bb.size - 1]!]
      let ty ← Lean.Meta.inferType pf
      return some (ty.getAppArgs[2]!, ← Lean.Meta.mkAppM ``heq_of_eq #[pf])
  let mut head := e
  let mut chain : Array Lean.Expr := #[]
  while head.getAppFn.isConstOf ``Functor.obj do
    let args := head.getAppArgs
    chain := chain.push args[args.size - 1]!
    head := args[args.size - 2]!
  if head.getAppFn.isConstOf ``Functor.whiskeringLeft₂ && chain.size == 5 then
    let pf ← Lean.Meta.mkAppM ``whiskering_object
      #[chain[4]!, chain[3]!, chain[2]!, chain[1]!, chain[0]!]
    let ty ← Lean.Meta.inferType pf
    return some (ty.getAppArgs[2]!, ← Lean.Meta.mkAppM ``heq_of_eq #[pf])
  unless e.getAppFn.isConstOf ``Functor.obj do return none
  let aa := e.getAppArgs
  unless aa.size ≥ 2 do return none
  let inner := aa[aa.size - 2]!
  if inner.getAppFn.isConstOf ``derivedTensorRight then
    let cc := inner.getAppArgs
    let pf ← Lean.Meta.mkAppM ``tensor_right_object
      #[cc[0]!, cc[cc.size - 4]!, cc[cc.size - 1]!, aa[aa.size - 1]!]
    let ty ← Lean.Meta.inferType pf
    return some (ty.getAppArgs[2]!, ← Lean.Meta.mkAppM ``heq_of_eq #[pf])
  if inner.getAppFn.isConstOf ``Functor.comp then
    let cc := inner.getAppArgs
    let pf ← Lean.Meta.mkAppM ``composite_object
      #[cc[cc.size - 2]!, cc[cc.size - 1]!, aa[aa.size - 1]!]
    let ty ← Lean.Meta.inferType pf
    return some (ty.getAppArgs[2]!, ← Lean.Meta.mkAppM ``heq_of_eq #[pf])
  if inner.getAppFn.isConstOf ``ordinaryFiniteTwistedPullback then
    let cc := inner.getAppArgs
    let pf ← Lean.Meta.mkAppM ``twisted_object
      #[cc[0]!, cc[cc.size - 2]!, cc[cc.size - 1]!, aa[aa.size - 1]!]
    let ty ← Lean.Meta.inferType pf
    return some (ty.getAppArgs[2]!, ← Lean.Meta.mkAppM ``heq_of_eq #[pf])
  unless inner.getAppFn.isConstOf ``Functor.obj do return none
  let bb := inner.getAppArgs
  unless bb.size ≥ 2 do return none
  let bifunctor := bb[bb.size - 2]!
  if bifunctor.getAppFn.isConstOf ``Functor.flip then
    let cc := bifunctor.getAppArgs
    let pf ← Lean.Meta.mkAppM ``flipped_object
      #[cc[cc.size - 1]!, bb[bb.size - 1]!, aa[aa.size - 1]!]
    let ty ← Lean.Meta.inferType pf
    return some (ty.getAppArgs[2]!, ← Lean.Meta.mkAppM ``heq_of_eq #[pf])
  let theoremName ←
    if bifunctor.getAppFn.isConstOf ``derivedTensorRightDerivedLowerShriek then
      pure ``derivedTensorRightDerivedLowerShriek_obj_obj
    else if bifunctor.getAppFn.isConstOf
        ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar then
      pure ``rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj
    else if bifunctor.getAppFn.isConstOf ``derivedTensorRightDerivedLowerStar then
      pure ``derivedTensorRightDerivedLowerStar_obj_obj
    else if bifunctor.getAppFn.isConstOf
        ``rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar then
      pure ``rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar_obj_obj
    else return none
  let cc := bifunctor.getAppArgs
  let pf ← Lean.Meta.mkAppM theoremName
    #[cc[0]!, cc[cc.size - 1]!, bb[bb.size - 1]!, aa[aa.size - 1]!]
  let ty ← Lean.Meta.inferType pf
  let rhs := ty.getAppArgs[2]!
  return some (rhs, ← Lean.Meta.mkAppM ``heq_of_eq #[pf])

/-- Build a kernel-checked congruence, avoiding expansion of the derived functors. -/
private meta def traceProofCongruence : Nat → String → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, _, _, _ => throwError "trace congruence exhausted its structural depth"
  | fuel + 1, path, lhs, rhs => do
    let lhs := (← Lean.instantiateMVars lhs).consumeMData.headBeta
    let rhs := (← Lean.instantiateMVars rhs).consumeMData.headBeta
    if lhs == rhs then
      return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
    if let (.const n _, .const m _) := (lhs, rhs) then
      if n == m then return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
    if lhs.isSort && rhs.isSort && (← Lean.Meta.isDefEq lhs rhs) then
      return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
    if ← Lean.Meta.isProp (← Lean.Meta.inferType lhs) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[lhs, rhs]
    if let some (lhs', p) ← objectBoundaryProof lhs then
      let q ← traceProofCongruence fuel (path ++ "/objL") lhs' rhs
      return ← Lean.Meta.mkAppM ``HEq.trans #[p, q]
    if let some (rhs', p) ← objectBoundaryProof rhs then
      let q ← traceProofCongruence fuel (path ++ "/objR") lhs rhs'
      let p' ← Lean.Meta.mkAppM ``HEq.symm #[p]
      return ← Lean.Meta.mkAppM ``HEq.trans #[q, p']
    let aa := lhs.getAppArgs
    let bb := rhs.getAppArgs
    let sameHead := lhs.getAppFn == rhs.getAppFn ||
      (lhs.getAppFn.constName?.isSome && lhs.getAppFn.constName? == rhs.getAppFn.constName?)
    unless sameHead && aa.size == bb.size && aa.size > 0 do
      if let some a ← unfoldInstanceBoundary lhs then
        return ← traceProofCongruence fuel (path ++ "/unfoldL") a rhs
      if let some b ← unfoldInstanceBoundary rhs then
        return ← traceProofCongruence fuel (path ++ "/unfoldR") lhs b
      if lhs.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory ||
          rhs.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory then
        if ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq lhs rhs) then
          return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
      throwError "non-proof disagreement at {path}: {lhs} versus {rhs}"
    let ct ← Lean.Meta.mkHCongrWithArity lhs.getAppFn aa.size
    let mut pf := ct.proof
    for i in [:aa.size] do
      let ih ← traceProofCongruence fuel
        (path ++ "/" ++ toString lhs.getAppFn.constName? ++ ":" ++ toString i) aa[i]! bb[i]!
      let arg ← match ct.argKinds[i]! with
        | .eq => Lean.Meta.mkAppM ``eq_of_heq #[ih]
        | .heq => pure ih
        | _ => throwError "unexpected congruence argument"
      pf := Lean.mkAppN pf #[aa[i]!, bb[i]!, arg]
    if (← Lean.Meta.inferType pf).isEq then
      return ← Lean.Meta.mkAppM ``heq_of_eq #[pf]
    return pf

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem proper_projection_compatible
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (compact_component A q B K).hom ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj
            ((ordinaryFinitePullback A q).obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app B)).app K ≫
        (star_component A q B K).hom := by
  rw [compact_component_hom, star_component_hom]
  have hs := projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) q B K
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let h := (← Lean.Meta.getLocalDeclFromUserName `hs).toExpr
      let lhs ← Lean.Meta.inferType h
      let rhs ← g.getType
      let heq ← traceProofCongruence 150 "root" lhs rhs
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[heq]
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, h])
    Lean.Elab.Tactic.replaceMainGoal []

attribute [-instance] CategoryTheory.catToReflQuiver in
private noncomputable def ordered_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((ordinaryFiniteTensor A Y).obj K).obj ((ordinaryFinitePushforward A q).obj B) ≅
      (ordinaryFinitePushforward A q).obj
        (((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A q).obj K)).obj B) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).app K).app
      ((ordinaryFinitePushforward A q).obj B) ≪≫
    star_component A q B K ≪≫ (ordinaryFinitePushforward A q).mapIso
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app B).app
        ((ordinaryFinitePullback A q).obj K))

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordered_component_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (ordered_component A q B K).hom = (ordinaryFiniteProjectionNatTrans A q B).app K := by
  unfold ordinaryFiniteProjectionNatTrans ordinaryFiniteProjection
  dsimp only [ordered_component, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty ← g.getType
      let aa := ty.getAppArgs
      let heq ← traceProofCongruence 150 "root" aa[1]! aa[2]!
      g.assign (← Lean.Meta.mkAppM ``eq_of_heq #[heq])
    Lean.Elab.Tactic.replaceMainGoal []

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordered_counit_native
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y)
    (s : (ordinaryFinitePushforward A q).obj B ⟶
      derivedTensorUnit (ModuleCat.{u + 1} A) Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app B).app
          ((ordinaryFinitePullback A q).obj K)) ≫
      (compact_component A q B K).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app B ≫ s)).app K ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y K).hom =
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((ordinaryFinitePullback A q).obj K)).obj B) ≫
      (((ordinaryFinitePushforward A q).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app B).app
            ((ordinaryFinitePullback A q).obj K)) ≫
          (star_component A q B K).inv) ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).inv.app K).app
          ((ordinaryFinitePushforward A q).obj B)) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map s ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom := by
  exact ordered_counit_modules A X Y
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q) (ordinaryFinitePushforward A q)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q)
    B ((ordinaryFinitePullback A q).obj K) K
    (compact_component A q B K) (star_component A q B K) s
    (proper_projection_compatible A q B K)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordered_component_inverse
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    letI := isIso_finiteP1Projection A q B
    (inv (ordinaryFiniteProjectionNatTrans A q B)).app K =
      (ordered_component A q B K).inv := by
  let := isIso_finiteP1Projection A q B
  exact inverse_app_eq (ordinaryFiniteProjectionNatTrans A q B) K
    (ordered_component A q B K) (ordered_component_hom A q B K)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordered_counit_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y)
    (s : (ordinaryFinitePushforward A q).obj B ⟶
      derivedTensorUnit (ModuleCat.{u + 1} A) Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app B).app
          ((ordinaryFinitePullback A q).obj K)) ≫
      (compact_component A q B K).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) q).hom.app B ≫ s)).app K ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y K).hom =
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((ordinaryFinitePullback A q).obj K)).obj B) ≫
      (ordered_component A q B K).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map s ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom := by
  dsimp only [ordered_component, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
  exact ordered_counit_native A q B K s

private meta def traceProofCongruenceStep
    (recur : String → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr)
    (facts : Array (Lean.Expr × Lean.Expr × Lean.Expr))
    (path : String) (lhs rhs : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if lhs == rhs then
    return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
  if let (.const n _, .const m _) := (lhs, rhs) then
    if n == m then return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
  if lhs.isSort && rhs.isSort && (← Lean.Meta.isDefEq lhs rhs) then
    return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
  if ← Lean.Meta.isProp (← Lean.Meta.inferType lhs) then
    return ← Lean.Meta.mkAppM ``proof_irrel_heq #[lhs, rhs]
  for (x, y, p) in facts do
    if lhs == x then
      let q ← recur (path ++ "/factL") y rhs
      return ← Lean.Meta.mkAppM ``HEq.trans #[p, q]
    if rhs == x then
      let q ← recur (path ++ "/factR") lhs y
      let p' ← Lean.Meta.mkAppM ``HEq.symm #[p]
      return ← Lean.Meta.mkAppM ``HEq.trans #[q, p']
  if let some (lhs', p) ← objectBoundaryProof lhs then
    let q ← recur (path ++ "/objL") lhs' rhs
    return ← Lean.Meta.mkAppM ``HEq.trans #[p, q]
  if let some (rhs', p) ← objectBoundaryProof rhs then
    let q ← recur (path ++ "/objR") lhs rhs'
    let p' ← Lean.Meta.mkAppM ``HEq.symm #[p]
    return ← Lean.Meta.mkAppM ``HEq.trans #[q, p']
  let aa := lhs.getAppArgs
  let bb := rhs.getAppArgs
  let sameHead := lhs.getAppFn == rhs.getAppFn ||
    (lhs.getAppFn.constName?.isSome && lhs.getAppFn.constName? == rhs.getAppFn.constName?)
  unless sameHead && aa.size == bb.size && aa.size > 0 do
    if let some a ← unfoldInstanceBoundary lhs then
      return ← recur (path ++ "/unfoldL") a rhs
    if let some b ← unfoldInstanceBoundary rhs then
      return ← recur (path ++ "/unfoldR") lhs b
    if lhs.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory ||
        rhs.getAppFn.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory then
      if ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq lhs rhs) then
        return ← Lean.Meta.mkAppM ``HEq.refl #[lhs]
    throwError "non-proof disagreement at {path}: {lhs} versus {rhs}"
  let ct ← Lean.Meta.mkHCongrWithArity lhs.getAppFn aa.size
  let mut pf := ct.proof
  for i in [:aa.size] do
    let ih ← recur
      (path ++ "/" ++ toString lhs.getAppFn.constName? ++ ":" ++ toString i) aa[i]! bb[i]!
    let arg ← match ct.argKinds[i]! with
      | .eq => Lean.Meta.mkAppM ``eq_of_heq #[ih]
      | .heq => pure ih
      | _ => throwError "unexpected congruence argument"
    pf := Lean.mkAppN pf #[aa[i]!, bb[i]!, arg]
  if (← Lean.Meta.inferType pf).isEq then
    return ← Lean.Meta.mkAppM ``heq_of_eq #[pf]
  return pf

private meta def memoTraceProofCongruenceWithFacts
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (facts : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
    Nat → String → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, _, _, _ => throwError "trace congruence exhausted its structural depth"
  | fuel + 1, path, lhs, rhs => do
    let lhs := (← Lean.instantiateMVars lhs).consumeMData.headBeta
    let rhs := (← Lean.instantiateMVars rhs).consumeMData.headBeta
    let old ← cache.get
    if let some pf := old[(lhs, rhs)]? then return pf
    let result ← traceProofCongruenceStep
      (memoTraceProofCongruenceWithFacts cache facts fuel) facts path lhs rhs
    cache.modify fun old ↦ old.insert (lhs, rhs) result
    return result

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Proper coincidence and tensor symmetry identify the kernel counit with the
specified inverse ordered-projection counit.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, G7 and proper coincidence.
(auxiliary; not a blueprint node)

Proof: proper coincidence commutes with the canonical projection map. Cancel the two
projection isomorphisms to compare their inverses. Naturality of the source braiding
moves it through proper coincidence. Naturality of the target braiding moves the trace
from the left factor to the right factor; the braiding with the unit identifies the
left unitor with the right unitor. The ordered ordinary projection is the symmetry
conjugate of the original projection, so its inverse has precisely these factors.
This argument uses actual maps and applies on the unbounded categories. -/
theorem finiteP1TraceCounit_kernel_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    (B : DerivedCategoryModule A X) (D : TraceDiagonalDatum A q B)
    (τ : (ordinaryFinitePushforward A q).obj B ⟶ ordinaryFiniteUnit A Y)
    (hτ : D.trace =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) q).hom.app B ≫
        τ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom)
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app B).app
          ((ordinaryFinitePullback A q).obj K)) ≫ (SfDiagonalKernel.counit A D).app K =
      (finiteP1TraceCounit A q B τ).app K := by
  have hc := ordered_counit_component A q B K
    (τ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom)
  have hk := kernelCounit_app A q D K
  have ho := finiteP1TraceCounit_app A q B τ K
  have hi := ordered_component_inverse A q B K
  have hp := compact_component_inv A q B K
  have hl := unitLeftUnitor_app (ModuleCat.{u + 1} A) Y K
  have hr := finiteTensorTrace_app A Y τ K
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let mut facts := #[]
      for n in #[`hk, `ho, `hi, `hp, `hl, `hr, `hτ] do
        let h := (← Lean.Meta.getLocalDeclFromUserName n).toExpr
        let ty ← Lean.Meta.whnf (← Lean.instantiateMVars (← Lean.Meta.inferType h))
        let aa := ty.getAppArgs
        unless ty.isEq do throwError "expected an equality fact: {ty}"
        let p ← Lean.Meta.mkAppM ``heq_of_eq #[h]
        facts := facts.push (aa[1]!, aa[2]!, p)
      let h := (← Lean.Meta.getLocalDeclFromUserName `hc).toExpr
      let lhs ← Lean.Meta.inferType h
      let rhs ← g.getType
      let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
      let pf ← memoTraceProofCongruenceWithFacts cache facts 150 "root" lhs rhs
      let eq ← Lean.Meta.mkAppM ``eq_of_heq #[pf]
      g.assign (← Lean.Meta.mkAppM ``Eq.mp #[eq, h])
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.Etale

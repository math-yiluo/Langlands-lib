/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.OrdinaryReductionPullComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Canonical reduction and pullback composition

The comparison is specified on K-flat complexes and by ordinary limit projections.
Source: blueprint latest, fix-prop-coherence.proof.md, maps-used sentence
(blueprint: lem-sf-canonical-reduction-pull-composition).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.GeneratorReduction

open IntegralSystemRealization

attribute [local implicit_reducible] PurCompactSupport.completed
  pullbackTensorSequenceDerived integralOperationsGoodLocalization
  coefficientSequenceHasDerived
  scalarReductionSourceDerived integralTowerHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted coefficientSequenceCommRingSystem
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSheaf
  Functor.leftAdjoint presheafToSheaf

private theorem map_triple
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' E' : C} (f : A ⟶ B) (g : B ⟶ C') (h : C' ⟶ D')
    (i : A ⟶ E') (j : E' ⟶ D') (w : f ≫ g ≫ h = i ≫ j) :
    F.map f ≫ F.map g ≫ F.map h = F.map i ≫ F.map j := by
  simpa only [Functor.map_comp] using congrArg (fun k : A ⟶ D' ↦ F.map k) w

private theorem pull_good
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    integralOperationsGoodComplex l E X
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj) := by
  exact AlgebraicGeometry.ProEtale.VaryingRing.ringPull_preserves_flat f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f) P.obj P.property.1 P.property.2

private noncomputable def ordinaryComp
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    integralOrdinaryPull l E (f ≫ g) ≅
      integralOrdinaryPull l E g ⋙ integralOrdinaryPull l E f :=
  (conjugateIsoEquiv
    ((AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction g
      ((PurCompactSupport.completed l E).ring Z)
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).pull g)).comp
    (AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)))
    (AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction (f ≫ g)
      ((PurCompactSupport.completed l E).ring Z)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull (f ≫ g)))).symm
    (PurCompactSupport.modulePushComposition_existsUnique
      (PurCompactSupport.completed l E) f g
      (PurCompactSupport.completedPull_comp l E f g)).exists.choose

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryFactors

private theorem derived_comp_factors
    {C D A : Type*} [Category C] [Category D] [Category A]
    [Abelian C] [Abelian D] [Abelian A]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory A]
    (F : C ⥤ D) (G : D ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    (F ⋙ G).mapDerivedCategoryFactors.hom.app P := by
  have hc := Functor.mapDerivedCategoryCompIso_fac F G P
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).hom.app P = 𝟙 _ := by
    ext n
    rfl
  rw [hi] at hc
  have hqi : DerivedCategory.Q.map (𝟙
      ((F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)).obj P)) =
      𝟙 _ := DerivedCategory.Q.map_id _
  rw [hqi] at hc
  erw [Category.comp_id] at hc
  exact hc

private theorem ringed_comp_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : CochainComplex (scalarReductionSource l E Z) ℤ) :
    (ringedPullComp l E f g).hom.app (DerivedCategory.Q.obj P) ≫
        (ringedPull l E f).map
          ((integralOrdinaryPull l E g).mapDerivedCategoryFactors.hom.app P) ≫
        (integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app
          (((integralOrdinaryPull l E g).mapHomologicalComplex (.up ℤ)).obj P) =
      (integralOrdinaryPull l E (f ≫ g)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryComp l E f g) (.up ℤ)).hom.app P) := by
  change ((Functor.mapDerivedCategoryNatIso (ordinaryComp l E f g)).hom.app _ ≫
    (Functor.mapDerivedCategoryCompIso _ _).inv.app _) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  rw [derived_comp_factors, Functor.mapDerivedCategoryNatIso_fac]
  rfl

attribute [local irreducible] pullbackTensorOrdinaryReduction pullbackTensorOrdinaryLimit
  pullbackTensorSequenceInverse AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  pullbackTensorCalculus pullbackTensorReductionModel ringedPullComp sheafCompose
  DerivedCategory.Q pullbackTensorSequenceDirect pullbackTensorOrdinaryAdjunction
  pullbackTensorSequenceAdjunction AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction OrdinaryLimitModel.reductionPull

private theorem ringed_comp_model_map
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : CochainComplex (scalarReductionSource l E Z) ℤ)
    (R : DerivedCategory (scalarReductionSource l E X) ⥤ coefficientSequenceDerived l E X) :
    R.map ((ringedPullComp l E f g).hom.app (DerivedCategory.Q.obj P)) ≫
      R.map ((ringedPull l E f).map
        ((integralOrdinaryPull l E g).mapDerivedCategoryFactors.hom.app P)) ≫
      R.map ((integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app
        (((integralOrdinaryPull l E g).mapHomologicalComplex (.up ℤ)).obj P)) =
    R.map ((integralOrdinaryPull l E (f ≫ g)).mapDerivedCategoryFactors.hom.app P) ≫
      R.map (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinaryComp l E f g) (.up ℤ)).hom.app P)) := by
  exact map_triple R _ _ _ _ _ (ringed_comp_model l E f g P)

private theorem on_good
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) (a : RealizationModel l E o) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : (integralOperationsGoodComplex l E Z).FullSubcategory) :
    (calculus l E X).reduction.map
        ((ringedPullComp l E f g).hom.app (DerivedCategory.Q.obj P.obj)) ≫
        (a.reductionPull f).hom.app
          ((ringedPull l E g).obj (DerivedCategory.Q.obj P.obj)) ≫
        (pull l E f).map ((a.reductionPull g).hom.app (DerivedCategory.Q.obj P.obj)) =
      (a.reductionPull (f ≫ g)).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (c.pullComp f g).hom.app
          ((calculus l E Z).reduction.obj (DerivedCategory.Q.obj P.obj)) := by
  let G := integralOrdinaryPull l E g
  let F := integralOrdinaryPull l E f
  let H := integralOrdinaryPull l E (f ≫ g)
  let S := pullbackTensorSequenceInverse l E f
  let T := pullbackTensorSequenceInverse l E g
  let RX := (calculus l E X).reduction
  let Q := DerivedCategory.Q (C := coefficientSequenceModules l E X)
  let Pg : (integralOperationsGoodComplex l E Y).FullSubcategory :=
    ⟨(G.mapHomologicalComplex (.up ℤ)).obj P.obj, pull_good l E g P⟩
  let Pfg : (integralOperationsGoodComplex l E X).FullSubcategory :=
    ⟨(F.mapHomologicalComplex (.up ℤ)).obj Pg.obj, pull_good l E f Pg⟩
  let Ph : (integralOperationsGoodComplex l E X).FullSubcategory :=
    ⟨(H.mapHomologicalComplex (.up ℤ)).obj P.obj, pull_good l E (f ≫ g) P⟩
  let d := (NatIso.mapHomologicalComplex (ordinaryComp l E f g) (.up ℤ)).hom.app P.obj
  let e := (NatIso.mapHomologicalComplex (c.ordinaryPull f g) (.up ℤ)).hom.app
    (((pullbackTensorOrdinaryReduction l E Z).mapHomologicalComplex (.up ℤ)).obj P.obj)
  let df := a.ordinary.reductionPullComplex l E f Pg.obj
  let dg := a.ordinary.reductionPullComplex l E g P.obj
  let dh := a.ordinary.reductionPullComplex l E (f ≫ g) P.obj
  have ho : ((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).map d ≫
      df ≫ (S.mapHomologicalComplex (.up ℤ)).map dg = dh ≫ e := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact ordinaryReductionPullComposition l E o a.ordinary c f g (P.obj.X i)
  let post := (pull l E f).map ((pull l E g).map
      ((pullbackTensorReductionModel l E Z).hom.app P)) ≫
    (pull l E f).map (T.mapDerivedCategoryFactors.hom.app
      (((pullbackTensorOrdinaryReduction l E Z).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
    S.mapDerivedCategoryFactors.hom.app
      ((T.mapHomologicalComplex (.up ℤ)).obj
        (((pullbackTensorOrdinaryReduction l E Z).mapHomologicalComplex (.up ℤ)).obj P.obj))
  apply (CategoryTheory.cancel_mono (C := coefficientSequenceDerived l E X) post).1
  dsimp only [post]
  simp only [Category.assoc]
  have hmg := congrArg (fun k ↦ (pull l E f).map k)
    (a.model g P (pull_good l E g P))
  simp only [Functor.map_comp] at hmg
  rw [reassoc_of% hmg]
  rw [← reassoc_of% (a.reductionPull f).hom.naturality
    (G.mapDerivedCategoryFactors.hom.app P.obj)]
  have hnf := S.mapDerivedCategoryFactors.hom.naturality dg
  dsimp only [Functor.comp_map] at hnf
  change (pull l E f).map (DerivedCategory.Q.map dg) ≫
      S.mapDerivedCategoryFactors.hom.app _ =
    S.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map dg) at hnf
  rw [hnf]
  rw [reassoc_of% (a.model f Pg (pull_good l E f Pg))]
  have hm := ringed_comp_model_map l E f g P.obj RX
  conv_lhs =>
    rw [(reassoc_of% hm) ((pullbackTensorReductionModel l E X).hom.app Pfg ≫
      Q.map df ≫ Q.map ((S.mapHomologicalComplex (.up ℤ)).map dg))]
  have hnr : RX.map (DerivedCategory.Q.map d) ≫
      (pullbackTensorReductionModel l E X).hom.app Pfg =
    (pullbackTensorReductionModel l E X).hom.app Ph ≫
      Q.map (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).map d) :=
    (pullbackTensorReductionModel l E X).hom.naturality
      (ObjectProperty.homMk d : Ph ⟶ Pfg)
  conv_lhs =>
    rw [(reassoc_of% hnr) (Q.map df ≫ Q.map ((S.mapHomologicalComplex (.up ℤ)).map dg))]
  have hqo := map_triple Q _ _ _ _ _ ho
  conv_lhs => rw [hqo]
  have hnc : (c.pullComp f g).hom.app
      ((calculus l E Z).reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
      (pull l E f).map ((pull l E g).map
        ((pullbackTensorReductionModel l E Z).hom.app P)) =
    (pull l E (f ≫ g)).map ((pullbackTensorReductionModel l E Z).hom.app P) ≫
      (c.pullComp f g).hom.app (DerivedCategory.Q.obj
        (((pullbackTensorOrdinaryReduction l E Z).mapHomologicalComplex (.up ℤ)).obj P.obj)) :=
    ((c.pullComp f g).hom.naturality
      ((pullbackTensorReductionModel l E Z).hom.app P)).symm
  conv_rhs =>
    rw [(reassoc_of% hnc)
      ((pull l E f).map (T.mapDerivedCategoryFactors.hom.app
        (((pullbackTensorOrdinaryReduction l E Z).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
        S.mapDerivedCategoryFactors.hom.app ((T.mapHomologicalComplex (.up ℤ)).obj
          (((pullbackTensorOrdinaryReduction l E Z).mapHomologicalComplex (.up ℤ)).obj P.obj)))]
  conv_rhs =>
    rw [c.pullComp_model f g
      (((pullbackTensorOrdinaryReduction l E Z).mapHomologicalComplex (.up ℤ)).obj P.obj)]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ Q.map e)
    (a.model (f ≫ g) P (pull_good l E (f ≫ g) P)).symm

/-- Canonical quotient/pullback comparison preserves the specified geometric compositor.
Source: blueprint latest, sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md, maps-used sentence; Stacks 03D7, 07A6, 0D6D and 0941.
(blueprint: lem-sf-canonical-reduction-pull-composition).

Proof: first compare ordinary direct images followed by the ordinary limit functor.
Postcompose with every limit projection and evaluate on a section of a pro-etale object.
The two composites are equal: both apply the projection and the same two base-change
maps. The projection normalization in OrdinaryLimitModel and the section normalization
of the ringed and sequence direct-image compositors give exactly these two expressions.
Ordinary limit projections are jointly monic, so the ordinary comparisons paste.
Conjugate by the ordinary pullback/direct-image and quotient/limit adjunctions. Mates
preserve pasting; this gives the ordinary reduction/pullback compositor equation.
Apply it degreewise to a flat-term K-flat complex. The model equations for reductionPull
and pullComp, and the mapDerivedCategoryCompIso used by ringedPullComp, identify its
localization with the displayed equation. Such complexes resolve every derived object;
naturality transports the equality along the resolving isomorphism. This argument uses
whole complexes and whole strict systems, without equality detection by derived finite
evaluations. Identity morphisms and zero complexes use the same projection calculation. -/
theorem canonicalReductionPullComposition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : IntegralSystemRealization.Operations l E)
    (a : IntegralSystemRealization.RealizationModel l E o)
    (c : IntegralSystemRealization.Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory (scalarReductionSource l E Z)) :
    (IntegralSystemRealization.calculus l E X).reduction.map
        ((IntegralSystemRealization.ringedPullComp l E f g).hom.app K) ≫
        (a.reductionPull f).hom.app
          ((IntegralSystemRealization.ringedPull l E g).obj K) ≫
        (IntegralSystemRealization.pull l E f).map
          ((a.reductionPull g).hom.app K) =
      (a.reductionPull (f ≫ g)).hom.app K ≫
        (c.pullComp f g).hom.app
          ((IntegralSystemRealization.calculus l E Z).reduction.obj K) := by
  let L := integralOperationsGoodLocalization l E Z
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E Z) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Z).ι
  let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E Z
  let lhs := Functor.whiskerRight (ringedPullComp l E f g).hom
      (calculus l E X).reduction ≫
    Functor.whiskerLeft (ringedPull l E g) (a.reductionPull f).hom ≫
    Functor.whiskerRight (a.reductionPull g).hom (pull l E f)
  let rhs := (a.reductionPull (f ≫ g)).hom ≫
    Functor.whiskerLeft (calculus l E Z).reduction (c.pullComp f g).hom
  have he : lhs = rhs := by
    apply Localization.natTrans_ext L W
    intro P
    exact on_good l E o a c f g P
  exact congr_app he K

end WeilConjectures.GeneratorReduction

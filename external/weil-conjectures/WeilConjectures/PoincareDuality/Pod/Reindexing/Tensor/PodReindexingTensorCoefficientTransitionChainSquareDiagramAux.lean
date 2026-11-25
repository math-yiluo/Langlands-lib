/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorDescentDiagram
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelTower
import all WeilConjectures.SmoothPurity.Supporting.AdditiveRoosHorizontal
import all WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionChainSquareDiagramFinite

/-! # Strict tower square behind the completed tensor square for scalar/reindexing transitions

Auxiliary module for `PodReindexingTensorCoefficientTransitionChainSquareDiagram`: the finite
level square, the Roos comparisons and the resulting chain square before the diagram wrappers.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-tensor-chain-square-diagram).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] podTensorReindexAdditive podTensorScalarZero podTensorMixedLeftZero
  podTensorMixedRightZero
  podTensorReindexLimits podTensorReindexColimits
attribute [local irreducible] integralCompletedTensor integralOrdinaryScalar
  scalarTensorChain scalarTensorOrdinary
  integralOperationsRoos completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor SheafOfModules.monoidalCategory
attribute [local implicit_reducible] podOrdinaryReindex podGoodReindex
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor integralOperationsTensorOnGood
  scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralOperationsCommHasDerivedCategory
  podTensorScalarGoodFunctor podTensorScalarGoodComparison podTensorReindexGoodComparison
  podTensorGoodConstructibleLocalization
  podTensorGoodConstructible podTensorMixedTensorIso podTensorGoodCoefficientTransition
  podTensorTensorReindexDerivedChain
  podTensorTensorScalarDerivedChain podTensorTensorMixedDerivedChain

attribute [local irreducible] integralOrdinaryTensorSection
  integralCompletedScalarMap scalarAdjunction
attribute [local implicit_reducible] integralOperationsTensorLevel
  integralOperationsTensorComposite integralOperationsRestrict
  integralOperationsTensorTowerFunctor
  Functor.ofOpSequence Functor.ofSequence isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
attribute [local instance 2001] integralOperationsFiniteHasMap

private theorem roosSquare
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasCountableProducts C] [HasCountableProducts D]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (H : A ⥤ C) [H.Additive] (I : C ⥤ D) [I.Additive]
    (s : F ⋙ G ≅ H ⋙ I)
    (C₀ : ℕᵒᵖ ⥤ CochainComplex A ℤ) (C₁ : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C₂ : ℕᵒᵖ ⥤ CochainComplex C ℤ)
    (C₃ C₄ : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (a : C₀ ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ C₁)
    (b : C₁ ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ C₃)
    (c : C₀ ⋙ H.mapHomologicalComplex (.up ℤ) ⟶ C₂)
    (d : C₂ ⋙ I.mapHomologicalComplex (.up ℤ) ⟶ C₄) (r : C₃ ⟶ C₄)
    (hc : whiskerRight a (G.mapHomologicalComplex (.up ℤ)) ≫ b ≫ r =
      whiskerLeft C₀ (NatIso.mapHomologicalComplex s (.up ℤ)).hom ≫
        whiskerRight c (I.mapHomologicalComplex (.up ℤ)) ≫ d) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (scalarRoosMap F C₀ ≫ integralOperationsRoosMap a) ≫
      scalarRoosMap G C₁ ≫ integralOperationsRoosMap b ≫ integralOperationsRoosMap r =
    (NatIso.mapHomologicalComplex s (.up ℤ)).hom.app (integralOperationsRoos C₀) ≫
      (I.mapHomologicalComplex (.up ℤ)).map
        (scalarRoosMap H C₀ ≫ integralOperationsRoosMap c) ≫
      scalarRoosMap I C₂ ≫ integralOperationsRoosMap d := by
  -- Compare both routes with the Roos map of their common strict tower map.
  have h₁ := roos_composite F G (H ⋙ I) s.hom C₀ C₁ C₄ a (b ≫ r)
    (whiskerRight c (I.mapHomologicalComplex (.up ℤ)) ≫ d) hc
  have h₂ := roos_composite H I (H ⋙ I) (𝟙 (H ⋙ I)) C₀ C₂ C₄ c d
    (whiskerRight c (I.mapHomologicalComplex (.up ℤ)) ≫ d) (by
      apply NatTrans.ext
      funext n
      simp only [NatTrans.comp_app, whiskerLeft_app, NatTrans.mapHomologicalComplex_id,
        NatTrans.id_app]
      erw [Category.id_comp])
  simp only [NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at h₂
  erw [Category.id_comp] at h₂
  simpa only [integralOperationsRoosMap_comp, Category.assoc] using
    h₁.trans (congrArg
      ((NatIso.mapHomologicalComplex s (.up ℤ)).hom.app (integralOperationsRoos C₀) ≫ ·)
      h₂.symm)

private theorem normalizedRoos
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) :
    (D.roos C).hom = scalarRoosMap (isoReductionIntegralInverse l E g) C := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hf, hs, _⟩ := hD
  obtain ⟨hcf, hcs⟩ := scalarRoosCoordinates (isoReductionIntegralInverse l E g) C
  dsimp only [podReindexTower, whiskeringRight_obj_obj] at ⊢
  apply roos_ext
  · have hh := hf C
    dsimp only [podReindexTower, whiskeringRight_obj_obj] at hh
    with_unfolding_all exact hh.trans hcf.symm
  · intro i
    have hh := hs C i
    dsimp only [podReindexTower, whiskeringRight_obj_obj] at hh
    with_unfolding_all exact hh.trans (hcs i).symm

-- The tensor reindexing chain is the reindexing Roos map of its strict tower map.
private theorem chainRoos
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    podReindexTensorChain l E g D T P Q =
      scalarRoosMap (isoReductionIntegralInverse l E g)
          ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)) ≫
        integralOperationsRoosMap (T.tower P Q).hom := by
  unfold podReindexTensorChain
  exact congrArg (fun x ↦ x ≫ integralOperationsRoosFunctor.map (T.tower P Q).hom)
    (normalizedRoos l E g D hD _)

-- The scalar tensor chain is the scalar Roos map of its strict tower map.
private theorem scalarChainRoos
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    scalarTensorChain l E L ι W P Q =
      scalarRoosMap (integralOrdinaryScalar l E L ι W)
          ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) ≫
        integralOperationsRoosMap ((scalarTensorTower l E L ι W).app (P, Q)) := by
  unfold scalarTensorChain
  rfl

-- The derived chain square for abstract exact functors, from a strict tower square.
-- Keeping the functors abstract keeps the comparison of the composite types cheap.
private theorem chainGeneric
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasCountableProducts C] [HasCountableProducts D]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (I : C ⥤ D) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (s : F ⋙ G ≅ H ⋙ I)
    (C₀ : ℕᵒᵖ ⥤ CochainComplex A ℤ) (C₁ : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C₂ : ℕᵒᵖ ⥤ CochainComplex C ℤ)
    (C₃ C₄ : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (a : C₀ ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ C₁)
    (b : C₁ ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ C₃)
    (c : C₀ ⋙ H.mapHomologicalComplex (.up ℤ) ⟶ C₂)
    (d : C₂ ⋙ I.mapHomologicalComplex (.up ℤ) ⟶ C₄) (r : C₃ ⟶ C₄)
    (hc : whiskerRight a (G.mapHomologicalComplex (.up ℤ)) ≫ b ≫ r =
      whiskerLeft C₀ (NatIso.mapHomologicalComplex s (.up ℤ)).hom ≫
        whiskerRight c (I.mapHomologicalComplex (.up ℤ)) ≫ d)
    (p : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C₀) ⟶
      integralOperationsRoos C₁)
    (hp : p = scalarRoosMap F C₀ ≫ integralOperationsRoosMap a)
    (q : (G.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C₁) ⟶
      integralOperationsRoos C₃)
    (hq : q = scalarRoosMap G C₁ ≫ integralOperationsRoosMap b)
    (e : (H.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C₀) ⟶
      integralOperationsRoos C₂)
    (he : e = scalarRoosMap H C₀ ≫ integralOperationsRoosMap c)
    (f : (I.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C₂) ⟶
      integralOperationsRoos C₄)
    (hf : f = scalarRoosMap I C₂ ≫ integralOperationsRoosMap d)
    (w : integralOperationsRoos C₃ ⟶ integralOperationsRoos C₄)
    (hw : w = integralOperationsRoosMap r) :
    G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app (integralOperationsRoos C₀) ≫
          DerivedCategory.Q.map p) ≫
      G.mapDerivedCategoryFactors.hom.app (integralOperationsRoos C₁) ≫
        DerivedCategory.Q.map q ≫ DerivedCategory.Q.map w =
    ((F.mapDerivedCategoryCompIso G ≪≫ mapDerivedCategoryNatIso s ≪≫
        (H.mapDerivedCategoryCompIso I).symm).hom.app
          (DerivedCategory.Q.obj (integralOperationsRoos C₀))) ≫
      I.mapDerivedCategory.map
        (H.mapDerivedCategoryFactors.hom.app (integralOperationsRoos C₀) ≫
          DerivedCategory.Q.map e) ≫
      I.mapDerivedCategoryFactors.hom.app (integralOperationsRoos C₂) ≫
        DerivedCategory.Q.map f := by
  subst hp hq he hf hw
  refine podCoefficientExactSquareChain F G H I s _ _ _ _ _ _ _ _ _ _ ?_
  simpa only [Category.assoc] using roosSquare F G H I s C₀ C₁ C₂ C₃ C₄ a b c d r hc

attribute [local irreducible] integralOperationsTensorTowerFunctor

/-- The derived chain square of the scalar/reindexing tensor transition on fixed good
representatives, before the diagram wrappers are unfolded.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: lem-pod-tensor-chain-square-diagram). -/
theorem podTensorMixedChainSquareCore
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    (A B : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralOrdinaryScalar l E L ι X).mapDerivedCategory.map
        ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E Y).obj (A.obj, B.obj)) ≫
          DerivedCategory.Q.map (podReindexTensorChain l E g D T A B)) ≫
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
          ((integralOperationsTensorComplexFunctor l E X).obj
            (((podGoodReindex l E g D).obj A).obj, ((podGoodReindex l E g D).obj B).obj)) ≫
        DerivedCategory.Q.map (scalarTensorChain l E L ι X ((podGoodReindex l E g D).obj A).obj
          ((podGoodReindex l E g D).obj B).obj) ≫
        DerivedCategory.Q.map ((integralOperationsTensorComplexFunctor l L X).map (Prod.mkHom
          ((S.complex l E g L ι D D').hom.app A.obj)
          ((S.complex l E g L ι D D').hom.app B.obj))) =
    (((isoReductionIntegralInverse l E g).mapDerivedCategoryCompIso
          (integralOrdinaryScalar l E L ι X)) ≪≫
        mapDerivedCategoryNatIso S.ordinary ≪≫
        ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryCompIso
          (isoReductionIntegralInverse l L g)).symm).hom.app
          (DerivedCategory.Q.obj
            ((integralOperationsTensorComplexFunctor l E Y).obj (A.obj, B.obj))) ≫
      (isoReductionIntegralInverse l L g).mapDerivedCategory.map
        ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E Y).obj (A.obj, B.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι Y A.obj B.obj)) ≫
      (isoReductionIntegralInverse l L g).mapDerivedCategoryFactors.hom.app
          ((integralOperationsTensorComplexFunctor l L Y).obj
            (((podTensorScalarGoodFunctor l E L ι Y).obj A).obj,
              ((podTensorScalarGoodFunctor l E L ι Y).obj B).obj)) ≫
        DerivedCategory.Q.map (podReindexTensorChain l L g D' T'
          ((podTensorScalarGoodFunctor l E L ι Y).obj A)
          ((podTensorScalarGoodFunctor l E L ι Y).obj B)) := by
  let F := isoReductionIntegralInverse l E g
  let G := integralOrdinaryScalar l E L ι X
  let H := integralOrdinaryScalar l E L ι Y
  let I := isoReductionIntegralInverse l L g
  let AX := (podGoodReindex l E g D).obj A
  let BX := (podGoodReindex l E g D).obj B
  let AL := (podTensorScalarGoodFunctor l E L ι Y).obj A
  let BL := (podTensorScalarGoodFunctor l E L ι Y).obj B
  let r := (integralOperationsTensorTowerFunctor l L X).map (Prod.mkHom
    ((S.complex l E g L ι D D').hom.app A.obj)
    ((S.complex l E g L ι D D').hom.app B.obj))
  have hd := chainGeneric F G H I S.ordinary
    ((integralOperationsTensorTowerFunctor l E Y).obj (A.obj, B.obj)) _ _ _ _
    (T.tower A B).hom ((scalarTensorTower l E L ι X).app (AX.obj, BX.obj))
    ((scalarTensorTower l E L ι Y).app (A.obj, B.obj)) (T'.tower AL BL).hom r ?ht
    (podReindexTensorChain l E g D T A B) (chainRoos l E g D hD T A B)
    (scalarTensorChain l E L ι X AX.obj BX.obj) (scalarChainRoos l E L ι X AX.obj BX.obj)
    (scalarTensorChain l E L ι Y A.obj B.obj) (scalarChainRoos l E L ι Y A.obj B.obj)
    (podReindexTensorChain l L g D' T' AL BL) (chainRoos l L g D' hD' T' AL BL)
    ((integralOperationsTensorComplexFunctor l L X).map (Prod.mkHom
      ((S.complex l E g L ι D D').hom.app A.obj)
      ((S.complex l E g L ι D D').hom.app B.obj))) rfl
  case ht =>
    apply NatTrans.ext
    funext n
    rcases n with ⟨n⟩
    have hX := (scalarTensorTower_existsUnique l E L ι X).exists.choose_spec
    have hY := (scalarTensorTower_existsUnique l E L ι Y).exists.choose_spec
    change scalarTensorTowerNormalization l E L ι X (scalarTensorTower l E L ι X) at hX
    change scalarTensorTowerNormalization l E L ι Y (scalarTensorTower l E L ι Y) at hY
    dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    rw [hX, hY]
    with_unfolding_all exact finiteSquare l E g D hD T hT L ι D' hD' T' hT' S hcore A B n
  exact hd

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionDescentData

/-! # Completed tensor square for scalar/reindexing transitions

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-tensor-representative-square).
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
  integralOperationsTensorTowerFunctor scalarTensorChain scalarTensorOrdinary
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

private theorem exactSquareFactors
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (I : C ⥤ D) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso H I).symm).hom.app
        (DerivedCategory.Q.obj K)) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fac F G K
  have hi₁ : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (.up ℤ)).hom.app K = 𝟙 _ := rfl
  erw [hi₁, DerivedCategory.Q.map_id, Category.comp_id] at h₁
  have h₂ := Functor.mapDerivedCategoryCompIso_fac H I K
  have hi₂ : (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I))
      (.up ℤ)).hom.app K = 𝟙 _ := rfl
  erw [hi₂, DerivedCategory.Q.map_id, Category.comp_id] at h₂
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    (DerivedCategory.Q.obj K))).1
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [h₂, Functor.mapDerivedCategoryNatIso_fac, ← h₁]
  simp only [NatIso.mapHomologicalComplex]
  repeat' erw [Category.assoc]

/-- A representative step of the scalar/reindexing tensor descent.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 05RU, 0941
(blueprint: lem-pod-tensor-representative-square).
Proof: Apply the exact-derived composition and natural-isomorphism factor equations separately in
    both variables. Product extensionality gives the square. -/
theorem podTensorCoefficientRepresentativeSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι X).map
        ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
      (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
        ((podGoodReindex l E g D).obj P).obj ≫
      DerivedCategory.Q.map ((S.complex l E g L ι D D').hom.app P.obj) =
    (S.derived l E L ι g D D').hom.app (DerivedCategory.Q.obj P.obj) ≫
      (podOrdinaryReindex l L g).map
        ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
      (isoReductionIntegralInverse l L g).mapDerivedCategoryFactors.hom.app
        ((podTensorScalarGoodFunctor l E L ι Y).obj P).obj := by
  dsimp only [PodReindexCoefficientTransition.derived, PodReindexCoefficientTransition.complex,
    podTensorScalarGoodFunctor, podGoodReindex, ObjectProperty.lift, Functor.comp_obj,
    ObjectProperty.ι_obj, isoReductionIntegralComplex,
    podOrdinaryReindex, integralOrdinaryDerivedScalar]
  exact (exactSquareFactors (isoReductionIntegralInverse l E g)
    (integralOrdinaryScalar l E L ι X) (integralOrdinaryScalar l E L ι Y)
    (isoReductionIntegralInverse l L g) S.ordinary P.obj).symm

end WeilConjectures

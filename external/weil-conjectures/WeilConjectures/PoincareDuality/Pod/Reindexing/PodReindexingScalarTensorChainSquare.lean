/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition

/-! # Scalar/reindexing maps before derived localization

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: def-pod-reindexing-tensor-chain-maps).
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

attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  podGoodReindex integralOperationsRoosFunctor

attribute [local irreducible] integralOperationsTensorTowerFunctor scalarTensorChain
  integralOrdinaryScalar
  completedIntegralCoefficientSheafUnrestricted integralOperationsRoos

/-- The actual relabelling map on Roos tensor complexes, before localization.
Source: Stacks 07A4, 0941
(blueprint: def-pod-reindexing-tensor-chain-maps). -/
def podReindexTensorChain
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (isoReductionIntegralComplex l E g).obj
        ((integralOperationsTensorComplexFunctor l E Y).obj (P.obj, Q.obj)) ⟶
      (integralOperationsTensorComplexFunctor l E X).obj
        (((podGoodReindex l E g D).obj P).obj, ((podGoodReindex l E g D).obj Q).obj) :=
  (D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom ≫
    integralOperationsRoosFunctor.map (T.tower P Q).hom

/-- Apply the fixed ordinary coefficient transition term by term.
Source: Stacks 015F
(blueprint: def-pod-reindexing-tensor-chain-maps). -/
def PodReindexCoefficientTransition.complex
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D : PodCompletionReindex l E g) (D' : PodCompletionReindex l L g)
    (S : PodReindexCoefficientTransition l E L ι g D D') :
    isoReductionIntegralComplex l E g ⋙
        (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ) ≅
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ) ⋙
        isoReductionIntegralComplex l L g := by
  haveI : (isoReductionIntegralInverse l E g).Additive :=
    @isoSectionwiseModuleInverseImage_additive.{u, u} X Y g inferInstance _ _
      (isoReductionCompletedMap l E g).hom (isoReductionCompletedMap l E g).isIso_hom
  haveI : (isoReductionIntegralInverse l L g).Additive :=
    @isoSectionwiseModuleInverseImage_additive.{u, u} X Y g inferInstance _ _
      (isoReductionCompletedMap l L g).hom (isoReductionCompletedMap l L g).isIso_hom
  haveI : (integralOrdinaryScalar l E L ι X).Additive :=
    integralOrdinaryScalar_additive l E L ι X
  haveI : (integralOrdinaryScalar l E L ι Y).Additive :=
    integralOrdinaryScalar_additive l E L ι Y
  exact NatIso.mapHomologicalComplex S.ordinary (.up ℤ)

end WeilConjectures

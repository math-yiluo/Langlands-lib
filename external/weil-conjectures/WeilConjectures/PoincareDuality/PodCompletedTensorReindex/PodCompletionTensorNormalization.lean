/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels

/-! # Normalized completed tensor reindexing models

Source: blueprint theorem-poincare-duality-frobenius--2 Steps 1 and 5;
Stacks 07A4, 0941 (blueprint: def-pod-completion-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

attribute [local irreducible] integralCompletedTensor sfIntegralConstructible
  podReindexCalculus podOrdinaryToCompleted

namespace PodCompletedTensorReindex
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)

/-- The comparison is the localization of the same two-coordinate Roos chain map.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-tensor-normalization). -/
def Model : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)),
    HEq ((podOrdinaryReindex l E g).map ((integralCompletedTensorComparison l E Y).hom.app (P,Q)) ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj))).hom ≫
            integralOperationsRoosFunctor.map (T.tower P Q).hom))
      ((T.tensor (⟨DerivedCategory.Q.obj P.obj,hP⟩ : sfIntegralConstructibleCategory l E Y)
        (⟨DerivedCategory.Q.obj Q.obj,hQ⟩ : sfIntegralConstructibleCategory l E Y)).hom ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
        (integralCompletedTensorComparison l E X).hom.app
          ((podGoodReindex l E g D).obj P,(podGoodReindex l E g D).obj Q))

/-- Equality with the actual completed pullback/tensor comparison after the specified
  ordinary-to-completed pullback identification.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-tensor-normalization). -/
def Canonical : Prop :=
  ∀ M N : sfIntegralConstructibleCategory l E Y,
    (podOrdinaryToCompleted l E g D).app ((integralCompletedTensor l E Y).obj (M.obj,N.obj)) ≫
        ((canonicalIntegralPullbackTensor l E g M N).hom).hom =
      (T.tensor M N).hom ≫ (integralCompletedTensor l E X).map
        (Prod.mkHom ((podOrdinaryToCompleted l E g D).app M.obj)
          ((podOrdinaryToCompleted l E g D).app N.obj))

/-- Normalization of completed tensor, retaining the actual canonical arrow.
Source: blueprint Steps 1 and 5; Stacks 03EL, 07A4, 0941
(blueprint: def-pod-completion-tensor-normalization). -/
def Laws : Prop :=
  Generators l E g D T ∧
  InverseGenerators l E g D T ∧
  TowerNaturality l E g D T ∧
  Naturality l E g D T ∧
  Model l E g D T ∧
  Canonical l E g D T

end PodCompletedTensorReindex

end WeilConjectures

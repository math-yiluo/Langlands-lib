/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRoosRepresentativeSquareAux

/-! # One strict tensor tower and its canonical completed representative square

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-tensor-roos-representative-square).
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

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] integralCompletedTensor sfIntegralConstructible
  podReindexCalculus podOrdinaryToCompleted

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical completed comparison is the realization of one normalized strict
finite tensor tower arrow, before comparison with any chosen derived tensor family.

Source: blueprint theorem-poincare-duality-frobenius--2 Steps 1 and 5; Stacks 07A4
and 0941 (blueprint: lem-pod-tensor-roos-representative-square).

Proof: on each quotient, the generator formula identifies τ with the balanced
pullback/tensor comparison conjugated by D.quotient for P and Q. Sheafified pure
tensor extensionality and coproduct extensionality give equality of the chain maps.
Because τ is a morphism of entire towers, these equalities respect every transition.
D.RoosFst and D.RoosSnd then identify the two coordinates of its realization.
Localize this equality and apply D.FiniteModel and D.LimitModel to the coherent
reduction system. Use pullbackTensorIntegralTensorNormalization to replace each
completed-tensor representative by its specified coherent tensor/Roos model.
In these coordinates pullbackTensorReferenceComparison is the limit of pullback
of the tensor counit, followed by the system tensor comparison, followed by the
tensor of the two inverse input counits. D.Unit and D.Counit transport these actual
whole-system maps; their adjunction identities cancel the input counits. This gives
the canonical completed tensor arrow. D.PullbackNormalization
fixes its ordinary-to-completed comparison. Transport the two input representatives
back along mapDerivedCategoryFactors; the resulting equality is the displayed
square. This calculation uses only one pair of representatives and one tower map,
and makes no assertion about an independently chosen derived tensor family.
Zero representatives and the empty scheme give the same zero-map identities.
-/
theorem podTensorRoosRepresentativeSquare
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj))
    (τ : (podReindexTower l E g).obj
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
      (integralOperationsTensorTowerFunctor l E X).obj
        (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj))
    (hgen : ∀ (n : ℕ) (p q : ℤ) (U : X.ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      ((((τ.hom.app (op n)).f (p + q)).val.app (op U)))
          (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
            (op ((proEtaleIsoPostcompose g).obj U)) x y) =
        integralOperationsTotalTensorSection l E X n
          (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
          p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
            ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    ((podOrdinaryReindex l E g).map
          ((integralCompletedTensorComparison l E Y).hom.app (P,Q)) ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj))).hom ≫
            integralOperationsRoosFunctor.map τ.hom)) ≫
      (integralCompletedTensorComparison l E X).inv.app
        ((podGoodReindex l E g D).obj P,(podGoodReindex l E g D).obj Q) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.inv.app P.obj)
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.inv.app Q.obj)) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom
          ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
          ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj))) =
    (podOrdinaryToCompleted l E g D).app
        ((integralCompletedTensor l E Y).obj
          (DerivedCategory.Q.obj P.obj,DerivedCategory.Q.obj Q.obj)) ≫
      ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom := by
  exact podTensorRoosRepresentativeSquare_of_normalization l E g D hD P Q hP hQ τ hgen

end WeilConjectures

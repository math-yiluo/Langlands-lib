/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.CategoryTheory.SmoothPurity.FunctorSquareRepresentativeDescent
import WeilConjectures.SmoothPurity.Integral.IntegralTensorRepresentativeReassociate

/-! # Descent of an integral scalar tensor representative isomorphism

Source: Stacks 07A4 and 0941; categories.tex, Tag 04VK.
(blueprint: lem-pur-integral-scalar-tensor-representative-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOperationsTensorTowerFunctor
  integralOperationsTensorComplexFunctor scalarTensorChain integralCompletedTensor
  integralOperationsRoosFunctor DerivedCategory.Q integralOperationsGoodComplex
attribute [local semireducible] integralOperationsTensorComplexFunctor
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor

variable (W : AlgebraicGeometry.Scheme.{u})
local notation "I" => ObjectProperty.ι (integralOperationsGoodComplex l E W)
local notation "q" => integralOperationsGoodLocalization l E W
local notation "V" => MorphismProperty.inverseImage
  (HomologicalComplex.quasiIso (integralTowerModules l E W) (ComplexShape.up ℤ)) I
local notation "F" => integralOrdinaryDerivedScalar l E L ι W
local notation "S" => Functor.mapHomologicalComplex
  (integralOrdinaryScalar l E L ι W) (ComplexShape.up ℤ)
local notation "k" => ObjectProperty.lift (integralOperationsGoodComplex l L W) (I ⋙ S)
  (fun P ↦ scalarGood l E L ι W P)
local notation "p" => integralOperationsGoodLocalization l L W
local notation "t" => Functor.prod I I ⋙ integralOperationsTensorComplexFunctor l E W
local notation "s" => Functor.prod (ObjectProperty.ι (integralOperationsGoodComplex l L W))
  (ObjectProperty.ι (integralOperationsGoodComplex l L W)) ⋙
    integralOperationsTensorComplexFunctor l L W

private def scalarTensorCoefficientComparison :
    (Functor.prod q q) ⋙ (Functor.prod F F) ≅ (Functor.prod k k) ⋙ (Functor.prod p p) :=
  NatIso.prod
    (Functor.isoWhiskerLeft I (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors)
    (Functor.isoWhiskerLeft I (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors)

private theorem scalarTensorCoefficientComparison_app (P) :
    (scalarTensorCoefficientComparison l E L ι W).hom.app P =
      CategoryTheory.Prod.mkHom
        ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.1.obj)
        ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.2.obj) := rfl

/-- The normalized tensor comparison descends uniquely from good representatives.
Source: Stacks 07A4 and 0941; categories.tex, Tag 04VK.
(blueprint: lem-pur-integral-scalar-tensor-representative-descent).
Proof: take a natural isomorphism on the good tensor representatives. The two normalized
tensor representative comparisons and the exact scalar representative comparison
form the source and target sides of a functor square. The product good-complex
localization makes restriction fully faithful, so functorSquareRepresentativeDescent
lifts that square uniquely. Its defining component equation is exactly the
specified Roos normalization. No new comparison map or theorem hole is chosen. -/
theorem integralScalarTensorRepresentativeDescent
    (eδ : t ⋙ S ⋙ DerivedCategory.Q ≅ (Functor.prod k k) ⋙ s ⋙ DerivedCategory.Q) :
    ∃! α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W,
      ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          eδ.hom.app (P, Q) =
        α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l L W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l L W).hom.app
            (⟨_, scalarGood l E L ι W P⟩, ⟨_, scalarGood l E L ι W Q⟩) := by
  let : Functor.IsLocalization q V := integralOperationsGoodLocalization_isLocalization l E W
  obtain ⟨α, hα, huniq⟩ := functorSquareRepresentativeDescent
    (Functor.prod q q) (Functor.prod p p) (Functor.prod k k) t s _ _
    (integralCompletedTensor l E W) (integralCompletedTensor l L W) S F (Functor.prod F F)
    (Localization.fullyFaithfulWhiskeringLeft (Functor.prod q q) (MorphismProperty.prod V V)
      (DerivedCategory (integralTowerModules l L W)))
    (integralTensorRepresentativeReassociate l E W) (integralTensorRepresentativeReassociate l L W)
    (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors
    (scalarTensorCoefficientComparison l E L ι W) eδ
  refine ⟨α, ?_, ?_⟩
  · intro P Q
    simpa only [integralTensorRepresentativeReassociate_app,
      scalarTensorCoefficientComparison_app,
      integralOperationsGoodLocalization, ObjectProperty.lift,
      Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj,
      NatIso.prod, NatTrans.prod, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
      using hα (P, Q)
  · intro β hβ
    apply huniq β
    intro P
    simpa only [integralTensorRepresentativeReassociate_app,
      scalarTensorCoefficientComparison_app,
      integralOperationsGoodLocalization, ObjectProperty.lift,
      Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj,
      NatIso.prod, NatTrans.prod, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
      using hβ P.1 P.2

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackChainProperties

/-! # Scalar pullback comparison on good representatives

Source: Stacks 07A4 and 0941; categories.tex, Tag 04VK.
(blueprint: lem-pur-integral-scalar-pullback-good-comparison).
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

attribute [local irreducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackComplexFunctor scalarPullbackChain
  integralOperationsRoosFunctor DerivedCategory.Q integralOperationsGoodComplex
attribute [local semireducible] integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor
attribute [local implicit_reducible] integralOperationsPullbackOnGood
  integralOperationsGoodLocalization integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
local notation "I" => ObjectProperty.ι (integralOperationsGoodComplex l E Y)
local notation "S" => Functor.mapHomologicalComplex
  (integralOrdinaryScalar l E L ι Y) (ComplexShape.up ℤ)
local notation "SX" => Functor.mapHomologicalComplex
  (integralOrdinaryScalar l E L ι X) (ComplexShape.up ℤ)
local notation "k" => ObjectProperty.lift (integralOperationsGoodComplex l L Y) (I ⋙ S)
  (fun P ↦ scalarGood l E L ι Y P)
local notation "t" => I ⋙ integralOperationsPullbackComplexFunctor l E f
local notation "s" => ObjectProperty.ι (integralOperationsGoodComplex l L Y) ⋙
  integralOperationsPullbackComplexFunctor l L f

/-- The localized pullback chain maps form a uniquely normalized natural isomorphism.
Source: Stacks 07A4, 0941 and 099N.
(blueprint: lem-pur-integral-scalar-pullback-good-comparison).
Proof: each Q-image of the prescribed chain map is invertible by the existing
pullback chain quasi-isomorphism theorem on good inputs. Naturality of that chain
map, followed by functoriality of Q, assembles these components into a natural
isomorphism. Its components are the prescribed Q-images by asIso_hom. Two such
isomorphisms agree on every hom component, so natural transformation extensionality
and isomorphism extensionality prove uniqueness. -/
theorem integralScalarPullbackGoodComparison :
    ∃! c : t ⋙ SX ⋙ DerivedCategory.Q ≅ k ⋙ s ⋙ DerivedCategory.Q,
      ∀ P, c.hom.app P = DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) := by
  apply existsUnique_of_exists_of_unique
  · let eδ : t ⋙ SX ⋙ DerivedCategory.Q ≅ k ⋙ s ⋙ DerivedCategory.Q :=
      NatIso.ofComponents (fun P ↦ by
        let := scalarPullbackChainQuasiIso l E L ι f P
        exact asIso (DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj)))
        (by
          intro P Q a
          simpa only [Functor.comp_map, Functor.map_comp, asIso_hom,
            ObjectProperty.ι_map, integralOperationsPullbackOnGood,
            ObjectProperty.lift, ObjectProperty.homMk_hom, Functor.comp_obj,
            ObjectProperty.ι_obj] using
            congrArg (fun z ↦ DerivedCategory.Q.map z)
              (scalarPullbackChain_naturality l E L ι f a.hom))
    refine ⟨eδ, ?_⟩
    intro P
    rfl
  · intro α β hα hβ
    apply Iso.ext
    apply NatTrans.ext
    funext P
    exact (hα P).trans (hβ P).symm

private def pullbackGoodIso :=
  (integralScalarPullbackGoodComparison l E L ι f).exists.choose

private theorem pullbackGoodIso_hom_app
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (pullbackGoodIso l E L ι f).hom.app P =
      DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) :=
  (integralScalarPullbackGoodComparison l E L ι f).exists.choose_spec P

end WeilConjectures

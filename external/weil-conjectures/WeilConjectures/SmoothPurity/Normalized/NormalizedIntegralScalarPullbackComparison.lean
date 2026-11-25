/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackGoodComparison
import WeilConjectures.CategoryTheory.SmoothPurity.FunctorSquareRepresentativeDescent
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Normalized scalar pullback comparison by localization

Source: Stacks 07A4, 0941, 099N.
(blueprint: lem-pur-normalized-integral-scalar-pullback-comparison).
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
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

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

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
attribute [local irreducible] constantSheaf limit
  integralDerivedPullback integralCompletedTensor integralScalarExtension

section ScalarPullbackOrdinaryDescent

attribute [local semireducible] integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor
attribute [local implicit_reducible] integralOperationsPullbackOnGood
  integralOperationsGoodLocalization integralOperationsPullbackComplexFunctor
  integralOperationsPullbackTowerFunctor

/-- The ordinary scalar/pullback comparison is the localization of scalarPullbackChain.
Source: Stacks 07A4, 099N (blueprint: lem-pur-normalized-integral-scalar-pullback-comparison).
Proof: the prescribed level generator maps are natural and commute with strict
reductions. The two Roos coordinates therefore give scalarPullbackChain. Finite
freeness commutes with countable products; cofinality of uniformizer filtrations
makes this chain map a quasi-isomorphism on good representatives. Localize the
map, conjugating by the two displayed representative comparisons. Good K-flat
resolutions compute all objects and roofs, giving naturality and invertibility.
The same localization property gives uniqueness with this normalization. -/
theorem normalizedIntegralScalarPullbackComparison {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f,
      scalarPullbackOrdinaryNormalization l E L ι f α := by
  let I := (integralOperationsGoodComplex l E Y).ι
  let q := integralOperationsGoodLocalization l E Y
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage I
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E Y
  let F := integralOrdinaryDerivedScalar l E L ι X
  let G := integralOrdinaryDerivedScalar l E L ι Y
  let S := (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)
  let SX := (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)
  let k := (integralOperationsGoodComplex l L Y).lift (I ⋙ S)
    (fun P ↦ scalarGood l E L ι Y P)
  let p := integralOperationsGoodLocalization l L Y
  let t := I ⋙ integralOperationsPullbackComplexFunctor l E f
  let s := (integralOperationsGoodComplex l L Y).ι ⋙
    integralOperationsPullbackComplexFunctor l L f
  let eδ : t ⋙ SX ⋙ DerivedCategory.Q ≅ k ⋙ s ⋙ DerivedCategory.Q :=
    pullbackGoodIso l E L ι f
  let r : q ⋙ integralDerivedPullback l E f ≅ t ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ (integralDerivedPullbackComparison l E f).app P)
      (by
        intro P Q a
        simpa only [Functor.comp_map, integralOperationsPullbackOnGood, t, I,
          ObjectProperty.ι_map, Iso.app_hom] using
          (integralDerivedPullbackComparison l E f).hom.naturality a)
  let r' : p ⋙ integralDerivedPullback l L f ≅ s ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ (integralDerivedPullbackComparison l L f).app P)
      (by
        intro P Q a
        simpa only [Functor.comp_map, integralOperationsPullbackOnGood, s,
          ObjectProperty.ι_map, Iso.app_hom] using
          (integralDerivedPullbackComparison l L f).hom.naturality a)
  let η : q ⋙ G ≅ k ⋙ p :=
    NatIso.ofComponents
      (fun P ↦ (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.app P.obj)
      (by
        intro P Q a
        simpa only [Functor.comp_map, I, q, p, G, S,
          integralOperationsGoodLocalization, k, ObjectProperty.lift,
          ObjectProperty.ι_map, ObjectProperty.homMk_hom, Iso.app_hom,
          Functor.comp_obj, ObjectProperty.ι_obj] using
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.naturality a.hom)
  change ∃! α : integralDerivedPullback l E f ⋙ F ≅ G ⋙ integralDerivedPullback l L f,
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      F.map (r.hom.app P) ≫
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app (t.obj P) ≫
          DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) =
        α.hom.app (q.obj P) ≫ (integralDerivedPullback l L f).map (η.hom.app P) ≫
          r'.hom.app (k.obj P)
  simpa only [eδ, pullbackGoodIso_hom_app] using
    functorSquareRepresentativeDescent q p k t s _ _
      (integralDerivedPullback l E f) (integralDerivedPullback l L f) SX F G
      (Localization.fullyFaithfulWhiskeringLeft q V
        (DerivedCategory (integralTowerModules l L X)))
      r r' (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors η eδ

end ScalarPullbackOrdinaryDescent

end WeilConjectures

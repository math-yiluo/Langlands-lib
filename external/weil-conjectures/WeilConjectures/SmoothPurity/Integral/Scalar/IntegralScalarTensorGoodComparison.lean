/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorChainQuasiIso
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorChainNaturality

/-! # Scalar tensor comparison on good representatives

Source: Stacks 07A4 and 0941; categories.tex, Tag 04VK.
(blueprint: lem-pur-integral-scalar-tensor-good-comparison).
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
local notation "S" => Functor.mapHomologicalComplex
  (integralOrdinaryScalar l E L ι W) (ComplexShape.up ℤ)
local notation "k" => ObjectProperty.lift (integralOperationsGoodComplex l L W) (I ⋙ S)
  (fun P ↦ scalarGood l E L ι W P)
local notation "t" => Functor.prod I I ⋙ integralOperationsTensorComplexFunctor l E W
local notation "s" => Functor.prod (ObjectProperty.ι (integralOperationsGoodComplex l L W))
  (ObjectProperty.ι (integralOperationsGoodComplex l L W)) ⋙
    integralOperationsTensorComplexFunctor l L W

/-- The Q-images of the specified scalar tensor chain maps form a natural isomorphism.
Source: Stacks 07A4, 0941 and 08TC.
(blueprint: lem-pur-integral-scalar-tensor-good-comparison).
Proof: each component is invertible by scalarTensorChainQuasiIso. Naturality is
scalarTensorChain_naturality mapped by Q, so NatIso.ofComponents assembles the
components. Its component equation follows from the definition of asIso. -/
theorem integralScalarTensorGoodComparison :
    ∃! c : t ⋙ S ⋙ DerivedCategory.Q ≅ (Functor.prod k k) ⋙ s ⋙ DerivedCategory.Q,
      ∀ P, c.hom.app P =
        DerivedCategory.Q.map (scalarTensorChain l E L ι W P.1.obj P.2.obj) := by
  apply existsUnique_of_exists_of_unique
  · let eδ : t ⋙ S ⋙ DerivedCategory.Q ≅ (Functor.prod k k) ⋙ s ⋙ DerivedCategory.Q :=
      NatIso.ofComponents (fun P ↦ by
        let := scalarTensorChainQuasiIso l E L ι W P.1 P.2
        exact asIso (DerivedCategory.Q.map
          (scalarTensorChain l E L ι W P.1.obj P.2.obj))) (by
        intro P Q a
        simpa only [Functor.comp_map, Functor.map_comp, asIso_hom,
          ObjectProperty.ι_map, integralOperationsTensorOnGood, ObjectProperty.lift,
          ObjectProperty.homMk_hom, Functor.comp_obj, ObjectProperty.ι_obj,
          Functor.prod_obj, Functor.prod_map] using
          congrArg (fun z ↦ DerivedCategory.Q.map z)
            (scalarTensorChain_naturality l E L ι W (CategoryTheory.Prod.mkHom a.1.hom a.2.hom)))
    refine ⟨eδ, ?_⟩
    intro P
    rfl
  · intro α β hα hβ
    apply Iso.ext
    apply NatTrans.ext
    funext P
    exact (hα P).trans (hβ P).symm

end WeilConjectures

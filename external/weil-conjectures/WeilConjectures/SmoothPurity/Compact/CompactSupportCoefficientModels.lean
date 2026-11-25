/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantPresentationTransport
public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerAdjunction
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.SmoothPurity.Pur.PurAdicScalarExtensionTorBound
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import all WeilConjectures.CategoryTheory.Site.SiteDerivedTensorRestriction
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientModelsOrdinaryExistence
import all WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientModelHelpers

/-! # Compatible coefficient models for integral compact support

Source: Bhatt--Scholze, Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1);
Weil blueprint, purity transport, coefficient extension step
(blueprint: lem-pur-compact-support-coefficient-models).

The arithmetic basis is fixed before passing to quotients. The scalar comparisons
are the published normalized comparisons, and the arbitrary ramified quotient is
handled by derived tensor balancing rather than a flatness assumption.
The native associator and unit clause is not restated: it is the proved
`RingedDerivedNative.associator_square`, `leftUnitor_square` and `rightUnitor_square`
of the cited node lem-sf-ringed-derived-native-tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] WeilConjectures.completedScalarComparison
  WeilConjectures.completedScalarChainComparison
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.completedAdicChangeData
attribute [local irreducible] CochainComplex.mapBifunctorSingle₂Iso
  CochainComplex.mapBifunctorSingle₁Iso
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped BigOperators
namespace WeilConjectures
open ConstantCompletion

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

-- The universe-polymorphic site-size instance gets stuck on the coefficient universe.
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall in
/-- In the constant model completed scalar extension is ordinary tensor with B.
Its normalization uses every local scalar, and is independent of the chosen basis.
Source: Stacks 03EK, 099L; Bhatt--Scholze 6.8.2(1)
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: a single integral basis identifies B with A^r and its completion with the
r-fold completed module. The scalar-inclusion square makes the tensor map balanced.
Map `b tensor x` to `completion(b) tensor x`; the coordinate identification proves it
invertible. Local tensor generators prove uniqueness. Exactness and the K-flat
computation counits transport this ordinary identification to derived complete objects. -/
theorem compactSupportCoefficientModels_ordinary (W : Scheme.{u}) :
    ∃! β : PurStrictScalar.constantRestriction l E W ⋙
        pbcExtend (PurStrictScalar.constantMap l E F i W) ≅
      pbcExtend (completedCoefficientMap l E F i W) ⋙
        PurStrictScalar.constantRestriction l F W,
      ∀ (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
        (b : ((PurStrictScalar.constants l F).ring W).obj.obj U) (x : M.val.obj U),
        (β.hom.app M).val.app U
            (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
              ((PurStrictScalar.constantRestriction l E W).obj M) U b x) =
          pbcTensorSection (completedCoefficientMap l E F i W) M U
            (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  classical
  choose β hβ using compactSupportCoefficientModels_ordinary_exists l E F i W
  let γ : PurStrictScalar.constantRestriction l E W ⋙
      pbcExtend (PurStrictScalar.constantMap l E F i W) ≅
      pbcExtend (completedCoefficientMap l E F i W) ⋙
        PurStrictScalar.constantRestriction l F W :=
    NatIso.ofComponents β (by
      intro M N f
      let h := (pbcExtensionExistence
        (PurStrictScalar.constantMap l E F i W)).choose_spec.choose
          ((PurStrictScalar.constantRestriction l E W).obj M)
      apply (cancel_epi (eqToHom h.symm)).mp
      apply SheafOfModules.tensor_generator_ext.{u + 1, u, u + 1}
        (PurStrictScalar.constantMap l E F i W)
      intro U x b
      change (β N).hom.val.app U
          (((pbcExtend (PurStrictScalar.constantMap l E F i W)).map
            ((PurStrictScalar.constantRestriction l E W).map f)).val.app U
              (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
                ((PurStrictScalar.constantRestriction l E W).obj M) U b x)) =
        ((pbcExtend (completedCoefficientMap l E F i W)).map f).val.app U
          ((β M).hom.val.app U
            (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
              ((PurStrictScalar.constantRestriction l E W).obj M) U b x))
      let c := ((integralConstantToCompletionOfUniverses l F W).hom.app U) b
      exact (congrArg ((β N).hom.val.app U)
        (coefficientExtensionTensor_naturality W
          (PurStrictScalar.constantMap l E F i W)
          ((PurStrictScalar.constantRestriction l E W).map f) U b x)).trans
        ((hβ N U b (f.val.app U x)).trans
          ((coefficientExtensionTensor_naturality W
            (completedCoefficientMap l E F i W) f U c x).symm.trans
            (congrArg
              (((pbcExtend (completedCoefficientMap l E F i W)).map f).val.app U)
              (hβ M U b x).symm))))
  refine ⟨γ, hβ, ?_⟩
  intro β' hβ'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let h : (pbcExtend (PurStrictScalar.constantMap l E F i W)).obj
      ((PurStrictScalar.constantRestriction l E W).obj M) =
      SheafOfModules.changeOfRings (PurStrictScalar.constantMap l E F i W)
        ((PurStrictScalar.constantRestriction l E W).obj M) :=
    (pbcExtensionExistence (PurStrictScalar.constantMap l E F i W)).choose_spec.choose _
  apply (cancel_epi (eqToHom h.symm)).mp
  apply SheafOfModules.tensor_generator_ext.{u + 1, u, u + 1}
    (PurStrictScalar.constantMap l E F i W)
  intro U x b
  change (β'.hom.app M).val.app U
      (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
        ((PurStrictScalar.constantRestriction l E W).obj M) U b x) =
    (γ.hom.app M).val.app U
      (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
        ((PurStrictScalar.constantRestriction l E W).obj M) U b x)
  exact (hβ' M U b x).trans (hβ M U b x).symm

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionIdeal Padic.coefficientExtensionUniformizer
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] reductionChange reductionDerivedChange
  completedCoefficientMap

attribute [local semireducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionIdeal Padic.coefficientExtensionUniformizer
attribute [local semireducible] reductionChange reductionDerivedChange
  completedAdicChangeData completedCoefficientMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] sfQcqsCompactSupportRealizationMap
  sfQcqsCompactSupportRealization

end WeilConjectures

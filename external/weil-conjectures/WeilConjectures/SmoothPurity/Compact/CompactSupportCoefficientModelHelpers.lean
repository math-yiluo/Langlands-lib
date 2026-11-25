/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.CategoryTheory.Site.SiteDerivedTensorRestriction
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Quotient

set_option linter.privateModule false

/-! # Coefficient-model balancing and proof helpers

Source: Bhatt--Scholze, Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1);
Weil blueprint, purity transport, coefficient extension step
(blueprint: lem-pur-compact-support-coefficient-models).

The proved balancing comparison and its private helpers are split out to keep
each consumer compile below 60 seconds.
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
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped BigOperators
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

private theorem coefficientExtensionTensor_naturality
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    [HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1}]
    [(ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (φ : R ⟶ S) {M N : pbcModules W R} (f : M ⟶ N)
    (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((pbcExtend φ).map f).val.app U (pbcTensorSection φ M U s x) =
      pbcTensorSection φ N U s (f.val.app U x) := by
  exact witnessTensor_naturality φ (pbcExtend φ)
    (pbcExtensionExistence φ).choose_spec.choose
    (pbcExtensionExistence φ).choose_spec.choose_spec.choose f U s x

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionIdeal Padic.coefficientExtensionUniformizer
open CategoryTheory.MonoidalCategory


end WeilConjectures

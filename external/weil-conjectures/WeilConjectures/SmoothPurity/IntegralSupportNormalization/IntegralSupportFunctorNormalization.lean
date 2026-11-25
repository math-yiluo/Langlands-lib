/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.SmoothPurity.IntegralImmersionNormalization.IntegralImmersionPullbackNormalization
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.Sf.SfIntegralOrdinaryRecollementRealization
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

public import WeilConjectures.DeligneLaumon.IntegralSupportNormalization.IntegralSupportNormalizationData
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralOpenSupportNormalization
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralClosedSupportNormalization
import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.ZetaSeries

/-! # Assembly of normalized integral support operations

Source: smooth-purity localization support paragraphs
(blueprint: lem-sf-integral-support-functor-normalization).
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

private theorem cancel_inverse {C : Type*} [Category C] {A B P T : C}
    (e : B ≅ T) (f : A ⟶ B) (g : A ⟶ P) (q : P ⟶ T)
    (h : f = g ≫ q ≫ e.inv) : f ≫ e.hom = g ≫ q := by
  rw [h]
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures.IntegralSupportNormalization

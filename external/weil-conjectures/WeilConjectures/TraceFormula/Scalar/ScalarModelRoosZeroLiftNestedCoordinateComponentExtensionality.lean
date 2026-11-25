/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Supporting.NestedChosenScalarTensorValExt

/-! # Nested scalar tensor component extensionality

Source: Stacks Project, Tag 0941; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-trf-scalar-model-roos-zero-lift-nested-coordinate-component-extensionality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralScalarExtensionOfUniverses completedDerivedScalarExtension completedScalarCounit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})

/-- Nested scalar tensor generators determine a single sheaf-module morphism.

Source: Stacks 0941; Bhatt--Scholze, Proposition 3.5.1.
Proof in words: apply the sheafification adjunction and module tensor universal
property first to the inner extension and then to the outer extension. Tensor
induction and separatedness identify the resulting morphisms on all sections.
(blueprint: lem-trf-scalar-model-roos-zero-lift-nested-coordinate-component-extensionality) -/
theorem completedNestedScalarTensor_ext
    (M : integralTowerModules l E X)
    (Q : integralTowerModules l F X)
    (f g : (completedOrdinaryScalarExtension l L F j X).obj
      ((completedOrdinaryScalarExtension l E L ι X).obj M) ⟶ Q)
    (h : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : M.val.obj U),
      f.val.app U (completedScalarTensorSection l L F j X
        ((completedOrdinaryScalarExtension l E L ι X).obj M) U s
        (completedScalarTensorSection l E L ι X M U t x)) =
      g.val.app U (completedScalarTensorSection l L F j X
        ((completedOrdinaryScalarExtension l E L ι X).obj M) U s
        (completedScalarTensorSection l E L ι X M U t x))) :
    f = g := by
  apply SheafOfModules.hom_ext
  exact nestedChosenScalarTensor_val_ext l E L F ι j X M Q f g h

end WeilConjectures

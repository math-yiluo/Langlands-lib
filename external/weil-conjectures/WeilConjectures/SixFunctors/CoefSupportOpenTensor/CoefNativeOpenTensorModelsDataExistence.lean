/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefOpenTensorEvaluationData
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.CoefNativeOpenTensorCochains
import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorProjectionDescent
import WeilConjectures.SixFunctors.IndependentTensorModel.ExactTensorModelConstructionIndependent
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension

/-! # Existence of native open tensor representative data

Source: Stacks 0E8I, 0GL1 and 07A4; support-open-tensor steps 5--6.
(blueprint: lem-coef-native-open-tensor-models-data-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

section Assembly
universe c v r
open WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{max c v r})
  (A : SemilinearSections.Closed.{c, v, r} J R) (T : SemilinearSections.Models.{c, v, r} J R A)

variable {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C') (R' : Sheaf J' CommRingCat.{max c v r})
  (A' : SemilinearSections.Closed.{c, v, r} J' R')
  (T' : SemilinearSections.Models.{c, v, r} J' R' A')
  (F : SemilinearSections.Mod.{c, v, max c v r} J' R' ⥤
    SemilinearSections.Mod.{c, v, max c v r} J R)
  (G : SemilinearSections.Mod.{c, v, max c v r} J R ⥤
    SemilinearSections.Mod.{c, v, max c v r} J' R')
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (adj : F ⊣ G)
  (H : C ⥤ C')
  (sectionPull : ∀ (N : SemilinearSections.Mod.{c, v, max c v r} J R) (V : Cᵒᵖ),
    N.val.obj V → (G.obj N).val.obj (H.op.obj V))

private theorem model_of_cochains
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull) :
    Nonempty (OpenTensorModel.{c, v, r} J R A T J' R' A' T' F G adj H sectionPull) := by
  obtain ⟨mu, restrictionModel, hordinary, _⟩ :=
    IndependentTensorModel.modelOfOrdinary.{c, v, r} J J' R R' G D.right D.pullAdjunction
      A A' T T' D.pullTensor D.pullNaturality D.pullKFlat
  let := SemilinearSections.abelianSheafify.{c, v, max c v r} J
  let := SemilinearSections.locallyBijective.{c, v, max c v r} J
  let := SemilinearSections.hasDerived.{c, v, max c v r} J R
  obtain ⟨ambient, hab, han⟩ := ringedTensorComparison_extension.{c, v, r, (max c v r) + 1} J R A T
  let := SemilinearSections.abelianSheafify.{c, v, max c v r} J'
  let := SemilinearSections.locallyBijective.{c, v, max c v r} J'
  let := SemilinearSections.hasDerived.{c, v, max c v r} J' R'
  obtain ⟨inside, hib, hin⟩ :=
    ringedTensorComparison_extension.{c, v, r, (max c v r) + 1} J' R' A' T'
  obtain ⟨gamma, hgamma, hmodel⟩ :=
    openTensorProjection_descent.{c, v, r} J R A T J' R' A' T' F G adj H sectionPull
      D mu restrictionModel hordinary ambient hab han inside hib hin
  refine ⟨{
    restriction := mu
    restrictionModel := restrictionModel
    restrictionPure := ?_
    ordinary := D.ordinary
    ordinary_inverse := ?_
    chain := D.chain
    summand := D.summand
    ambientModel := ambient
    ambientBoth := hab
    ambientNaturality := han
    openModel := inside
    openBoth := hib
    openNaturality := hin
    restrictionFlat := D.pullFlat
    gamma := gamma
    gamma_inverse := hgamma
    derived_model := hmodel }⟩
  · simpa only [hordinary] using D.pullPure
  · simpa only [hordinary] using D.ordinaryInverse

end Assembly

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

-- Keep the recorded existential binder names, whose witnesses do not occur in True.
set_option linter.unusedVariables false in
/-- The localized-site and finite coefficient constructions provide native system and
finite open tensor representative data. The construction uses the normalized open
adjunction, its restriction/tensor comparison, and total K-flat representatives.
Source: Stacks 0E8I, 0GL1 and 07A4; support-open-tensor proof steps 5--6.
(blueprint: lem-coef-native-open-tensor-models-data-existence).
-/
theorem nativeOpenTensorModels_data_exists {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z) :
    ∃ (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors)
      (On : ∀ n : ℕ, FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors n), True := by
  obtain ⟨D, Dn, _⟩ := nativeOpenTensor_cochains_exists l E j
  obtain ⟨O⟩ : Nonempty (SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors) :=
    @model_of_cochains.{u + 1, u, u} (ℕ × Z.ProEt) _
      (ProEtale.VaryingRing.sequenceSiteSmall Z)
      (coefficientSequenceTopology (ProEt.topology Z))
      (coefficientSequenceCommRingSheaf.{u, u} l E Z)
      SZ.systemClosed SZ.systemTensorModel
      (ℕ × X.ProEt) _ (ProEtale.VaryingRing.sequenceSiteSmall X)
      (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceCommRingSheaf.{u, u} l E X)
      SX.systemClosed SX.systemTensorModel
      (ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionAdditive (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionLimits (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionColimits (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullAdditive (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullLimits (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullColimits (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.baseChange j) (pullSection l E j) D
  have hn (n : ℕ) : Nonempty (FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors n) := by
    let := ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j
    let := ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j
    let := ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j
    let := proEtaleRingModulePullback_additive j
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
      (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
    let := proEtaleRingModulePullback_preservesFiniteLimits j
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
      (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
    let := proEtaleRingModulePullback_preservesFiniteColimits j
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
      (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
    exact model_of_cochains.{u + 1, u, u} _ _ _ _ _ _ _ _ _ _ _ _ _ (Dn n)
  exact ⟨O, fun n ↦ Classical.choice (hn n), trivial⟩

end WeilConjectures.CoefSupportOpenTensor

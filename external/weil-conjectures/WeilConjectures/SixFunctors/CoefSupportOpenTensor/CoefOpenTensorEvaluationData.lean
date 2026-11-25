/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefSupportOpenTensor.OpenTensorRepresentativeData
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus

/-! # Native quotient-system open tensor evaluation data

Source: blueprint main-20261015, prop-coef-integral-dualizing.proof.md paragraph 2,
compact-support/open-model subargument, steps 5--6; Stacks 0GL1, 07A4
(blueprint: def-coef-native-open-tensor-evaluation-data).

These are actual site specializations and a finite-evaluation predicate, with no
existence assertion. Every functor and comparison is the recorded native one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Specialized additive instance for the actual finite open functor.
Source: Stacks 03DI; strict-tower moduleJ_exact
(blueprint: def-coef-native-open-tensor-evaluation-data). -/
instance finiteOpenAdditive {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).Additive :=
  ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j

/-- Actual inverse-image section, given by the unit of the recorded module adjunction.
Source: Stacks 07A4; node proof step 5
(blueprint: def-coef-native-open-tensor-evaluation-data). -/
def pullSection {X Z : Scheme.{u}} (j : X ⟶ Z)
    (N : coefficientSequenceModules.{u, u} l E Z) (V : (ℕ × Z.ProEt)ᵒᵖ)
    (x : N.val.obj V) :
    ((ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j).obj N).val.obj
        ((ProEtale.VaryingRing.baseChange j).op.obj V) :=
  ((ProEtale.VaryingRing.moduleAdj (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) j).unit.app N).val.app V x

/-- Specialize the normalized open tensor model to the actual quotient sequence site.
Source: Stacks 0E8I, 0GL1; node proof steps 5--6
(blueprint: def-coef-native-open-tensor-evaluation-data). -/
abbrev SystemOpenModel {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemTensors.{u, u} l E X)
    (SZ : CoefficientDerivedSystemTensors.{u, u} l E Z) :=
  letI := ProEtale.VaryingRing.extensionAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  @OpenTensorModel.{u+1, u, u} (ℕ × Z.ProEt) _
    (ProEtale.VaryingRing.sequenceSiteSmall Z)
    (coefficientSequenceTopology (ProEt.topology Z)) (coefficientSequenceCommRingSheaf.{u, u} l E Z)
    SZ.systemClosed SZ.systemTensorModel
    (ℕ × X.ProEt) _ (ProEtale.VaryingRing.sequenceSiteSmall X)
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf.{u, u} l E X)
    SX.systemClosed SX.systemTensorModel
    (ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    _ _ _ _ _ _
    (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.baseChange j) (pullSection l E j)

/-- The system gamma with its exact native functor instances made explicit.
Source: Stacks 0GL1; node proof steps 5--6
(blueprint: def-coef-native-open-tensor-evaluation-data). -/
abbrev systemGamma {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemTensors.{u, u} l E X)
    (SZ : CoefficientDerivedSystemTensors.{u, u} l E Z)
    (O : SystemOpenModel l E j SX SZ) :=
  letI := ProEtale.VaryingRing.extensionAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  @OpenTensorModel.gamma.{u+1, u, u} (ℕ × Z.ProEt) _
    (ProEtale.VaryingRing.sequenceSiteSmall Z)
    (coefficientSequenceTopology (ProEt.topology Z)) (coefficientSequenceCommRingSheaf.{u, u} l E Z)
    SZ.systemClosed SZ.systemTensorModel
    (ℕ × X.ProEt) _ (ProEtale.VaryingRing.sequenceSiteSmall X)
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf.{u, u} l E X)
    SX.systemClosed SX.systemTensorModel
    (ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    _ _ _ _ _ _
    (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.baseChange j) (pullSection l E j) O

/-- Inverse-image sections at one finite coefficient ring, with the actual scalar unit.
Source: Stacks 07A4; node proof step 6
(blueprint: def-coef-native-open-tensor-evaluation-data). -/
def finitePullSection {X Z : Scheme.{u}} (j : X ⟶ Z) (n : ℕ)
    (N : normalizedDVRModules.{u, u} l E Z n) (V : Z.ProEtᵒᵖ)
    (x : N.val.obj V) :
    ((ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j).obj N).val.obj
      ((proEtaleBaseChange j).op.obj V) :=
  ((proEtaleRingModuleAdjunction j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso
      (compactSupportSystemLevel l E n) j)).unit.app N).val.app V x

/-- The identical normalized comparison over the constant finite ring A_(n+1).
Its ordinary and derived inverse-unit equations characterize the canonical finite
open tensor comparison of lem-sf-open-tensor-normalization.
Source: Stacks 0E8I, 0GL1; node proof step 6
(blueprint: def-coef-native-open-tensor-evaluation-data). -/
abbrev FiniteOpenModel {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemTensors.{u, u} l E X)
    (SZ : CoefficientDerivedSystemTensors.{u, u} l E Z) (n : ℕ) :=
  letI := ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j
  letI := proEtaleRingModulePullback_additive j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteLimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteColimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  @OpenTensorModel.{u+1, u, u} Z.ProEt _
    (WeilConjectures.instEssentiallySmallProEt_weilConjectures Z) (ProEt.topology Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (SZ.finiteClosed n) (SZ.finiteTensorModel n)
    X.ProEt _ (WeilConjectures.instEssentiallySmallProEt_weilConjectures X) (ProEt.topology X)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (SX.finiteClosed n) (SX.finiteTensorModel n)
    (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j)
    (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j)
    _ _ _ _ _ _
    (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)
    (proEtaleBaseChange j) (finitePullSection l E j n)

/-- The finite gamma with its exact native functor instances made explicit.
Source: Stacks 0GL1; node proof step 6
(blueprint: def-coef-native-open-tensor-evaluation-data). -/
abbrev finiteGamma {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemTensors.{u, u} l E X)
    (SZ : CoefficientDerivedSystemTensors.{u, u} l E Z) (n : ℕ)
    (O : FiniteOpenModel l E j SX SZ n) :=
  letI := ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j
  letI := proEtaleRingModulePullback_additive j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteLimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteColimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  @OpenTensorModel.gamma.{u+1, u, u} Z.ProEt _
    (WeilConjectures.instEssentiallySmallProEt_weilConjectures Z) (ProEt.topology Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (SZ.finiteClosed n) (SZ.finiteTensorModel n)
    X.ProEt _ (WeilConjectures.instEssentiallySmallProEt_weilConjectures X) (ProEt.topology X)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (SX.finiteClosed n) (SX.finiteTensorModel n)
    (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j)
    (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j)
    _ _ _ _ _ _
    (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)
    (proEtaleBaseChange j) (finitePullSection l E j n) O

/-- Exact finite evaluation of gamma under the actual open, restriction and tensor
comparisons. This is equality of the evaluated transformation with the canonical
finite transformation, on every pair of derived objects.
Source: Stacks 0GL1, 07A4; node proof step 6
(blueprint: def-coef-native-open-tensor-evaluation-data). -/
def GammaEvaluation {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z)
    (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors)
    (On : ∀ n : ℕ, FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors n) : Prop :=
  ∀ (n : ℕ) (U : coefficientSequenceDerived.{u, u} l E X)
    (L : coefficientSequenceDerived.{u, u} l E Z),
    (coefficientSequenceDerivedEvaluation.{u, u} l E Z n).map
        ((systemGamma l E j SX.toCoefficientDerivedSystemTensors
          SZ.toCoefficientDerivedSystemTensors O).hom.app (U, L)) ≫
      (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j n).hom.app
          (SX.systemClosed.tensor.obj (U,
            (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) j).obj L)) ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).mapDerivedCategory.map
        ((SX.evaluationTensor n).hom.app (U,
          (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j).obj L)) ≫
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j).mapDerivedCategory.map
        ((SX.finiteClosed n).tensor.map (Prod.mkHom (𝟙 _)
          ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) j n).hom.app L))) =
    (SZ.evaluationTensor n).hom.app
        ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj U, L) ≫
      (SZ.finiteClosed n).tensor.map (Prod.mkHom
        ((ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app U) (𝟙 _)) ≫
      (finiteGamma l E j SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors n (On n)).hom.app
          ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj U,
        (coefficientSequenceDerivedEvaluation.{u, u} l E Z n).obj L)

end WeilConjectures.CoefSupportOpenTensor

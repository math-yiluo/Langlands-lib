/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-!
# Strict reduction and normalized realization of integral open extension

Source: Stacks Project, Tags 0GL1 and 0E8I; blueprint `fix-prop-coherence`,
open-factor sentence (blueprint: lem-sf-integral-open-reduction-comparison).
The natural index n denotes exponent n+1. Site and coefficient sizes are independent.

## Main definitions

- `Coefficients`: constant-section and quotient-normalized transport to the actual open slice.
- `Operations`: the localized extension/restriction functors on modules and strict systems.
- `Comparison`: strict representative normalization and realized adjunction identities.

## Main statements

- `Comparison`: the specified strict comparison and its realization laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOpenReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Sheafification in the universe containing both sites and coefficients.
Source: Stacks 03DA (blueprint: lem-sf-integral-open-reduction-comparison). -/
instance openAbSheafify : HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t+1)} :=
  SemilinearSections.abelianSheafify.{t+1, t, max u (t+1)} (ProEt.topology X)

/-- The corresponding local sheafification criterion. Source: Stacks 03DA
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance openAbLocallyBijective :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t+1)} :=
  SemilinearSections.locallyBijective.{t+1, t, max u (t+1)} (ProEt.topology X)

/-- The actual open object, including the empty open. Source: Stacks 098K
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev openObject := cbcOpenObject j inferInstance

/-- The literal slice-to-open site functor. Source: Stacks 098K
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev sliceSite := cbcSliceFunctor X (openObject j)

/-- Continuity of the literal slice presentation. Source: Stacks 098K
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance sliceContinuous : (sliceSite j).IsContinuous
    ((ProEt.topology X).over (openObject j)) (ProEt.topology U) :=
  cbcSliceFunctor_continuous X (openObject j)

/-- The finite coefficient sheaves, with their recorded quotient transitions.
Source: Stacks 0941 (blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev rings (T : Scheme.{t}) := integralCoefficientCommRingSheaf l E T

/-- The actual strict quotient maps. Source: Stacks 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev transitions (T : Scheme.{t}) := coefficientSequenceCommRingTransition l E T

/-- The actual localized semilinear system category. Source: Stacks 03DJ, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev SliceSystems := SemilinearSections.Systems.{t+1, t, max u (t+1)}
  ((ProEt.topology X).over (openObject j))
  (fun n ↦ (rings l E X n).over (openObject j))
  (fun n ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
    (openObject j)).map (transitions l E X n))

/-- The actual slice coefficient system, not independent finite coefficient choices.
Source: Stacks 0941 (blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev sliceRing := SemilinearSections.systemRing.{t+1, t, max u (t+1)}
  ((ProEt.topology X).over (openObject j))
  (fun n ↦ (rings l E X n).over (openObject j))
  (fun n ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
    (openObject j)).map (transitions l E X n))

/-- Transport of completed and finite coefficients to the open's actual slice.
All finite maps are fixed by constant sections, the completed map by its quotient
projections, and each module equivalence by the concrete continuous pushforward.
Source: Stacks 098K, 03DI, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
structure Coefficients where
  finiteMap : ∀ n : ℕ, (rings l E X n).over (openObject j) ⟶
    ((sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t+1)}
      ((ProEt.topology X).over (openObject j)) (ProEt.topology U)).obj (rings l E U n)
  finiteConstants : ∀ (n : ℕ) (V : Over (openObject j)),
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1)))))).app
          (op V.left) ≫ (finiteMap n).hom.app (op V) =
    (toSheafify (ProEt.topology U)
      ((Functor.const U.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1)))))).app
          (op ((sliceSite j).obj V))
  completedMap : (completedIntegralCommRingSheafUnrestricted l E X).over (openObject j) ⟶
    ((sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t+1)}
      ((ProEt.topology X).over (openObject j)) (ProEt.topology U)).obj
        (completedIntegralCommRingSheafUnrestricted l E U)
  projections : ∀ n : ℕ, completedMap ≫
    ((sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t+1)}
      ((ProEt.topology X).over (openObject j)) (ProEt.topology U)).map
        (completedIntegralCommRingProjectionUnrestricted l E U n) =
    ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)} (openObject j)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n) ≫ finiteMap n
  integral : scalarReductionSource l E U ≌
    SheafOfModules.{max u (t+1)}
      ((completedIntegralCoefficientSheafUnrestricted l E X).over (openObject j))
  integralFunctor : integral.functor = SheafOfModules.pushforward.{max u (t+1)}
    (F := sliceSite j)
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
      completedMap)
  finite : ∀ n : ℕ, normalizedDVRModules l E U n ≌
    SheafOfModules.{max u (t+1)} ((integralCoefficientSheaf l E X n).over (openObject j))
  finiteFunctor : ∀ n : ℕ, (finite n).functor =
    SheafOfModules.pushforward.{max u (t+1)} (F := sliceSite j)
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
        (finiteMap n))
  [systemContinuous : ((𝟭 ℕ).prod (sliceSite j)).IsContinuous
    (coefficientSequenceTopology ((ProEt.topology X).over (openObject j)))
    (coefficientSequenceTopology (ProEt.topology U))]
  systemMap : sliceRing l E j ⟶
    (((𝟭 ℕ).prod (sliceSite j)).sheafPushforwardContinuous CommRingCat.{max u (t+1)}
      (coefficientSequenceTopology ((ProEt.topology X).over (openObject j)))
      (coefficientSequenceTopology (ProEt.topology U))).obj
        (coefficientSequenceCommRingSheaf l E U)
  systemComponents : ∀ (n : ℕ) (V : Over (openObject j)),
    systemMap.hom.app (op (n, V)) = (finiteMap n).hom.app (op V)
  systems : coefficientSequenceModules l E U ≌ SliceSystems l E j
  systemsFunctor : systems.functor =
    SheafOfModules.pushforward.{max u (t+1)} (F := (𝟭 ℕ).prod (sliceSite j))
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map
        systemMap)

/-- All coefficient transports are additive, and the strict open extension is the
section-normalized localized adjunction supplied by semilinear derived sections.
Source: Stacks 03DI--03DJ, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
structure Operations extends Coefficients l E j where
  [integralAdditive : integral.functor.Additive]
  [finiteAdditive : ∀ n : ℕ, (finite n).functor.Additive]
  [systemsAdditive : systems.functor.Additive]
  openSystems : SemilinearSections.OpenSystems.{t+1, t, max u (t+1)}
    (ProEt.topology X) (rings l E X) (transitions l E X) (openObject j)
  transportEvaluation : ∀ n : ℕ,
    systems.functor ⋙ SemilinearSections.evaluation.{t+1, t, max u (t+1)}
      ((ProEt.topology X).over (openObject j))
      (fun k ↦ (rings l E X k).over (openObject j))
      (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
        (openObject j)).map (transitions l E X k)) n ≅
      coefficientSequenceEvaluation l E U n ⋙ (finite n).functor
  transportSections : ∀ (n : ℕ) (M : coefficientSequenceModules l E U)
    (V : (Over (openObject j))ᵒᵖ)
    (x : ((systems.functor ⋙ SemilinearSections.evaluation.{t+1, t, max u (t+1)}
      ((ProEt.topology X).over (openObject j))
      (fun k ↦ (rings l E X k).over (openObject j))
      (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
        (openObject j)).map (transitions l E X k)) n).obj M).val.obj V),
      HEq (((transportEvaluation n).hom.app M).val.app V x) x

attribute [instance] Operations.integralAdditive Operations.finiteAdditive
  Operations.systemsAdditive

variable (o : Operations l E j)

attribute [instance] SemilinearSections.OpenSystems.extensionAdditive
  SemilinearSections.OpenSystems.extensionLimits SemilinearSections.OpenSystems.extensionColimits

/-- Ordinary completed-coefficient extension: concrete slice transport followed
by direct-sum extension and sheafification. Source: Stacks 03DI
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev extension := o.integral.functor ⋙
  SheafOfModules.localizedSystemExtension.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X) (openObject j)

/-- The corresponding completed-coefficient restriction. Source: Stacks 03DJ
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev restriction := SheafOfModules.localizedSystemRestriction.{t+1, t, max u (t+1)}
  (completedIntegralCommRingSheafUnrestricted l E X) (openObject j) ⋙ o.integral.inverse

/-- Ordinary extension at the positive finite level. Source: Stacks 03DI
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev finiteExtension (n : ℕ) := (o.finite n).functor ⋙
  SheafOfModules.localizedSystemExtension.{t+1, t, max u (t+1)}
    (rings l E X n) (openObject j)

/-- Ordinary finite restriction. Source: Stacks 03DJ
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev finiteRestriction (n : ℕ) :=
  SheafOfModules.localizedSystemRestriction.{t+1, t, max u (t+1)}
    (rings l E X n) (openObject j) ⋙ (o.finite n).inverse

/-- Exact termwise system extension, before taking the derived category.
Source: Stacks 03DI, 0941 (blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev systemExtension := o.systems.functor ⋙ o.openSystems.extension

/-- Exact termwise system restriction. Source: Stacks 03DJ, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev systemRestriction :=
  SemilinearSections.openRestriction.{t+1, t, max u (t+1)}
    (ProEt.topology X) (rings l E X) (transitions l E X) (openObject j) ⋙ o.systems.inverse

/-- Additivity of the constructed open functors. Source: Stacks 03DI
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance extensionAdditive : (extension l E j o).Additive :=
  letI := o.integralAdditive
  letI := SheafOfModules.localizedSystemExtensionAdditive.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X) (openObject j)
  inferInstance

/-- Additivity of restriction. Source: Stacks 03DJ
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance restrictionAdditive : (restriction l E j o).Additive :=
  letI := o.integralAdditive
  inferInstance

/-- Additivity of finite extension. Source: Stacks 03DI
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance finiteExtensionAdditive (n : ℕ) : (finiteExtension l E j o n).Additive :=
  letI := o.finiteAdditive n
  letI := SheafOfModules.localizedSystemExtensionAdditive.{t+1, t, max u (t+1)}
    (rings l E X n) (openObject j)
  inferInstance

/-- Additivity of strict extension. Source: Stacks 03DI, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance systemExtensionAdditive : (systemExtension l E j o).Additive :=
  letI := o.systemsAdditive
  letI := o.openSystems.extensionAdditive
  inferInstance

/-- Additivity of strict restriction. Source: Stacks 03DJ, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance systemRestrictionAdditive : (systemRestriction l E j o).Additive :=
  letI := o.systemsAdditive
  inferInstance

/-- Left exactness of extension. Source: Stacks 03DJ
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance extensionLimits : PreservesFiniteLimits (extension l E j o) :=
  letI := SheafOfModules.localizedSystemExtensionLimits.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X) (openObject j)
  inferInstance

/-- Right exactness of extension. Source: Stacks 03DI
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance extensionColimits : PreservesFiniteColimits (extension l E j o) :=
  letI := SheafOfModules.localizedSystemExtensionColimits.{t+1, t, max u (t+1)}
    (completedIntegralCommRingSheafUnrestricted l E X) (openObject j)
  inferInstance

/-- Left exactness of termwise system extension. Source: Stacks 03DJ, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance systemExtensionLimits : PreservesFiniteLimits (systemExtension l E j o) :=
  letI := o.openSystems.extensionLimits
  inferInstance

/-- Right exactness of termwise system extension. Source: Stacks 03DI, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
instance systemExtensionColimits : PreservesFiniteColimits (systemExtension l E j o) :=
  letI := o.openSystems.extensionColimits
  inferInstance

/-- The localized ringed open adjunction, retaining the actual summand unit.
Source: Stacks 03DI (blueprint: lem-sf-integral-open-reduction-comparison). -/
def ordinaryAdjunction : extension l E j o ⊣ restriction l E j o :=
  o.integral.toAdjunction.comp
    (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
      (completedIntegralCommRingSheafUnrestricted l E X) (openObject j))

/-- The ordinary strict-system adjunction. Source: Stacks 03DI, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
def ordinarySystemAdjunction : systemExtension l E j o ⊣ systemRestriction l E j o :=
  o.systems.toAdjunction.comp o.openSystems.ordinaryAdjunction

/-- Localized completed extension on unbounded derived categories. Source: Stacks 0GL1
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev shriek := (extension l E j o).mapDerivedCategory

/-- Localized completed restriction. Source: Stacks 0GL1
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev star := (restriction l E j o).mapDerivedCategory

/-- Localized strict-system extension. Source: Stacks 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev J := (systemExtension l E j o).mapDerivedCategory

/-- Localized strict-system restriction. Source: Stacks 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev P := (systemRestriction l E j o).mapDerivedCategory

/-- The actual localized open adjunction. Source: Stacks 015F, 03DI
(blueprint: lem-sf-integral-open-reduction-comparison). -/
def openAdjunction : shriek l E j o ⊣ star l E j o :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (ordinaryAdjunction l E j o)

/-- The actual localized system adjunction. Source: Stacks 015F, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
def systemAdjunction : J l E j o ⊣ P l E j o :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (ordinarySystemAdjunction l E j o)

/-- Termwise extension evaluation with the identity on transported sections.
Source: Stacks 03DI, 0941 (blueprint: lem-sf-integral-open-reduction-comparison). -/
def extensionEvaluation (n : ℕ) :
    systemExtension l E j o ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E U n ⋙ finiteExtension l E j o n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft o.systems.functor (o.openSystems.extensionEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (o.transportEvaluation n)
      (SheafOfModules.localizedSystemExtension.{t+1, t, max u (t+1)}
        (rings l E X n) (openObject j)) ≪≫
    Functor.associator _ _ _

open Classical in
/-- The actual extension generator, including the prescribed slice transport.
Source: Stacks 03DI (blueprint: lem-sf-integral-open-reduction-comparison). -/
def extensionSection (M : scalarReductionSource l E U) (V : X.ProEt)
    (a : V ⟶ openObject j) (x : M.val.obj (op ((sliceSite j).obj (Over.mk a)))) :
    ((extension l E j o).obj M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
    ((SheafOfModules.extensionByZeroPresheaf.{max u (t+1)}
      (completedIntegralCoefficientSheafUnrestricted l E X) (openObject j)).obj
        (o.integral.functor.obj M))).app (op V)
    (DirectSum.lof ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj (op V))
      (V ⟶ openObject j) (fun b ↦ (o.integral.functor.obj M).val.obj (op (Over.mk b))) a
        (((eqToHom o.integralFunctor.symm).app M).val.app (op (Over.mk a)) x))

open Classical in
/-- The same direct-sum generator at a finite quotient coefficient.
Source: Stacks 03DI (blueprint: lem-sf-integral-open-reduction-comparison). -/
def finiteExtensionSection (n : ℕ) (M : normalizedDVRModules l E U n) (V : X.ProEt)
    (a : V ⟶ openObject j) (x : M.val.obj (op ((sliceSite j).obj (Over.mk a)))) :
    ((finiteExtension l E j o n).obj M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
    ((SheafOfModules.extensionByZeroPresheaf.{max u (t+1)}
      (integralCoefficientSheaf l E X n) (openObject j)).obj
        ((o.finite n).functor.obj M))).app (op V)
    (DirectSum.lof ((integralCoefficientSheaf l E X n).obj.obj (op V))
      (V ⟶ openObject j) (fun b ↦ ((o.finite n).functor.obj M).val.obj (op (Over.mk b))) a
        (((eqToHom (o.finiteFunctor n).symm).app M).val.app (op (Over.mk a)) x))

/-- The canonical open-tensor comparison, fixed on every scalar-extension unit
of every extension summand. Linearity then fixes all coefficient multiples.
Source: Stacks 0E8I (blueprint: lem-sf-integral-open-reduction-comparison). -/
structure TensorComparison where
  ordinary : ∀ n : ℕ,
    extension l E j o ⋙ scalarReductionExtension l E X n ≅
      scalarReductionExtension l E U n ⋙ finiteExtension l E j o n
  generators : ∀ (n : ℕ) (M : scalarReductionSource l E U) (V : X.ProEt)
    (a : V ⟶ openObject j) (x : M.val.obj (op ((sliceSite j).obj (Over.mk a)))),
    ((ordinary n).hom.app M).val.app (op V)
      (coefficientIntegralScalarUnitSection l E X n ((extension l E j o).obj M) (op V)
        (extensionSection l E j o M V a x)) =
    finiteExtensionSection l E j o n ((scalarReductionExtension l E U n).obj M) V a
      (coefficientIntegralScalarUnitSection l E U n M
        (op ((sliceSite j).obj (Over.mk a))) x)

/-- The recorded quotient-tower completeness predicate, without a boundedness assumption.
Source: Bhatt--Scholze 3.5.2 (blueprint: lem-sf-integral-open-reduction-comparison). -/
abbrev complete (T : Scheme.{t}) : ObjectProperty (DerivedCategory (scalarReductionSource l E T)) :=
  IntegralOnSlice.IsComplete l E T none

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep the concrete model hidden while elaborating the large comparison signatures.
attribute [local irreducible] HasDerivedCategory.standard
  IntegralOnSlice.completionUnit IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.roosUnit IntegralOnSlice.augmentation

/-- A presentation is normalized by the scalar-adjunction units as one strict
chain augmentation, and by its transpose for the actual reduction/limit adjunction.
This fixes the system arrow itself, rather than a lift of its finite evaluations.
Source: Stacks 06YY, 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
def AugmentedPresentation (T : Scheme.{t}) (S : CoefficientDerivedSystemCalculus l E T)
    (Q : CochainComplex (scalarReductionSource l E T) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E T) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E T n).mapHomologicalComplex (.up ℤ)).obj Q) : Prop :=
  ∃ a : ((Functor.const ℕᵒᵖ : scalarReductionSource l E T ⥤
      (ℕᵒᵖ ⥤ scalarReductionSource l E T)).mapHomologicalComplex (.up ℤ)).obj Q ⟶
    ((coefficientSequenceRestriction l E T).mapHomologicalComplex (.up ℤ)).obj C,
    (∀ (i : ℤ) (n : ℕ) (V : T.ProEtᵒᵖ) (x : (Q.X i).val.obj V),
      HEq ((((a.f i).app (op n)).val.app V) x)
        ((((κ n).inv.f i).val.app V)
          (coefficientIntegralScalarUnitSection l E T n (Q.X i) V x))) ∧
    (S.adjunction.homEquiv _ _ e.hom =
      (integralComparisonConstantAdjunction l E T).homEquiv _ _
        ((Functor.const ℕᵒᵖ : scalarReductionSource l E T ⥤
          (ℕᵒᵖ ⥤ scalarReductionSource l E T)).mapDerivedCategoryFactors.hom.app Q ≫
          DerivedCategory.Q.map a ≫
          (coefficientSequenceRestriction l E T).mapDerivedCategoryFactors.inv.app C))

/-- Representative normalization of one strict system map, including all its
finite tensor components. Naming this predicate avoids expanding the full
simultaneous representative construction in every projection of Comparison.
Source: Stacks 0GL1 and 0941
(blueprint: lem-sf-integral-open-reduction-comparison). -/
def StrictModel (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U) (tensor : TensorComparison l E j o)
    (r : (complete l E U).ι ⋙ shriek l E j o ⋙ SX.reduction ≅
      (complete l E U).ι ⋙ SU.reduction ⋙ J l E j o) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology U) (R := completedIntegralCommRingSheafUnrestricted l E U) Q)
    (_hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology U) (R := completedIntegralCommRingSheafUnrestricted l E U) (Q.X i))
    (hcomplete : complete l E U (DerivedCategory.Q.obj Q)),
    ∃ (hJQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X)
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (D : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (eC : SU.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
      (eD : SX.reduction.obj (DerivedCategory.Q.obj
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q)) ≅ DerivedCategory.Q.obj D)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E U n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E U n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj
            (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (f : D ≅ ((systemExtension l E j o).mapHomologicalComplex (.up ℤ)).obj C),
      CoefficientReductionPresentation l E U SU.toCoefficientDerivedSystemReduction
        Q hQ C eC κC ∧
      AugmentedPresentation l E U SU Q C eC κC ∧
      CoefficientReductionPresentation l E X SX.toCoefficientDerivedSystemReduction
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) hJQ D eD κD ∧
      AugmentedPresentation l E X SX
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) D eD κD ∧
      (r.hom.app ⟨DerivedCategory.Q.obj Q, hcomplete⟩ ≫ (J l E j o).map eC.hom ≫
        (systemExtension l E j o).mapDerivedCategoryFactors.hom.app C =
      SX.reduction.map ((extension l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        eD.hom ≫ DerivedCategory.Q.map f.hom) ∧
      (∀ (n : ℕ) (i : ℤ),
        (coefficientSequenceEvaluation l E X n).map (f.hom.f i) ≫
          (extensionEvaluation l E j o n).hom.app (C.X i) ≫
          (finiteExtension l E j o n).map ((κC n).hom.f i) =
        (κD n).hom.f i ≫ (tensor.ordinary n).hom.app (Q.X i))

/-- The comparisons of actual strict systems and the actual completion units.
The representative square is imposed before evaluation; its finite components
are the generator-normalized open-tensor map. The last equations are the realized
open unit and counit, as words in the specified adjunction transformations.
Source: Stacks 0GL1, 0E8I and 0941; node proof Steps 1--10
(blueprint: lem-sf-integral-open-reduction-comparison). -/
structure Comparison (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U) (tensor : TensorComparison l E j o) where
  r : (complete l E U).ι ⋙ shriek l E j o ⋙ SX.reduction ≅
    (complete l E U).ι ⋙ SU.reduction ⋙ J l E j o
  extensionComplete : ∀ K : (complete l E U).FullSubcategory,
    complete l E X ((shriek l E j o).obj K.obj)
  restrictionComplete : ∀ H : (complete l E X).FullSubcategory,
    complete l E U ((star l E j o).obj H.obj)
  s : (complete l E X).ι ⋙ star l E j o ⋙ SU.reduction ≅
    (complete l E X).ι ⋙ SX.reduction ⋙ P l E j o
  /-- Ordinary restriction is realized by its actual completion unit. -/
  unitU : ∀ K : (complete l E U).FullSubcategory,
    K.obj ≅ (coefficientSequenceLimit l E U).obj (SU.reduction.obj K.obj)
  unitUHom : ∀ K, (unitU K).hom = SU.adjunction.unit.app K.obj
  unitX : ∀ H : (complete l E X).FullSubcategory,
    H.obj ≅ (coefficientSequenceLimit l E X).obj (SX.reduction.obj H.obj)
  unitXHom : ∀ H, (unitX H).hom = SX.adjunction.unit.app H.obj
  d : (complete l E U).ι ⋙ SU.reduction ⋙ J l E j o ⋙ coefficientSequenceLimit l E X ≅
    (complete l E U).ι ⋙ shriek l E j o
  dFormula : ∀ K : (complete l E U).FullSubcategory,
    d.hom.app K = (coefficientSequenceLimit l E X).map (r.inv.app K) ≫
      (unitX ⟨(shriek l E j o).obj K.obj, extensionComplete K⟩).inv
  reductionD : ∀ K : (complete l E U).FullSubcategory,
    SX.reduction.map (d.hom.app K) ≫ r.hom.app K =
      SX.adjunction.counit.app ((J l E j o).obj (SU.reduction.obj K.obj))
  /-- Completed restriction comparison, inverse of its actual reconstruction unit. -/
  pullRealization : (complete l E X).ι ⋙ SX.reduction ⋙ P l E j o ⋙
      coefficientSequenceLimit l E U ≅ (complete l E X).ι ⋙ star l E j o
  pullFormula : ∀ H : (complete l E X).FullSubcategory,
    pullRealization.hom.app H = (coefficientSequenceLimit l E U).map (s.inv.app H) ≫
      (unitU ⟨(star l E j o).obj H.obj, restrictionComplete H⟩).inv
  systemUnit : ∀ K : (complete l E U).FullSubcategory,
    SU.reduction.map ((openAdjunction l E j o).unit.app K.obj) ≫
      s.hom.app ⟨(shriek l E j o).obj K.obj, extensionComplete K⟩ ≫
      (P l E j o).map (r.hom.app K) =
    (systemAdjunction l E j o).unit.app (SU.reduction.obj K.obj)
  systemCounit : ∀ H : (complete l E X).FullSubcategory,
    r.hom.app ⟨(star l E j o).obj H.obj, restrictionComplete H⟩ ≫
      (J l E j o).map (s.hom.app H) ≫
      (systemAdjunction l E j o).counit.app (SX.reduction.obj H.obj) =
    SX.reduction.map ((openAdjunction l E j o).counit.app H.obj)
  realizedUnit : ∀ K : (complete l E U).FullSubcategory,
    (unitU K).hom ≫
      (coefficientSequenceLimit l E U).map
        ((systemAdjunction l E j o).unit.app (SU.reduction.obj K.obj)) ≫
      (coefficientSequenceLimit l E U).map ((P l E j o).map (r.inv.app K)) ≫
      pullRealization.hom.app ⟨(shriek l E j o).obj K.obj, extensionComplete K⟩ =
    (openAdjunction l E j o).unit.app K.obj
  realizedCounit : ∀ H : (complete l E X).FullSubcategory,
    d.inv.app ⟨(star l E j o).obj H.obj, restrictionComplete H⟩ ≫
      (coefficientSequenceLimit l E X).map ((J l E j o).map (s.hom.app H)) ≫
      (coefficientSequenceLimit l E X).map
        ((systemAdjunction l E j o).counit.app (SX.reduction.obj H.obj)) ≫
      (unitX H).inv = (openAdjunction l E j o).counit.app H.obj
  /-- One strict chain comparison, before evaluation or realization. -/
  strictModel : StrictModel l E j o SX SU tensor r

end WeilConjectures.IntegralOpenReduction

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization

import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOpenScalarPullbackMate
import WeilConjectures.SmoothPurity.Derived.DerivedCompleteFiniteReductionDetection
import all WeilConjectures.SixFunctors.FrobeniusExchange.IntegralSystemEvaluationNormalization
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.OrdinaryOpenFiniteEvaluation
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralSystemOpenEvaluation
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import all WeilConjectures.SixFunctors.FrobeniusExchange.IntegralSystemCompositorNormalization
import all WeilConjectures.SixFunctors.FrobeniusExchange.IntegralSystemSquareNormalization
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SixFunctors.System.SystemDirectImageRoosPresentation
import WeilConjectures.SixFunctors.Supporting.DerivedLimitTriangleTransport
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.SixFunctors.System.SystemDirectImageEffectivity
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.SmoothPurity.Compact.CompactSupportRepresentativeIndependence
import WeilConjectures.SixFunctors.FrobeniusExchange.SystemNativeEvaluationBridge
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportStrictReductionGamma
import WeilConjectures.Tactic.ExactByKernel
import WeilConjectures.Tactic.RflByKernel

/-! # Simultaneous-system realization of operation exchanges

Source: slopmaster2 blueprint, `def:weil-direct-image-object` and
`def:weil-compact-support-object`; Deligne, Weil II, (1.1.10)--(1.1.14)
(blueprint: def-weil-system-operation-exchange-realization).

## Main definitions and statements

- `finiteExchange`, `finiteTensorExchange`: finite mates for a general commuting square.
- `systemExchange`, `systemCompactExchange`: actual mates before evaluation.
- `realize`, `integralExchange`, `coefficientExchange`: normalized whole-system realization.
- `directIntegral`, `compactIntegral`: natural transformations on constructible domains.
- `directIntegral_reduction`, `compactIntegral_reduction`: the specified counit equations.
-/

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.FrobeniusExchange

private theorem realization_counit_cancel
    {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) (L : D ⥤ C) (ε : L ⋙ R ⟶ 𝟭 D)
    {a b c d : D} {x : C} (q : x ⟶ L.obj a)
    (s : a ⟶ b) (t : b ⟶ c) (β : d ≅ c) :
    R.map ((q ≫ L.map s) ≫ L.map t ≫ L.map β.inv) ≫ ε.app d ≫ β.hom =
      (R.map q ≫ ε.app a) ≫ s ≫ t := by
  have hn {A B : D} (h : A ⟶ B) :
      R.map (L.map h) ≫ ε.app B = ε.app A ≫ h := ε.naturality h
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (hn β.inv), Iso.inv_hom_id, Category.comp_id,
    hn t, reassoc_of% (hn s)]

/-- Transport a counit equation through fixed source and target isomorphisms. -/
private theorem transport_reduction_equation
    {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) (P : C ⥤ C) (G : D ⥤ D) (κ : P ⋙ R ⟶ R ⋙ G)
    {a a' b b' : C} {d : D} (δ : a ⟶ a') (γ : b ⟶ b') (γinv : b' ⟶ b)
    (hγ : γinv ≫ γ = 𝟙 b')
    (x : P.obj a' ⟶ b') (r : R.obj b' ⟶ d) (e : G.obj (R.obj a') ⟶ d)
    (h : R.map x ≫ r = κ.app a' ≫ e) :
    R.map (P.map δ ≫ x ≫ γinv) ≫ R.map γ ≫ r =
      κ.app a ≫ G.map (R.map δ) ≫ e := by
  calc
    _ = R.map (P.map δ) ≫ (R.map x ≫ r) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← R.map_comp_assoc γinv γ, hγ, R.map_id, Category.id_comp]
    _ = R.map (P.map δ) ≫ κ.app a' ≫ e := by
      rw [h]
    _ = _ := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun k ↦ k ≫ e) (κ.naturality δ)

variable (A : Type u) [CommRing A] [Finite A]

/-- The finite exchange for any commuting square is the specified adjunction mate.
The four corners and both vertical arrows may differ; only commutativity is used.
Source: blueprint `def:direct-image-exchange` and `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def finiteExchange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (w : gX ≫ f = f' ≫ gY) :
    proEtaleConstantDerivedDirectImage f A ⋙ sfIntrinsicDerivedPullback A gY ⟶
      sfIntrinsicDerivedPullback A gX ⋙ proEtaleConstantDerivedDirectImage f' A :=
  (mateEquiv
    (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicConstantModuleAdjunction f' A).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _
      ((sfIntrinsicDerivedPullbackComp A f' gY).symm ≪≫
        eqToIso (congrArg (fun h ↦ sfIntrinsicDerivedPullback A h) w.symm) ≪≫
        sfIntrinsicDerivedPullbackComp A gX f).hom))

/-- The ambient mate in the recorded tensor-pullback coordinates. Both coordinate
changes are uniquely fixed by the ordinary units, so this is the ambient ringed mate.
Source: blueprint `def:direct-image-exchange`
(blueprint: def-weil-system-operation-exchange-realization). -/
def finiteTensorExchange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (w : gX ≫ f = f' ≫ gY) :
    proEtaleConstantDerivedDirectImage f A ⋙ proEtaleConstantRingDerivedPullback A gY ⟶
      proEtaleConstantRingDerivedPullback A gX ⋙ proEtaleConstantDerivedDirectImage f' A :=
  whiskerLeft (proEtaleConstantDerivedDirectImage f A)
      (openSquareDerivedPullbackModel A gY).hom ≫
    finiteExchange A f f' gX gY w ≫
    whiskerRight (openSquareDerivedPullbackModel A gX).inv
      (proEtaleConstantDerivedDirectImage f' A)

variable (A : Type u) [CommRing A] [Finite A]

section Systems
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev systemRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
private abbrev systemQuotient (n : ℕ) :
    systemRings l E (n + 1) ⟶ systemRings l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift
private theorem samePush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralComparisonSequenceDirectImage l E f =
      ProEtale.VaryingRing.push (systemRings l E) (systemQuotient l E) f := by
  rfl

/-- Finite chosen-compactification exchange, literally the proper mate followed
by proper image of the canonical open-adjunction exchange.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def finiteCompact (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) gY ⟶
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) gX ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  exact whiskerLeft (sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E n) c.i)
      (finiteTensorExchange (Padic.coefficientExtensionRing l E n) c.g c.g gB gY wp) ≫
    whiskerRight (constantOpenSquareExchange l E n hn gX c.i c.i gB sj).hom
      (proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E n))

/-- Additivity of the sectionwise direct image on the strict varying-ring diagram.
Source: Zheng 4.1 and 4.10; blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization).
Proof: addition is sectionwise, and precomposition and scalar restriction leave
addition unchanged, at every index and every vertical object. -/
theorem systemDirect_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralComparisonSequenceDirectImage l E f).Additive := by
  exact (integralComparisonSequenceDirectImage l E f).additive_of_preserves_binary_products

attribute [instance] systemDirect_additive

/-- Strict coefficient systems admit simultaneous K-injective resolutions.
Source: Zheng 4.10; Stacks 079P, 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: these systems are module sheaves on the small vertical sequence site.
The Grothendieck module-sheaf theorem gives functorial K-injective resolutions
in its ordinary unbounded derived category. -/
theorem system_hasKInjectives (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X) := by
  have : IsGrothendieckAbelian.{u + 1} (coefficientSequenceModules l E X) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0} _ _
  exact Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

attribute [instance] system_hasKInjectives

/-- Total right-derived direct image of entire strict semilinear coefficient systems.
Source: Zheng 4.10; blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
abbrev systemDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y :=
  (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor

/-- The derived adjunction is derived from the actual ordinary system adjunction.
Source: Zheng 4.10; Stacks 07A4
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralComparisonDerivedSequencePullback l E f ⊣ systemDirect l E f :=
  letI : (integralComparisonSequenceDirectImage l E f).leftAdjoint.Additive :=
    inferInstanceAs (integralComparisonSequencePullback l E f).Additive
  letI : PreservesFiniteLimits (integralComparisonSequenceDirectImage l E f).leftAdjoint :=
    inferInstanceAs (PreservesFiniteLimits (integralComparisonSequencePullback l E f))
  letI : PreservesFiniteColimits (integralComparisonSequenceDirectImage l E f).leftAdjoint :=
    inferInstanceAs (PreservesFiniteColimits (integralComparisonSequencePullback l E f))
  (Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f)).mapDerivedCategoryRightDerivedAdjunction

/-- The square comparison on the derived category of whole strict systems.
It is obtained before evaluation, from the section-normalized ordinary compositor.
Source: Zheng 4.10; blueprint `def:direct-image-exchange`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY) :
    integralComparisonDerivedSequencePullback l E gY ⋙
        integralComparisonDerivedSequencePullback l E f ≅
      integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequencePullback l E gX :=
  (integralComparisonSystemComposition l E f gY).symm ≪≫
    eqToIso (congrArg (fun h ↦ integralComparisonDerivedSequencePullback l E h) w.symm) ≪≫
    integralComparisonSystemComposition l E gX f

/-- The specified system mate, formed before finite evaluation or derived inverse limit.
Source: Zheng 4.10; blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemExchange {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY) :
    systemDirect l E f ⋙ integralComparisonDerivedSequencePullback l E gY ⟶
      integralComparisonDerivedSequencePullback l E gX ⋙ systemDirect l E f :=
  (mateEquiv (systemAdjunction l E f) (systemAdjunction l E f)
    (TwoSquare.mk _ _ _ _ (systemSquare l E f gX gY w).hom))

/-- A simultaneous quotient-complex presentation of the published integral operations.
Its reduction, total limit and pullback realizations carry the dependency's full
K-flat quotient-generator and K-injective Roos normalizations.
Source: Stacks 099N(5), 0941; blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def models : IntegralComparisonCoefficientData l E :=
  ((integralPullbackComparisonRealization l (ULift.{u} ℚ_[l]) (ULift.{u} ℚ_[l])
    (AlgHom.id ℚ_[l] (ULift.{u} ℚ_[l]))).choose).coefficient E

/-- The coherent reduction system of one integral object, including all quotient maps.
Source: blueprint `def:weil-direct-image-object`, integral paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
abbrev reduction (X : Scheme.{u}) := (models l E).system X |>.reduction

/-- Realize an actual system operation by reduction, that operation, exact scalar
restriction, and total right-derived inverse limit, in that order.
Source: blueprint `def:weil-direct-image-object`, integral paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
def realize {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y) :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  reduction l E X ⋙ H ⋙ coefficientSequenceLimit l E Y

/-- The canonical operation-reduction map is the whole-system adjunction counit.
Source: blueprint integral operation comparisons
(blueprint: def-weil-system-operation-exchange-realization). -/
def operationReduction {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y) :
    realize l E H ⋙ reduction l E Y ⟶ reduction l E X ⋙ H :=
  whiskerLeft (reduction l E X ⋙ H) ((models l E).system Y).adjunction.counit

/-- Integral direct image in the simultaneous-system presentation.
Source: blueprint `def:weil-direct-image-object`, integral paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
def integralDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  realize l E (systemDirect l E f)

/-- The operation comparison on the source is the pullback realization followed
by pullback of the entire-system counit. It is constructed before evaluation.
Source: blueprint `def:weil-direct-image-object`, alpha-star
(blueprint: def-weil-system-operation-exchange-realization). -/
def sourceComparison {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y)
    (gY : Y ⟶ Y) :
    realize l E H ⋙ integralDerivedPullback l E gY ⟶
      reduction l E X ⋙ H ⋙ integralComparisonDerivedSequencePullback l E gY ⋙
        coefficientSequenceLimit l E Y :=
  whiskerLeft (realize l E H) ((models l E).pullback gY).realization.hom ≫
    whiskerRight
      (whiskerRight
        (whiskerLeft (reduction l E X ⋙ H) ((models l E).system Y).adjunction.counit)
        (integralComparisonDerivedSequencePullback l E gY))
      (coefficientSequenceLimit l E Y)

/-- The canonical reduction comparison for pullback is inverted on the integral
constructible domain, using the dependency's whole-system effectivity assertion.
Source: blueprint `def:weil-direct-image-object`, beta-star
(blueprint: def-weil-system-operation-exchange-realization). -/
def reductionPullbackIso {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] (gX : X ⟶ X) :
    (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E gX ⋙
        reduction l E X ≅
      (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        integralComparisonDerivedSequencePullback l E gX := by
  let t := whiskerLeft (sfIntegralConstructible l E X).ι
    (integralComparisonPullbackCounit l E gX ((models l E).system X)
      ((models l E).system X) ((models l E).roos X) ((models l E).pullback gX))
  letI : ∀ K : sfIntegralConstructibleCategory l E X, IsIso (t.app K) :=
    fun K ↦ (models l E).effective gX K
  letI := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The integral exchange is beta after L of the specified system map after alpha.
No morphism is chosen from its finite evaluations.
Source: blueprint `def:weil-direct-image-object`, integral exchange formula
(blueprint: def-weil-system-operation-exchange-realization). -/
def integralExchange {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y)
    (e : H ⋙ integralComparisonDerivedSequencePullback l E gY ⟶
      integralComparisonDerivedSequencePullback l E gX ⋙ H) :
    (sfIntegralConstructible l E X).ι ⋙ realize l E H ⋙ integralDerivedPullback l E gY ⟶
      (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E gX ⋙ realize l E H :=
  whiskerLeft (sfIntegralConstructible l E X).ι (sourceComparison l E H gY) ≫
    whiskerRight (whiskerLeft ((sfIntegralConstructible l E X).ι ⋙ reduction l E X) e)
      (coefficientSequenceLimit l E Y) ≫
    whiskerRight (reductionPullbackIso l E gX).inv (H ⋙ coefficientSequenceLimit l E Y)

/-- Counit naturality computes reduction of any realized system exchange.
Source: the alpha-L(e)-beta definition above and naturality of the adjunction counit
(blueprint: def-weil-system-operation-exchange-realization). -/
private theorem integralExchange_reduction {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y)
    (e : H ⋙ integralComparisonDerivedSequencePullback l E gY ⟶
      integralComparisonDerivedSequencePullback l E gX ⋙ H)
    (K : sfIntegralConstructibleCategory l E X) :
    (reduction l E Y).map ((integralExchange l E H gX gY e).app K) ≫
        (operationReduction l E H).app ((integralDerivedPullback l E gX).obj K.obj) ≫
        H.map ((reductionPullbackIso l E gX).hom.app K) =
      (integralComparisonPullbackCounit l E gY ((models l E).system Y)
          ((models l E).system Y) ((models l E).roos Y)
          ((models l E).pullback gY)).app ((realize l E H).obj K.obj) ≫
        (integralComparisonDerivedSequencePullback l E gY).map
          ((operationReduction l E H).app K.obj) ≫
        e.app ((reduction l E X).obj K.obj) := by
  let R := reduction l E Y
  let L := coefficientSequenceLimit l E Y
  let ε := ((models l E).system Y).adjunction.counit
  let G := integralComparisonDerivedSequencePullback l E gY
  let N := (reduction l E X).obj K.obj
  let β := H.mapIso ((reductionPullbackIso l E gX).app K)
  let q := ((models l E).pullback gY).realization.hom.app ((realize l E H).obj K.obj)
  have h := realization_counit_cancel R L ε q
    (G.map (ε.app (H.obj N))) (e.app N) β
  simpa only [integralExchange, sourceComparison, operationReduction,
    integralComparisonPullbackCounit, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.map_comp, Category.assoc, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.comp_map, Iso.app_hom, Iso.app_inv,
    R, L, ε, G, N, β, q, Functor.comp_obj, ObjectProperty.ι_obj] using h

/-- Exact open extension exists on whole strict coefficient systems.
Source: Zheng 4.1, 4.10; blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization).
Proof: localize the vertical sequence site at the open. The direct-sum extension
presheaf and sheafification give the left adjoint to restriction, independently
at every quotient index. Its sectionwise units are the actual open units.
Both kernels and cokernels are computed componentwise, so extension is exact. -/
theorem systemPullback_isRightAdjoint {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (integralComparisonSequencePullback l E j).IsRightAdjoint := by
  exact ProEtale.VaryingRing.pull_isRightAdjoint (systemRings l E) (systemQuotient l E) j

/-- The universal ordinary open extension, determined up to its adjunction comparison.
Source: Zheng 4.1; blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  letI := systemPullback_isRightAdjoint l E j
  (integralComparisonSequencePullback l E j).leftAdjoint

/-- The actual system open adjunction, with its canonical unit and counit.
Source: Zheng 4.1; blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    systemOpen l E j ⊣ integralComparisonSequencePullback l E j :=
  letI := systemPullback_isRightAdjoint l E j
  Adjunction.ofIsRightAdjoint (integralComparisonSequencePullback l E j)

/-- Exactness of the specified open extension on strict coefficient systems.
Source: Zheng 4.1, 4.10; Stacks 03DI, 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: identify this left adjoint with the localized extension presheaf followed
by sheafification via the unique adjunction-compatible comparison. The open
extension is exact at every level, hence exact on the abelian system category. -/
theorem systemOpen_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (systemOpen l E j).Additive ∧ PreservesFiniteLimits (systemOpen l E j) ∧
      PreservesFiniteColimits (systemOpen l E j) := by
  have h := ProEtale.VaryingRing.extension_exact (systemRings l E) (systemQuotient l E) j
  simpa only [systemOpen, integralComparisonSequencePullback, samePush,
    ProEtale.VaryingRing.extension, ProEtale.VaryingRing.pull] using h

/-- The additive structure from exact system open extension.
Source: Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
instance systemOpenAdditive {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (systemOpen l E j).Additive := (systemOpen_exact l E j).1

/-- Finite-limit preservation from exact system open extension.
Source: Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
instance systemOpenLimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (systemOpen l E j) := (systemOpen_exact l E j).2.1

/-- Finite-colimit preservation from exact system open extension.
Source: Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
instance systemOpenColimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (systemOpen l E j) := (systemOpen_exact l E j).2.2

/-- Termwise open extension descends exactly to the ordinary derived system category.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
abbrev systemDerivedOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (systemOpen l E j).mapDerivedCategory

/-- The derived open adjunction is the exact descent of the ordinary one.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemDerivedOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    systemDerivedOpen l E j ⊣ integralComparisonDerivedSequencePullback l E j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (systemOpenAdjunction l E j)

/-- Ordinary direct image commutes strictly with vertical evaluation. The coefficient
maps are the same constant sections; both functors evaluate M at (n, X ×_Y U).
Source: Zheng 4.1, 4.10 (blueprint: def-weil-system-operation-exchange-realization).
Proof: unfold the two sectionwise pushforwards and vertical evaluation. Their
base-change functors agree on objects and maps. Their ring maps send each constant
section to the same section. Module and functor extensionality, followed by proof
irrelevance for sheaf conditions and ring-map compatibility, gives equality. -/
theorem systemDirectEvaluationOrdinary_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonSequenceDirectImage l E f ⋙ coefficientSequenceEvaluation l E Y n =
      coefficientSequenceEvaluation l E X n ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) := by
  unfold integralComparisonSequenceDirectImage coefficientSequenceEvaluation
    proEtaleConstantModuleDirectImage
  apply vertical_pushforward_eq (ProEt.topology Y) (ProEt.topology X)
    (proEtaleBaseChange f) n
  intro U
  rw [ObjectProperty.eqToHom_hom, eqToHom_app,
    ObjectProperty.eqToHom_hom, eqToHom_app]
  change (𝟙 _ : _ ⟶ _) ≫ _ = _ ≫ (𝟙 _ : _ ⟶ _)
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- Inverse-image evaluation is the conjugate of the actual sectionwise equality.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemPullEvaluationOrdinaryInv {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⟶
      integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E X n :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
    (sfIntrinsicConstantModuleAdjunction f (Padic.coefficientExtensionRing l E (n + 1)))).symm
    (TwoSquare.mk _ _ _ _ (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).hom))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The section-normalized inverse-image evaluation mate is invertible.
Source: Zheng 4.1, 4.10 (blueprint: def-weil-system-operation-exchange-realization).
Proof: the ordinary inverse image on the sequence site is vertical inverse image
at each level. The displayed mate sends every tensor generator to its identical
inverse-image generator. The generator map and its inverse preserve vertical
restriction and quotient transitions, and hence are mutually inverse sheaf maps. -/
theorem systemPullEvaluationOrdinaryInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (systemPullEvaluationOrdinaryInv l E f n) := by
  let d := eqToIso (systemDirectEvaluationOrdinary_eq l E f n)
  change IsIso ((mateEquiv (Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f))
    (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l E (n + 1)))).symm d.hom)
  apply WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
    (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficientSequenceCommRingSheaf l E Y))
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficientSequenceCommRingSheaf l E X)) n
    ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    (integralCoefficientSheaf l E Y n) (integralCoefficientSheaf l E X n)
    (coefficientSequenceEvaluationRing_eq l E Y n)
    (coefficientSequenceEvaluationRing_eq l E X n)
    ⟨Functor.whiskerRight
      (proEtaleCoefficientDirectImageMap f
        (Padic.coefficientExtensionRing l E (n + 1))).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    (integralComparisonSequencePullback l E f)
    (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f)
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
    (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l E (n + 1))) d

/-- Exact descent of the uniquely unit-normalized inverse-image evaluation mate.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemPullEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    coefficientSequenceDerivedEvaluation l E Y n ⋙
        sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f ≅
      integralComparisonDerivedSequencePullback l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n := by
  letI := systemPullEvaluationOrdinaryInv_isIso l E f n
  letI := coefficientSequenceEvaluation_additiveInstance l E X n
  letI := coefficientSequenceEvaluation_additiveInstance l E Y n
  letI := coefficientSequenceEvaluation_limits l E X n
  letI := coefficientSequenceEvaluation_limits l E Y n
  letI := coefficientSequenceEvaluation_colimits l E X n
  letI := coefficientSequenceEvaluation_colimits l E Y n
  letI := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits
    (Padic.coefficientExtensionRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits
    (Padic.coefficientExtensionRing l E (n + 1)) f
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (systemPullEvaluationOrdinaryInv l E f n)) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Direct-image evaluation is the derived adjunction mate of that same pullback map.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemDirectEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    systemDirect l E f ⋙ coefficientSequenceDerivedEvaluation l E Y n ⟶
      coefficientSequenceDerivedEvaluation l E X n ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  (mateEquiv (systemAdjunction l E f)
    (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (systemPullEvaluation l E f n).hom))

section EvaluationProof
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified direct-image evaluation mate is invertible.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization).
Proof: use the simultaneous-resolution calculus of Zheng 4.10 for sectionwise
system direct image and its finite evaluations. Resolve the whole system in the
common acyclic class for these section direct images; the same resolution then
computes each finite direct image. The ordinary sectionwise equality identifies
their comparison. The evaluated units identify this comparison with the displayed
mate, proving invertibility. No exactness of finite quotient tensor is required. -/
theorem systemDirectEvaluation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (systemDirectEvaluation l E f n) := by
  let a : integralComparisonSequencePullback l E f ⊣
      integralComparisonSequenceDirectImage l E f := Adjunction.ofIsRightAdjoint _
  let b := sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (n + 1))
  let θ := @asIso _ _ _ _ (systemPullEvaluationOrdinaryInv l E f n)
    (systemPullEvaluationOrdinaryInv_isIso l E f n)
  have hθ : IsIso (mateEquiv a b θ.hom) := by
    change IsIso (mateEquiv a b ((mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _
        (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).hom)))
    rw [Equiv.apply_symm_apply]
    exact (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).isIso_hom
  unfold systemDirectEvaluation systemAdjunction
  exact integralSystemEvaluationMate_isIso l E f n a b θ hθ

end EvaluationProof

/-- Open-extension evaluation is the left mate of normalized pullback evaluation.
Source: Zheng 4.10; Stacks 03DI
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenEvaluationInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    coefficientSequenceDerivedEvaluation l E U n ⋙
        sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E (n + 1)) j ⟶
      systemDerivedOpen l E j ⋙ coefficientSequenceDerivedEvaluation l E X n :=
  ((mateEquiv (systemDerivedOpenAdjunction l E j)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j))).symm
    (TwoSquare.mk _ _ _ _ (systemPullEvaluation l E j n).inv))

section OpenEvaluationProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false

open Opposite

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheafTransition ProEtale.VaryingRing.coefficientTransition
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  integralComparisonSequencePullback integralCoefficientSheaf
  integralComparisonDerivedSequencePullback systemPullEvaluationOrdinaryInv
attribute [local irreducible] constantSheaf Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

section OrdinarySections

attribute [local irreducible] integralComparisonSequenceDirectImage coefficientSequenceEvaluation
  proEtaleConstantModuleDirectImage

private theorem openEvaluation_eqToIso_sections
    {U X : Scheme.{u}} (n : ℕ)
    {F G : coefficientSequenceModules l E U ⥤ normalizedDVRModules l E X n}
    (h : F = G) (M : coefficientSequenceModules l E U) (V : X.ProEtᵒᵖ)
    (x : (F.obj M).val.obj V) :
    HEq (((eqToIso h).hom.app M).val.app V x) x := by
  subst G
  rfl

private theorem ordinaryDirectSections {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)
    (M : coefficientSequenceModules l E U) (V : X.ProEt)
    (x : ((integralComparisonSequenceDirectImage l E j ⋙
      coefficientSequenceEvaluation l E X n).obj M).val.obj (op V)) :
    HEq (((eqToIso (systemDirectEvaluationOrdinary_eq l E j n)).hom.app M).val.app
      (op V) x) x :=
  openEvaluation_eqToIso_sections l E (U := U) (X := X) n
    (systemDirectEvaluationOrdinary_eq l E j n) M (op V) x

private theorem ordinaryPullUnit {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)
    (M : coefficientSequenceModules l E X) :
    (sfIntrinsicConstantModuleAdjunction j
      (Padic.coefficientExtensionRing l E (n + 1))).homEquiv _ _
        ((systemPullEvaluationOrdinaryInv l E j n).app M) =
      (coefficientSequenceEvaluation l E X n).map
        ((Adjunction.ofIsRightAdjoint
          (integralComparisonSequenceDirectImage l E j)).unit.app M) ≫
        (eqToIso (systemDirectEvaluationOrdinary_eq l E j n)).hom.app
          ((integralComparisonSequencePullback l E j).obj M) := by
  rw [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E j))
    (sfIntrinsicConstantModuleAdjunction j
      (Padic.coefficientExtensionRing l E (n + 1)))
    (TwoSquare.mk _ _ _ _ (eqToIso (systemDirectEvaluationOrdinary_eq l E j n)).hom) M).symm

end OrdinarySections

/-- Substitute the two evaluation functor equalities before applying the ordinary
normalization theorem, avoiding repeated unfolding of sectionwise pushforwards. -/
private theorem normalizedFiniteEvaluationWithEqualities
    (R : ℕ → CommRingCat.{u + 1}) (τ : ∀ k, R (k + 1) ⟶ R k)
    {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ)
    (F : ProEtale.VaryingRing.Modules R τ X ⥤ ProEtale.VaryingRing.Modules R τ Y)
    [hFadj : F.IsRightAdjoint]
    (hF : F = ProEtale.VaryingRing.push R τ j)
    (Q : ProEtale.StrictTower.Modules (R n) Y ⥤ ProEtale.StrictTower.Modules (R n) X)
    (Fn : ProEtale.StrictTower.Modules (R n) X ⥤ ProEtale.StrictTower.Modules (R n) Y)
    (hFn : Fn = ProEtale.StrictTower.moduleDirectImage (R n) j)
    (b : Q ⊣ Fn)
    (O : ProEtale.VaryingRing.Modules R τ X ⥤ ProEtale.VaryingRing.Modules R τ Y)
    (a : O ⊣ F.leftAdjoint)
    (EX : ProEtale.VaryingRing.Modules R τ X ⥤ ProEtale.StrictTower.Modules (R n) X)
    (EY : ProEtale.VaryingRing.Modules R τ Y ⥤ ProEtale.StrictTower.Modules (R n) Y)
    (hEX : EX = ProEtale.VaryingRing.eval R τ X n)
    (hEY : EY = ProEtale.VaryingRing.eval R τ Y n)
    (d : F ⋙ EY ≅
      EX ⋙ Fn)
    (hd : ∀ (M : ProEtale.VaryingRing.Modules R τ X) (U : Y.ProEt)
      (x : ((F ⋙ EY).obj M).val.obj (op U)),
      HEq ((d.hom.app M).val.app (op U) x) x)
    (β : EY ⋙ Q ≅
      F.leftAdjoint ⋙ EX)
    (hβ : ∀ M, b.homEquiv _ _ (β.hom.app M) =
      (EY).map
        ((Adjunction.ofIsRightAdjoint F).unit.app M) ≫ d.hom.app (F.leftAdjoint.obj M)) :
    ∃ (L : ProEtale.StrictTower.Modules (R n) X ⥤ ProEtale.StrictTower.Modules (R n) Y)
      (adj : L ⊣ Q)
      (e : O ⋙ EY ≅
        EX ⋙ L),
      ∀ N : ProEtale.VaryingRing.Modules R τ Y,
        (EY).map (a.counit.app N) =
          e.hom.app (F.leftAdjoint.obj N) ≫ L.map (β.inv.app N) ≫
            adj.counit.app ((EY).obj N) := by
  subst EX EY
  exact IntegralSystemRealization.normalizedFiniteEvaluation R τ j n F hF Q Fn hFn b O a
    d hd β hβ

private theorem ordinaryEvaluation_eq (X : Scheme.{u}) (n : ℕ) :
    coefficientSequenceEvaluation l E X n =
      ProEtale.VaryingRing.eval (systemRings l E) (systemQuotient l E) X n := by
  rfl

section MateNormalization

attribute [local irreducible] integralComparisonSequenceDirectImage coefficientSequenceEvaluation
  proEtaleConstantModuleDirectImage

-- The coefficient-category and chosen-adjoint transports need a larger elaboration budget.
private theorem systemOpenEvaluationOrdinaryInv_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :
    IsIso ((mateEquiv (systemOpenAdjunction l E j)
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)).symm
      (TwoSquare.mk _ _ _ _
        (@asIso _ _ _ _ (systemPullEvaluationOrdinaryInv l E j n)
          (systemPullEvaluationOrdinaryInv_isIso l E j n)).inv)) := by
  letI : (integralComparisonSequenceDirectImage l E j).IsRightAdjoint :=
    integralComparisonSequenceRightAdjoint l E j
  let b := sfIntrinsicConstantModuleAdjunction j
    (Padic.coefficientExtensionRing l E (n + 1))
  let d := eqToIso (systemDirectEvaluationOrdinary_eq l E j n)
  let β := @asIso _ _ _ _ (systemPullEvaluationOrdinaryInv l E j n)
    (systemPullEvaluationOrdinaryInv_isIso l E j n)
  have hd := ordinaryDirectSections l E j n
  have hβ := ordinaryPullUnit l E j n
  obtain ⟨L, c, e, he⟩ :=
    normalizedFiniteEvaluationWithEqualities
      (hFadj := integralComparisonSequenceRightAdjoint l E j)
      (systemRings l E) (systemQuotient l E) j n
      (integralComparisonSequenceDirectImage l E j) (samePush l E j)
      (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j)
      (proEtaleConstantModuleDirectImage j (Padic.coefficientExtensionRing l E (n + 1)))
      (finitePush_eq l E j n) b (systemOpen l E j) (systemOpenAdjunction l E j)
      (coefficientSequenceEvaluation l E U n) (coefficientSequenceEvaluation l E X n)
      (ordinaryEvaluation_eq l E U n) (ordinaryEvaluation_eq l E X n) d hd β hβ
  have hi : IsIso ((mateEquiv (systemOpenAdjunction l E j) c).symm β.inv) :=
    inverseMate_isIso_of_counit
      (systemOpenAdjunction l E j) c β.inv e he
  letI := hi
  exact IntegralSystemRealization.inverseMate_change_left
    (systemOpenAdjunction l E j) (systemOpenAdjunction l E j)
    (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j) c β.inv

end MateNormalization

/-- The open evaluation mate is invertible with the original open units.
Source: Zheng 4.10; Stacks 03DI
(blueprint: def-weil-system-operation-exchange-realization).
Proof: the ordinary direct-image equality is the identity on sections. Its
inverse-image mate satisfies the specified unit normalization. The ordinary open
evaluation theorem then gives a counit-normalized isomorphism; its inverse is
the inverse mate. Uniqueness of left adjoints retains this invertibility for the
specified finite open adjunction. Exact localization preserves inverse mates,
and the symmetry formula for the derived square identifies that localized map
with systemOpenEvaluationInv. This covers empty opens and unbounded complexes. -/
theorem systemOpenEvaluationInv_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : IsIso (systemOpenEvaluationInv l E j n) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  letI := sfIntrinsicPullback_additive A j
  letI := sfIntrinsicPullback_preservesFiniteLimits A j
  letI := sfIntrinsicPullback_preservesFiniteColimits A j
  letI := sfIntrinsicExtensionByZero_additive j A
  letI := sfIntrinsicExtensionByZero_preservesFiniteLimits j A
  letI := sfIntrinsicExtensionByZero_preservesFiniteColimits j A
  letI := coefficientSequenceEvaluation_additiveInstance l E U n
  letI := coefficientSequenceEvaluation_additiveInstance l E X n
  letI := coefficientSequenceEvaluation_limits l E U n
  letI := coefficientSequenceEvaluation_limits l E X n
  letI := coefficientSequenceEvaluation_colimits l E U n
  letI := coefficientSequenceEvaluation_colimits l E X n
  let β := @asIso _ _ _ _ (systemPullEvaluationOrdinaryInv l E j n)
    (systemPullEvaluationOrdinaryInv_isIso l E j n)
  letI : IsIso ((mateEquiv (systemOpenAdjunction l E j)
      (sfIntrinsicOpenAdjunction A j)).symm
      (TwoSquare.mk _ _ _ _ β.symm.hom)) := by
    simpa only [β, A, Iso.symm_hom] using systemOpenEvaluationOrdinaryInv_isIso l E j n
  have hi := (exact_localization_inverse_mate (systemOpenAdjunction l E j)
    (sfIntrinsicOpenAdjunction A j) β.symm).1
  have he : (Functor.mapDerivedCategorySquareIso β.symm).hom =
      (systemPullEvaluation l E j n).inv := by
    dsimp only [Functor.mapDerivedCategorySquareIso, systemPullEvaluation]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc, β]
  rw [he] at hi
  exact hi

end OpenEvaluationProof

/-- Finite evaluation of the actual compact system, fixed by both adjunction mates.
Source: Bhatt--Scholze 6.7.6; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization). -/
def compactFiniteEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    reduction l E X ⋙ (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        coefficientSequenceDerivedEvaluation l E Y n ≅
      scalarReductionDerivedExtension l E X n ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) := by
  letI := systemDirectEvaluation_isIso l E c.g n
  letI := systemOpenEvaluationInv_isIso l E c.i n
  exact isoWhiskerLeft (reduction l E X ⋙ systemDerivedOpen l E c.i)
      (asIso (systemDirectEvaluation l E c.g n)) ≪≫
    isoWhiskerRight (isoWhiskerLeft (reduction l E X)
      (asIso (systemOpenEvaluationInv l E c.i n)).symm)
        (proEtaleConstantDerivedDirectImage c.g
          (Padic.coefficientExtensionRing l E (n + 1))) ≪≫
    isoWhiskerRight (((models l E).system X).reductionEvaluation n)
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))

/-! The specified finite evaluations agree with the native varying-ring evaluations.
The two presentations of the strict coefficient systems are definitionally equal, but the
elaborator's unifier cannot compare their adjunction mates in reasonable time; these
comparisons are left to the kernel with `exact_by_kernel`. -/

/-- The section-normalized ordinary direct-image evaluation is the native one,
in finite intrinsic coordinates: both are the identity on sections.
Source: Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
private theorem systemDirectEvaluationOrdinary_eqToIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) :
    (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).hom =
      (compactSupportOrdinaryDirectEvaluation l E f n).hom := by
  exact_by_kernel eqToIso_directEvaluation l E f n (systemDirectEvaluationOrdinary_eq l E f n)

/-- The ordinary pullback evaluation is the native one, in intrinsic coordinates.
Source: Zheng 4.1; Stacks 03D2
(blueprint: def-weil-system-operation-exchange-realization). -/
private theorem systemPullEvaluationOrdinaryInv_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    systemPullEvaluationOrdinaryInv l E f n =
      Functor.whiskerLeft (ProEtale.VaryingRing.eval (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) Y n)
          (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f).inv ≫
        (ProEtale.VaryingRing.moduleEvalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f n).inv := by
  unfold systemPullEvaluationOrdinaryInv
  rw [systemDirectEvaluationOrdinary_eqToIso_hom]
  exact_by_kernel pullEvaluationMate_eq l E f n

/-- The derived pullback evaluation is the native `evalG`, in intrinsic coordinates.
Source: Zheng 4.1; Stacks 03D2
(blueprint: def-weil-system-operation-exchange-realization). -/
private theorem systemPullEvaluation_inv_app {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceDerived l E Y) :
    (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f n).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso
        (openSquarePullbackModel (Padic.coefficientExtensionRing l E (n + 1)) f)).hom.app
          ((coefficientSequenceDerivedEvaluation l E Y n).obj M) =
      (systemPullEvaluation l E f n).inv.app M := by
  exact_by_kernel pullEvaluation_derived l E f n
    (by exact_by_kernel @asIso _ _ _ _ _ (systemPullEvaluationOrdinaryInv_isIso l E f n))
    (by exact_by_kernel systemPullEvaluationOrdinaryInv_eq l E f n) M

/-- The system direct-image evaluation is the native `evalP`, in intrinsic coordinates.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
private theorem systemDirectEvaluation_app {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceDerived l E X) :
    letI := proEtaleConstantModuleDirectImage_additive f
      (Padic.coefficientExtensionRing l E (n + 1))
    (systemDirectEvaluation l E f n).app M =
      (ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) f n ≪≫
        isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
          (compactSupportDirectModel f (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
            M := by
  exact_by_kernel directEvaluationMate_eq l E f n
    (by exact_by_kernel systemPullEvaluation l E f n)
    (by exact_by_kernel systemPullEvaluation_inv_app l E f n) M

/-- The system open-extension evaluation is the native `evalJ`, in intrinsic coordinates.
Source: Stacks 03DI; Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
private theorem systemOpenEvaluationInv_inv_app {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) (M : coefficientSequenceDerived l E U) :
    letI := systemOpenEvaluationInv_isIso l E j n
    letI := sfIntrinsicExtensionByZero_additive j (Padic.coefficientExtensionRing l E (n + 1))
    letI := (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (n + 1))).2.1
    letI := (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (n + 1))).2.2
    (asIso (systemOpenEvaluationInv l E j n)).symm.hom.app M =
      (ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n ≪≫
        isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
          (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1))))).hom.app M := by
  let := systemOpenEvaluationInv_isIso l E j n
  exact_by_kernel openEvaluationMate_eq l E j n
    (by exact_by_kernel systemPullEvaluation l E j n)
    (by exact_by_kernel systemPullEvaluation_inv_app l E j n)
    (by exact_by_kernel (asIso (systemOpenEvaluationInv l E j n)).symm)
    (by exact_by_kernel (rfl : systemOpenEvaluationInv l E j n = systemOpenEvaluationInv l E j n))
    M

/-- The specified compact-system evaluation is the native compact-support evaluation.
Source: Bhatt--Scholze 6.7.6; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization). -/
private theorem compactFiniteEvaluation_hom_app {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) (K : DerivedCategory (scalarReductionSource l E X)) :
    (compactFiniteEvaluation l E c n).hom.app K =
      (isoWhiskerLeft ((models l E).system X).reduction
          (compactSupportSystemEvaluation l E c n) ≪≫
        isoWhiskerRight (((models l E).system X).reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))).hom.app
            K := by
  let := systemDirectEvaluation_isIso l E c.g n
  let := systemOpenEvaluationInv_isIso l E c.i n
  have hP : (systemDirectEvaluation l E c.g n).app
      ((reduction l E X ⋙ systemDerivedOpen l E c.i).obj K) = _ :=
    systemDirectEvaluation_app l E c.g n
      ((systemDerivedOpen l E c.i).obj ((reduction l E X).obj K))
  have hJ := systemOpenEvaluationInv_inv_app l E c.i n ((reduction l E X).obj K)
  simp only [compactFiniteEvaluation, compactSupportSystemEvaluation, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, asIso_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Iso.symm_hom] at hP hJ
  rw [hP, ← hJ]
  simp only [Category.assoc]
  rfl_by_kernel

/-- The inverse open exchange is the left mate of the inverse pullback square.
Source: Zheng 4.10; blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenExchangeInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (gU : U ⟶ U) (gX : X ⟶ X) (w : gU ≫ j = j ≫ gX) :
    integralComparisonDerivedSequencePullback l E gU ⋙ systemDerivedOpen l E j ⟶
      systemDerivedOpen l E j ⋙ integralComparisonDerivedSequencePullback l E gX :=
  ((mateEquiv (systemDerivedOpenAdjunction l E j) (systemDerivedOpenAdjunction l E j)).symm
    (TwoSquare.mk _ _ _ _ (systemSquare l E j gU gX w).inv))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The open mate is invertible for a Cartesian open square.
Source: Stacks 03S6; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization).
Proof: on the localized vertical site the open-adjunction mate is the identity
on the pulled-back open and the unique map between zero values off that open.
The Cartesian condition identifies these opens, giving the inverse sectionwise.
This is a map of whole systems, since both maps commute with quotient restrictions.
Exact descent gives an inverse in the ordinary derived category before evaluation. -/
theorem systemOpenExchangeInv_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (gU : U ⟶ U) (gX : X ⟶ X)
    (sq : IsPullback gU j j gX) :
    IsIso (systemOpenExchangeInv l E j gU gX sq.w) := by
  unfold systemOpenExchangeInv systemSquare
  exact integralInverseOpenMate_isIso l E j gU gX sq
    (systemDerivedOpenAdjunction l E j)

/-- The canonical open-system exchange, inverse to the specified open-adjunction mate.
Source: Stacks 03S6; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenExchange {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (gU : U ⟶ U) (gX : X ⟶ X) (sq : IsPullback gU j j gX) :
    systemDerivedOpen l E j ⋙ integralComparisonDerivedSequencePullback l E gX ≅
      integralComparisonDerivedSequencePullback l E gU ⋙ systemDerivedOpen l E j :=
  (@asIso _ _ _ _ (systemOpenExchangeInv l E j gU gX sq.w)
    (systemOpenExchangeInv_isIso l E j gU gX sq)).symm

/-- The compactification-relative system composite: proper mate, then proper image
of open exchange, using the same compactification at every quotient level.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemCompactExchange {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB) :
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        integralComparisonDerivedSequencePullback l E gY ⟶
      integralComparisonDerivedSequencePullback l E gX ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) :=
  whiskerLeft (systemDerivedOpen l E c.i) (systemExchange l E c.g gB gY wp) ≫
    whiskerRight (systemOpenExchange l E c.i gX gB sj).hom (systemDirect l E c.g)

section ScalarSystems
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The scalar realization uses the same single global normalized system as models.
Source: Stacks 06YY, 0941 (blueprint: def-weil-system-operation-exchange-realization). -/
def scalarModels : IntegralComparisonScalarData l E L ι (models l E) (models l L) :=
  ((integralPullbackComparisonRealization l (ULift.{u} ℚ_[l]) (ULift.{u} ℚ_[l])
    (AlgHom.id ℚ_[l] (ULift.{u} ℚ_[l]))).choose).scalar E L ι

/-- Coefficient change of direct image is the actual mate of normalized tensor pullback.
It is formed on whole strict systems, before any evaluation or inverse limit.
Source: proposition-six-operations-change-coefficients; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemDirectScalar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    systemDirect l E f ⋙ integralComparisonDerivedSequenceScalar l E L ι Y ⟶
      integralComparisonDerivedSequenceScalar l E L ι X ⋙ systemDirect l L f :=
  (mateEquiv (systemAdjunction l E f) (systemAdjunction l L f)
    (TwoSquare.mk _ _ _ _ (integralComparisonSystemScalarPullback l E L ι f).inv))

/-- The inverse open coefficient exchange is the actual left-adjunction mate.
Source: Zheng 4.1, 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenScalarInv {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    integralComparisonDerivedSequenceScalar l E L ι X ⋙ systemDerivedOpen l L j ⟶
      systemDerivedOpen l E j ⋙ integralComparisonDerivedSequenceScalar l E L ι B :=
  ((mateEquiv (systemDerivedOpenAdjunction l E j)
    (systemDerivedOpenAdjunction l L j)).symm
    (TwoSquare.mk _ _ _ _ (integralComparisonSystemScalarPullback l E L ι j).hom))

/-- Tensor extension commutes with the specified exact open extension, componentwise.
Source: Zheng 4.1, 4.10; Stacks 03DI
(blueprint: lem-weil-system-open-scalar-inv-app-is-iso).
The component calculation is the finite coefficient mate calculation; its
remaining proof is isolated so the natural-transformation statement below is
obtained by the standard componentwise criterion. -/
theorem systemOpenScalarInv_app_isIso {X B : Scheme.{u}} (j : X ⟶ B)
    [IsOpenImmersion j] (K : coefficientSequenceDerived l E X) :
    IsIso ((systemOpenScalarInv l E L ι j).app K) := by
  have := systemScalarPullback_leftMate_isIso l E L ι j
    (systemDerivedOpenAdjunction l E j) (systemDerivedOpenAdjunction l L j)
  exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ (systemOpenScalarInv l E L ι j) this K

/-- Tensor extension commutes with the specified exact open extension.
Source: Zheng 4.1, 4.10; Stacks 03DI
(blueprint: def-weil-system-operation-exchange-realization).
Proof: apply the componentwise invertibility result to the natural transformation. -/
theorem systemOpenScalarInv_isIso {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    IsIso (systemOpenScalarInv l E L ι j) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro K
  exact systemOpenScalarInv_app_isIso l E L ι j K

/-- The forward open scalar comparison is the inverse of that specified mate.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenScalar {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :=
  letI := systemOpenScalarInv_isIso l E L ι j
  (asIso (systemOpenScalarInv l E L ι j)).symm

/-- The proper/open scalar comparison uses the same compactification at every level.
Source: proposition-six-operations-change-coefficients, compact-support paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemCompactScalar {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        integralComparisonDerivedSequenceScalar l E L ι Y ⟶
      integralComparisonDerivedSequenceScalar l E L ι X ⋙
        (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g) :=
  whiskerLeft (systemDerivedOpen l E c.i) (systemDirectScalar l E L ι c.g) ≫
    whiskerRight (systemOpenScalar l E L ι c.i).hom (systemDirect l L c.g)

/-- Canonical alpha for coefficient change of an actual system operation.
Source: Stacks 06YY, 0941 (blueprint: def-weil-system-operation-exchange-realization). -/
def scalarSourceComparison {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y) :
    realize l E H ⋙ integralScalarExtensionOfUniverses l E L ι Y ⟶
      reduction l E X ⋙ H ⋙ integralComparisonDerivedSequenceScalar l E L ι Y ⋙
        coefficientSequenceLimit l L Y :=
  whiskerLeft (realize l E H) ((scalarModels l E L ι).model Y).realization.hom ≫
    whiskerRight
      (whiskerRight
        (whiskerLeft (reduction l E X ⋙ H) ((models l E).system Y).adjunction.counit)
        (integralComparisonDerivedSequenceScalar l E L ι Y))
      (coefficientSequenceLimit l L Y)

/-- Whole-system effectivity of the specified coefficient-reduction counit.
Source: Stacks 06YY, 0941 (blueprint: def-weil-system-operation-exchange-realization). -/
def scalarReductionIso (X : Scheme.{u}) :
    (sfIntegralConstructible l E X).ι ⋙ integralScalarExtensionOfUniverses l E L ι X ⋙
        reduction l L X ≅
      (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        integralComparisonDerivedSequenceScalar l E L ι X := by
  let t := whiskerLeft (sfIntegralConstructible l E X).ι
    (integralComparisonScalarCounit l E L ι X ((models l E).system X)
      ((models l L).system X) ((models l L).roos X) ((scalarModels l E L ι).model X))
  letI : ∀ K : sfIntegralConstructibleCategory l E X, IsIso (t.app K) :=
    fun K ↦ (scalarModels l E L ι).effective X K
  letI := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- Realize a specified coefficient-system mate, rather than lift finite evaluations.
Source: proposition-six-operations-change-coefficients; Stacks 06YY, 0941
(blueprint: def-weil-system-operation-exchange-realization). -/
def coefficientExchange {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y)
    (H' : coefficientSequenceDerived l L X ⥤ coefficientSequenceDerived l L Y)
    (e : H ⋙ integralComparisonDerivedSequenceScalar l E L ι Y ⟶
      integralComparisonDerivedSequenceScalar l E L ι X ⋙ H') :
    (sfIntegralConstructible l E X).ι ⋙ realize l E H ⋙
        integralScalarExtensionOfUniverses l E L ι Y ⟶
      (sfIntegralConstructible l E X).ι ⋙ integralScalarExtensionOfUniverses l E L ι X ⋙
        realize l L H' :=
  whiskerLeft (sfIntegralConstructible l E X).ι (scalarSourceComparison l E L ι H) ≫
    whiskerRight (whiskerLeft ((sfIntegralConstructible l E X).ι ⋙ reduction l E X) e)
      (coefficientSequenceLimit l L Y) ≫
    whiskerRight (scalarReductionIso l E L ι X).inv (H' ⋙ coefficientSequenceLimit l L Y)

end ScalarSystems

end Systems

section ConstructibleOperations
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [fo : f.IsOver (Spec (.of K₀))]

include hl xo yo xft xqc yft yqc fo

/-- The integral direct-image construction is the recorded Roos object, not a
replacement functor inferred from its reductions.
Source: blueprint integral direct-image paragraph; Stacks 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: evaluate the derived system direct image by the normalized sectionwise
adjunction. The quotient maps become exactly sfDirectImageTransition. Restrict
scalars and use the total-limit Roos triangle, with its specified projections.
This gives the displayed SfIntegralDirectImage presentation with the same object.
Countable products exist by the completed-module Grothendieck construction. -/
theorem directImage_roos (K : sfIntegralConstructibleCategory l E X) :
    ∃ hprod : HasProduct (sfDirectImageTerm l E f K.obj),
      ∃ M : @SfIntegralDirectImage l _ E _ _ _ X Y f K.obj hprod,
        M.obj = (integralDirectImage l E f).obj K.obj := by
  obtain ⟨hprod, L, e, _a, _ha⟩ :=
    WeilConjectures.systemDirectImage_roosPresentation l E f ((models l E).system X) K.obj
  let _ := hprod
  let N := (coefficientSequenceLimit l E Y).obj
    ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
      (((models l E).system X).reduction.obj K.obj))
  let p := e.hom ≫ L.projection
  let δ := L.boundary ≫ (shiftFunctor _ (1 : ℤ)).map e.inv
  have hroos : IsDerivedLimitTriangle (sfDirectImageTransition l E f K.obj)
      N p δ  := derivedLimitTriangleTransport
    (sfDirectImageTransition l E f K.obj) e L.projection L.boundary L.roos
  let M : @SfIntegralDirectImage l _ E _ _ _ X Y f K.obj hprod :=
    { obj := N, projection := p, boundary := δ, roos := hroos }
  refine ⟨hprod, M, ?_⟩
  rfl

/-- The simultaneous direct-image realization is bounded constructible.
Source: blueprint integral direct-image paragraph; Bhatt--Scholze 6.5, 6.7
(blueprint: def-weil-system-operation-exchange-realization).
Proof: derive the actual system direct image on a single system resolution.
Evaluation is its canonical finite direct image, including the scalar-transition
mates, by the finite left adjoints to evaluation. Exact scalar restriction and
the canonical total-limit projections identify the resulting object with the
Roos triangle of SfIntegralDirectImage. Apply
lem-sf-integral-direct-image-constructible, including its empty-scheme case. -/
theorem directImage_constructible (K : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructible l E Y ((integralDirectImage l E f).obj K.obj) := by
  obtain ⟨hprod, M, hM⟩ := directImage_roos l E K₀ hl f K
  let := hprod
  exact hM ▸ ((sfIntegralDirectImage_constructible K₀ l hl E f K.obj K.property).2.1 M).1

/-- The actual direct-image action on the recorded full constructible categories.
Source: blueprint integral direct-image paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
def directImageFunctor :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfIntegralConstructible l E Y).lift
    ((sfIntegralConstructible l E X).ι ⋙ integralDirectImage l E f)
    (directImage_constructible l E K₀ hl f)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Additivity and constant-coefficient linearity of the actual direct-image action.
Source: blueprint scalar-localization paragraph
(blueprint: def-weil-system-operation-exchange-realization).
Proof: reduction, the sectionwise system direct image and exact scalar restriction
commute with addition and the constant O_E action. Derive these identities and
pass through the total-limit universal map. The full inclusion reflects them. -/
theorem directImage_linear :
    (directImageFunctor l E K₀ hl f).Additive ∧
      (directImageFunctor l E K₀ hl f).Linear (Padic.coefficientExtensionIntegers l E) := by
  have : (coefficientSequenceLimit l E X).Additive := by
    dsimp only [coefficientSequenceLimit, coefficientConstantTowerLimit,
      coefficientSequenceDerivedRestriction]
    infer_instance
  have : (coefficientSequenceLimit l E Y).Additive := by
    dsimp only [coefficientSequenceLimit, coefficientConstantTowerLimit,
      coefficientSequenceDerivedRestriction]
    infer_instance
  have : (reduction l E X).Additive := ((models l E).system X).adjunction.left_adjoint_additive
  have : (systemDirect l E f).Additive := by
    dsimp only [systemDirect]
    infer_instance
  have : (integralDirectImage l E f).Additive := by
    dsimp only [integralDirectImage, realize]
    infer_instance
  refine ⟨?_, ?_⟩
  · constructor
    intro K M a b
    apply ObjectProperty.hom_ext
    exact (integralDirectImage l E f).map_add (f := a.hom) (g := b.hom)
  · let R := Padic.coefficientExtensionIntegers l E
    let := compactSupportScalarLinear l E X
    let := compactSupportScalarLinear l E Y
    let := compactSupportSequenceLinear l E X
    let := compactSupportSequenceLinear l E Y
    let := DerivedCategory.instLinear R (scalarReductionSource l E X)
    let := DerivedCategory.instLinear R (scalarReductionSource l E Y)
    let := DerivedCategory.instLinear R (coefficientSequenceModules l E X)
    let := DerivedCategory.instLinear R (coefficientSequenceModules l E Y)
    let := DerivedCategory.instLinear R (ℕᵒᵖ ⥤ scalarReductionSource l E X)
    let := DerivedCategory.instLinear R (ℕᵒᵖ ⥤ scalarReductionSource l E Y)
    have := compactSupportSequenceRestrictionLinear l E X
    have := compactSupportSequenceRestrictionLinear l E Y
    have := compactSupportLimitLinear l E X
    have := compactSupportLimitLinear l E Y
    have : (integralComparisonSequenceDirectImage l E f).Linear R :=
      compactSupportSystemPushLinear l E f
    have : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
        scalarReductionSource l E X).rightDerivedFunctor.Linear R :=
      compactSupportRightDerivedLinear _ _
    have : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
        scalarReductionSource l E Y).rightDerivedFunctor.Linear R :=
      compactSupportRightDerivedLinear _ _
    have : (coefficientSequenceLimit l E X).Linear R := by
      unfold coefficientSequenceLimit coefficientConstantTowerLimit
        coefficientSequenceDerivedRestriction
      infer_instance
    have : (coefficientSequenceLimit l E Y).Linear R := by
      unfold coefficientSequenceLimit coefficientConstantTowerLimit
        coefficientSequenceDerivedRestriction
      infer_instance
    have : (reduction l E X).Linear R := ((models l E).system X).adjunction.left_adjoint_linear
    have : (systemDirect l E f).Linear R := compactSupportRightDerivedLinear _ _
    have h : (integralDirectImage l E f).Linear R := by
      dsimp only [integralDirectImage, realize]
      infer_instance
    change @Functor.Linear R _ _ _ _ _ _ _
      (DerivedCategory.instLinear R (scalarReductionSource l E X))
      (DerivedCategory.instLinear R (scalarReductionSource l E Y)) (integralDirectImage l E f)
        at h
    rw [normalizedDerivedLinear l E X (compactSupportScalarLinear l E X)
        (compactSupportScalarLinear_normalized l E X),
      normalizedDerivedLinear l E Y (compactSupportScalarLinear l E Y)
        (compactSupportScalarLinear_normalized l E Y)] at h
    constructor
    intro K M a r
    apply ObjectProperty.hom_ext
    exact h.map_smul a.hom r

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Integral direct exchange: the constructed whole-system mate, realized by
beta, total derived limit and alpha, on its bounded constructible domain.
The semilinear horizontal arrows have no K₀-linearity assumption.
Source: blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def directIntegral (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (w : gX ≫ f = f ≫ gY) :
    directImageFunctor l E K₀ hl f ⋙ constructibleIntegralPullback l E gY ⟶
      constructibleIntegralPullback l E gX ⋙ directImageFunctor l E K₀ hl f where
  app K := ObjectProperty.homMk
    ((integralExchange l E (systemDirect l E f) gX gY
      (systemExchange l E f gX gY w)).app K)
  naturality _K _L a := ObjectProperty.hom_ext _
    ((integralExchange l E (systemDirect l E f) gX gY
      (systemExchange l E f gX gY w)).naturality a)

variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The actual integral chosen-compactification operation on simultaneous systems.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def compactImage (c : Compactification f) :=
  realize l E (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)

/-- Fix the comparison with the recorded integral Rf_! by its actual Roos projections.
Both sides use this one compactification and the positive exponent n+1.
Source: Bhatt--Scholze 6.7.6; sfQcqsCompactSupportRealization normalization
(blueprint: def-weil-system-operation-exchange-realization). -/
def CompactRealizationSpec (c : Compactification f)
    (τ : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ compactImage l E f c) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E Y n).map (τ.hom.app K) ≫
        (((models l E).system Y).reductionEvaluation n).inv.app
          ((compactImage l E f c).obj K.obj) ≫
        (coefficientSequenceDerivedEvaluation l E Y n).map
          ((operationReduction l E (systemDerivedOpen l E c.i ⋙
            systemDirect l E c.g)).app K.obj) ≫
        (compactFiniteEvaluation l E c n).hom.app K.obj =
      (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom

/-- There is a projection-normalized identification of the recorded Rf_! with the
simultaneous system realization, on the entire constructible category.
Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: the strict reduction comparison of the recorded compact-support functor with the
native compact-support system has the finite projections of
sfCompactSupportFiniteReductionIso. The native system is the specified one, and its native
finite evaluation is compactFiniteEvaluation. Transposing the projection equation under the
finite scalar adjunction, using the evaluated reduction counit, gives the specification. -/
theorem compactRealization_exists (c : Compactification f) :
    ∃ τ : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ compactImage l E f c,
      CompactRealizationSpec l E K₀ hl f c τ := by
  obtain ⟨γ, hγ⟩ := qcqsCompactSupport_strictReductionGamma l E K₀ hl c
    ((models l E).system X) ((models l E).system Y)
  refine ⟨by exact_by_kernel γ, fun K n ↦ ?_⟩
  exact_by_kernel map_comp_counit_eq_of_projection (coefficientFiniteAdjunction l E Y n)
    ((models l E).system Y).adjunction (coefficientSequenceProjection l E Y n)
    (((models l E).system Y).reductionEvaluation n)
    (fun N ↦ ((models l E).system Y).counit_projection N n)
    (by exact_by_kernel γ.hom.app K)
    (by exact_by_kernel (compactFiniteEvaluation l E c n).hom.app K.obj)
    (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom
    (by
      rw [compactFiniteEvaluation_hom_app]
      exact_by_kernel hγ K n)

/-- Uniqueness of the projection-normalized identification, given that the shifted Hom
groups from the recorded Rf_! into its finite restricted reductions are finite. Derived
completeness of the target holds since it is isomorphic to a constructible object.
Over a finite field `K₀` the finiteness is
the finiteness of étale cohomology of constructible complexes (SGA 4½, Th. finitude); over an
arbitrary field it can fail, so no general uniqueness statement is made; `compactRealization`
takes its witness from `compactRealization_exists`.
Source: Stacks, Lemma map-into-Rlim
(blueprint: def-weil-system-operation-exchange-realization).
Proof: both normalizations give the same reduction of each component, after cancelling the
composite of the inverse reduction evaluation, the operation reduction and the finite
evaluation, which is invertible since the reduction of `τ` is. Reductions detect maps into a
derived-complete object with finite shifted reduction Hom groups. -/
theorem compactRealization_unique_of_finite (c : Compactification f)
    (hfin : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ), Finite
      (((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj⟦(1 : ℤ)⟧ ⟶
        (sfDerivedReductionRestricted l E Y n).obj ((compactImage l E f c).obj K.obj)))
    (τ τ' : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ compactImage l E f c)
    (hτ : CompactRealizationSpec l E K₀ hl f c τ)
    (hτ' : CompactRealizationSpec l E K₀ hl f c τ') : τ' = τ := by
  have := sfIntegralConstructible_isClosedUnderIsomorphisms l E Y
  obtain ⟨σ, -⟩ := compactRealization_exists l E K₀ hl f c
  ext K
  have hQ : IsSfDerivedComplete l E Y ((compactImage l E f c).obj K.obj) :=
    ((sfIntegralConstructible l E Y).prop_of_iso (σ.app K)
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property).1
  refine derivedComplete_finiteReduction_ext l E Y hQ (hfin K) _ _ fun n ↦ ?_
  have h := hτ K n
  have h' := hτ' K n
  rw [← h] at h'
  have : IsIso ((scalarReductionDerivedExtension l E Y n).map (τ.hom.app K)) :=
    inferInstanceAs (IsIso ((scalarReductionDerivedExtension l E Y n).mapIso
      (τ.app K)).hom)
  have : IsIso ((((models l E).system Y).reductionEvaluation n).inv.app
        ((compactImage l E f c).obj K.obj) ≫
      (coefficientSequenceDerivedEvaluation l E Y n).map
        ((operationReduction l E (systemDerivedOpen l E c.i ⋙
          systemDirect l E c.g)).app K.obj) ≫
      (compactFiniteEvaluation l E c n).hom.app K.obj) := by
    rw [(IsIso.eq_inv_comp _).2 h]
    infer_instance
  exact (cancel_mono _).1 h'

/-- The identification determined by the actual integral compact-support projections.
Source: Bhatt--Scholze 6.7.6 (blueprint: def-weil-system-operation-exchange-realization). -/
def compactRealization (c : Compactification f) :=
  (compactRealization_exists l E K₀ hl f c).choose

/-- Alpha-shriek starts at the recorded integral Rf_!, uses its uniquely normalized
identification, then the actual system pullback realization and counit.
Source: blueprint alpha-shriek (blueprint: def-weil-system-operation-exchange-realization). -/
def compactAlpha (c : Compactification f) (gY : Y ⟶ Y) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E gY ⟶
      (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        integralComparisonDerivedSequencePullback l E gY ⋙ coefficientSequenceLimit l E Y :=
  whiskerRight (compactRealization l E K₀ hl f c).hom (integralDerivedPullback l E gY) ≫
    whiskerLeft (sfIntegralConstructible l E X).ι
      (sourceComparison l E (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) gY)

/-- Beta-shriek is the effective pullback counit inverse followed by the inverse
of that same projection-normalized Rf_! identification, on the pulled input.
Source: blueprint beta-shriek (blueprint: def-weil-system-operation-exchange-realization). -/
def compactBeta (c : Compactification f) (gX : X ⟶ X) :
    (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        integralComparisonDerivedSequencePullback l E gX ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙ coefficientSequenceLimit l E Y ⟶
      constructibleIntegralPullback l E gX ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ (sfIntegralConstructible l E Y).ι :=
  whiskerRight (reductionPullbackIso l E gX).inv
      ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙ coefficientSequenceLimit l E Y) ≫
    whiskerLeft (constructibleIntegralPullback l E gX)
      (compactRealization l E K₀ hl f c).inv

/-- Reduction of the recorded operation, transported by the fixed identification.
Source: blueprint compact operation comparisons
(blueprint: def-weil-system-operation-exchange-realization). -/
def compactOperationReduction (c : Compactification f) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ⋙ reduction l E Y ⟶
      (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) :=
  whiskerRight (compactRealization l E K₀ hl f c).hom (reduction l E Y) ≫
    whiskerLeft (sfIntegralConstructible l E X).ι
      (operationReduction l E (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g))

/-- Integral compact exchange: proper system mate followed by the system open
exchange, then the single specified total-limit realization composite.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def compactIntegralAmbient (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E gY ⟶
      constructibleIntegralPullback l E gX ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ (sfIntegralConstructible l E Y).ι :=
  compactAlpha l E K₀ hl f c gY ≫
    whiskerRight
      (whiskerLeft ((sfIntegralConstructible l E X).ι ⋙ reduction l E X)
        (systemCompactExchange l E c gX gB gY wp sj)) (coefficientSequenceLimit l E Y) ≫
    compactBeta l E K₀ hl f c gX

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Integral compact exchange on the recorded integral compact-support functor.
Its underlying map is exactly alpha-shriek, L(e), beta-shriek above.
Source: blueprint FrEx-shriek (blueprint: def-weil-system-operation-exchange-realization). -/
def compactIntegral (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ constructibleIntegralPullback l E gY ⟶
      constructibleIntegralPullback l E gX ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c E where
  app K := ObjectProperty.homMk
    ((compactIntegralAmbient l E K₀ hl f c gX gB gY wp sj).app K)
  naturality K M a := by
    apply ObjectProperty.hom_ext
    have h := (compactIntegralAmbient l E K₀ hl f c gX gB gY wp sj).naturality a
    simpa only [Functor.comp_map, constructibleIntegralPullback, ObjectProperty.lift,
      ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, id_eq, Functor.comp_obj, ObjectProperty.ι_obj] using h

attribute [local irreducible] models
attribute [local irreducible] compactRealization
attribute [local implicit_reducible] compactImage realize constructibleIntegralPullback
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Reduction of the constructed compact exchange is the specified proper/open
system composite through the same operation and pullback counits.
Source: blueprint integral compact-support paragraph
(blueprint: def-weil-system-operation-exchange-realization).
Proof: specialize the general integral exchange counit equation to the proper/open
system composite. Transport it through the fixed compact realization at the input
and its pullback. Functoriality cancels the inverse and forward realization at the
output; naturality of the pullback/reduction counit transports the source.
The component formulas for compact alpha, beta and operation reduction identify
this equation with the one displayed here. -/
theorem compactIntegral_reduction (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)
    (K : sfIntegralConstructibleCategory l E X) :
    let H := systemDerivedOpen l E c.i ⋙ systemDirect l E c.g
    (reduction l E Y).map ((compactIntegral l E K₀ hl f c gX gB gY wp sj).app K).hom ≫
        (compactOperationReduction l E K₀ hl f c).app
          ((constructibleIntegralPullback l E gX).obj K) ≫
        H.map ((reductionPullbackIso l E gX).hom.app K) =
      (reductionPullbackIso l E gY).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K) ≫
        (integralComparisonDerivedSequencePullback l E gY).map
          ((compactOperationReduction l E K₀ hl f c).app K) ≫
        (systemCompactExchange l E c gX gB gY wp sj).app ((reduction l E X).obj K.obj) := by
  let H := systemDerivedOpen l E c.i ⋙ systemDirect l E c.g
  let e := systemCompactExchange l E c gX gB gY wp sj
  let τ := compactRealization l E K₀ hl f c
  let Q := (constructibleIntegralPullback l E gX).obj K
  let κ := integralComparisonPullbackCounit l E gY ((models l E).system Y)
    ((models l E).system Y) ((models l E).roos Y) ((models l E).pullback gY)
  have h := integralExchange_reduction l E H gX gY e K
  have ht := transport_reduction_equation (reduction l E Y)
    (integralDerivedPullback l E gY) (integralComparisonDerivedSequencePullback l E gY)
    κ (τ.hom.app K) (τ.hom.app Q) (τ.inv.app Q) (τ.inv_hom_id_app Q)
    ((integralExchange l E H gX gY e).app K)
    ((operationReduction l E H).app Q.obj ≫ H.map ((reductionPullbackIso l E gX).hom.app K))
    ((integralComparisonDerivedSequencePullback l E gY).map
      ((operationReduction l E H).app K.obj) ≫ e.app ((reduction l E X).obj K.obj))
    (by simpa only [Q, constructibleIntegralPullback, ObjectProperty.lift,
      Functor.comp_obj, ObjectProperty.ι_obj, κ, compactImage, H, Category.assoc] using h)
  have hκ : (reductionPullbackIso l E gY).hom.app
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K) =
      κ.app ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj := by
    simp only [reductionPullbackIso, asIso_hom, whiskerLeft_app, ObjectProperty.ι_obj, κ]
  have hop (T : sfIntegralConstructibleCategory l E X) :
      (compactOperationReduction l E K₀ hl f c).app T =
        (reduction l E Y).map (τ.hom.app T) ≫ (operationReduction l E H).app T.obj := by
    rfl
  have hexNat : compactIntegralAmbient l E K₀ hl f c gX gB gY wp sj =
      whiskerRight τ.hom (integralDerivedPullback l E gY) ≫
        integralExchange l E H gX gY e ≫
        whiskerLeft (constructibleIntegralPullback l E gX) τ.inv := by
    dsimp only [compactIntegralAmbient, compactAlpha, compactBeta, integralExchange,
      τ, H, e]
    simp only [Category.assoc]
  have hex : ((compactIntegral l E K₀ hl f c gX gB gY wp sj).app K).hom =
      (integralDerivedPullback l E gY).map (τ.hom.app K) ≫
        (integralExchange l E H gX gY e).app K ≫ τ.inv.app Q := by
    change (compactIntegralAmbient l E K₀ hl f c gX gB gY wp sj).app K = _
    rw [hexNat]
    rfl
  rw [hex, hop, hop, hκ]
  simpa only [Category.assoc, Functor.map_comp, Functor.comp_obj,
    ObjectProperty.ι_obj, H, e, Q] using ht

end ConstructibleOperations

end WeilConjectures.FrobeniusExchange

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.PoincareDuality.PullbackIdentitiesScalarExtension
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # Exact isomorphism transport at integral and field coefficient stages

Source: main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, sentence 1, through prose-10-20,
first paragraph (blueprint: def-pod-isomorphism-field-transport-clauses).

All functors, coefficient maps, scalar comparisons and quotient Hom constructors
below are the published constructions. The clause records specify comparisons,
rather than selecting arbitrary inverse equivalences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (ofHom inclusion)

/-- Clauses at one finite field, retaining the normalized lambda and epsilon and
localizing the latter on every rational object. Source: the integral and rational
paragraphs of the inverse automorphism argument
(blueprint: def-pod-isomorphism-field-transport-clauses). -/
structure IsomorphismFieldTransportStage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) where
  coefficient_projection : ∀ n : ℕ,
    inverseImageCompletedCoefficientMap l E g ≫
      limit.π (integralCoefficientSheafSystem l E X) (Opposite.op n) =
        inverseImageCompletedCoefficientComponent l E g n
  moduleEquivalence : (inverseImageIntegralModules l E g).IsEquivalence
  moduleAdditive : (inverseImageIntegralModules l E g).Additive
  moduleLimits : PreservesFiniteLimits (inverseImageIntegralModules l E g)
  moduleColimits : PreservesFiniteColimits (inverseImageIntegralModules l E g)
  moduleEpsilon : inverseImageIntegralModules l E g ⋙
    inverseImageIntegralModules l E (inv g) ≅ 𝟭 (integralTowerModules l E Y)
  module_epsilon_formula : ∀ M : integralTowerModules l E Y,
    moduleEpsilon.hom.app M = (pullbackIdentityModuleCounit l E g).hom.app M
  integralEquivalence : (constructibleIntegralPullback l E g).IsEquivalence
  integralShift : (constructibleIntegralPullback l E g).CommShift ℤ
  lambda : constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E Y).ι ⋙ inverseImageIntegralDerived l E g
  lambda_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (lambda.hom.app K) (pullbackIdentityLambda l E g hX hY K).hom
  lambda_shift :
    (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
      NatTrans.CommShift lambda.hom ℤ) (_s := integralShift)
  integralExact :
    (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
      (constructibleIntegralPullback l E g).IsTriangulated) (_s := integralShift)
  integralLinear : (constructibleIntegralPullback l E g).Linear
    (Padic.coefficientExtensionIntegers l E)
  epsilon : constructibleIntegralPullback l E g ⋙
    constructibleIntegralPullback l E (inv g) ≅ 𝟭 (sfIntegralConstructibleCategory l E Y)
  epsilon_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (epsilon.hom.app K).hom (pullbackIdentityEpsilon l E g K).hom
  rationalEquivalence : (rationalDerivedPullback l E g).IsEquivalence
  rationalShift : (rationalDerivedPullback l E g).CommShift ℤ
  rational_shift_formula : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (((rationalDerivedPullback l E g).commShiftIso
      (self := rationalShift) (1 : ℤ)).hom.app
        ((sfRationalConstructibleLocalization l E Y).obj K))
      ((sfRationalConstructibleLocalization l E X).map
        (((constructibleIntegralPullback l E g).commShiftIso
          (self := integralShift) (1 : ℤ)).hom.app K))
  rationalExact :
    (fun [_s : (rationalDerivedPullback l E g).CommShift ℤ] ↦
      (rationalDerivedPullback l E g).IsTriangulated) (_s := rationalShift)
  rationalAdditive : (rationalDerivedPullback l E g).Additive
  rational_object : ∀ K : sfRationalConstructibleCategory l E Y,
    (rationalDerivedPullback l E g).obj K =
      ⟨(constructibleIntegralPullback l E g).obj K.obj⟩
  rational_tensor : ∀ (K M : sfIntegralConstructibleCategory l E Y) (f : K ⟶ M)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    HEq ((rationalDerivedPullback l E g).map
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
        (sfRationalConstructibleLocalization l E Y).obj K ⟶
          (sfRationalConstructibleLocalization l E Y).obj M))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (constructibleIntegralPullback l E g).map f)
  rationalEpsilon : rationalDerivedPullback l E g ⋙ rationalDerivedPullback l E (inv g) ≅
    𝟭 (sfRationalConstructibleCategory l E Y)
  rational_epsilon_formula : ∀ K : sfRationalConstructibleCategory l E Y,
    HEq (rationalEpsilon.hom.app K)
      ((sfRationalConstructibleLocalization l E Y).map (epsilon.hom.app K.obj))

/-- The scalar inverse equation for the prescribed completed scalar/pullback maps.
Source: scalar paragraph, inverse automorphism argument
(blueprint: def-pod-isomorphism-field-transport-clauses). -/
def isomorphismFieldTransportScalarLaw
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq
      ((integralPullbackScalarComparison l E L ι (inv g)
          ((constructibleIntegralPullback l E g).obj K)).hom.hom ≫
        (integralDerivedPullback l L (inv g)).map
          (integralPullbackScalarComparison l E L ι g K).hom.hom ≫
        (pullbackIdentityEpsilon l L g
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K)).hom)
      ((integralScalarExtensionOfUniverses l E L ι Y).map
        (pullbackIdentityEpsilon l E g K).hom)

/-- Localization of the inverse/scalar equation on every rational object. Naturality
of the natural isomorphisms ranges over all localized arrows.
Source: rational and scalar paragraphs, inverse automorphism argument
(blueprint: def-pod-isomorphism-field-transport-clauses). -/
def isomorphismFieldTransportRationalScalarLaw
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (SE : IsomorphismFieldTransportStage l E g hX hY)
    (SL : IsomorphismFieldTransportStage l L g hX hY) : Prop :=
  ∀ K : sfRationalConstructibleCategory l E Y,
    (rationalPullbackScalarComparison l E L ι (inv g)).hom.app
        ((rationalDerivedPullback l E g).obj K) ≫
      (rationalDerivedPullback l L (inv g)).map
        ((rationalPullbackScalarComparison l E L ι g).hom.app K) ≫
      SL.rationalEpsilon.hom.app
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) =
    (sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map (SE.rationalEpsilon.hom.app K)

/-- Common-stage clauses use the actual quotient arrows and inclusion of the localized
finite-stage epsilon. Source: final common-stage paragraphs, inverse automorphism argument
(blueprint: def-pod-isomorphism-field-transport-clauses). -/
structure IsomorphismFieldTransportCommon
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hY) where
  equivalence : (commonStageDerivedPullback l Ω g).IsEquivalence
  shift : (commonStageDerivedPullback l Ω g).CommShift ℤ
  exact :
    (fun [_s : (commonStageDerivedPullback l Ω g).CommShift ℤ] ↦
      (commonStageDerivedPullback l Ω g).IsTriangulated) (_s := shift)
  additive : (commonStageDerivedPullback l Ω g).Additive
  stageComparison : ∀ E : Index l Ω,
    inclusion (Y := Y) E ⋙ commonStageDerivedPullback l Ω g ≅
      rationalDerivedPullback l (Coefficient.{u} l Ω E) g ⋙ inclusion (Y := X) E
  stage_comparison_formula : ∀ (E : Index l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
    HEq ((stageComparison E).hom.app K) (𝟙 ((commonStagePullbackObject l Ω g
      ((inclusion (Y := Y) E).obj K))))
  stage_shift : ∀ E : Index l Ω,
    @NatTrans.CommShift _ _ _ _ _ _ (stageComparison E).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _
        (inclusion (Y := Y) E) (commonStageDerivedPullback l Ω g) ℤ _ _ _ _
        (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
          (l := l) (Ω := Ω) (Y := Y) E) shift)
      (@Functor.CommShift.comp _ _ _ _ _ _
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) g) (inclusion (Y := X) E)
        ℤ _ _ _ _ (S E).rationalShift
        (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
          (l := l) (Ω := Ω) (Y := X) E))
  object_formula : ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
    (commonStageDerivedPullback l Ω g).obj P = commonStagePullbackObject l Ω g P
  arrow_formula : ∀ (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
    (f : P.toStage hP ⟶ Q.toStage hQ),
    HEq ((commonStageDerivedPullback l Ω g).map (ofHom P Q L hP hQ f))
      (ofHom (commonStagePullbackObject l Ω g P) (commonStagePullbackObject l Ω g Q)
        L hP hQ ((commonStagePullbackComparison l Ω g P L hP).hom ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) g).map f ≫
          (commonStagePullbackComparison l Ω g Q L hQ).inv))
  epsilon : commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω (inv g) ≅
    𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω Y)
  epsilon_formula : ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
    HEq (epsilon.hom.app P)
      ((inclusion (Y := Y) P.stage).map ((S P.stage).rationalEpsilon.hom.app P.obj))

end WeilConjectures

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
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalProEtaleRealization
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalDerivedSiteRealization
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalFiniteSupportRealization
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralExceptionalInverseImage
public import WeilConjectures.SixFunctors.Supporting.SequenceAdjointShiftInterfaces
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralOperationShiftData
public import WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction
public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData

/-! # Integral reconstruction of the exceptional adjunction

Source: Zheng, Propositions 2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24;
blueprint exceptional inverse-image construction, integral steps 10--12
(blueprint: def-sf-exceptional-integral-reconstruction-interfaces).

All systems below are strict systems. Level n is the positive exponent n+1.
The full normalized category imposes common cohomological and Tor bounds, without
adding a compatible-origin witness to its definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived AlgebraicGeometry.strictEtaleLevelDerived

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ExceptionalIntegralReconstruction
open IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The inherited triangulated structure on the recorded integral finite-Tor predicate.
Source: blueprint integral finite-Tor paragraph
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
instance integralTriangulated (T : Scheme.{u}) :
    (finiteTorConstructibleIntegral l E T).IsTriangulated :=
  ConstructibleExceptionalCoefficients.integralTriangulated l { carrier := E } T

attribute [-instance] integralTriangulated
attribute [local instance] integralTriangulated

/-- The full normalized finite-Tor system category, with common bounds at all levels.
Source: Zheng 4.1, 5.22 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def normalized (T : Scheme.{u}) : ObjectProperty (System l E T) := fun N ↦
  IsNormalizedCoefficientSequence l E T N ∧ LevelBounds l E T N

/-- Change only the quotient-ring coordinates of actual strict systems.
Source: Zheng 4.1 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def coordinates (T : Scheme.{u}) :=
  letI : (integralExceptionalCoordinates l E T).asEquivalence.functor.Additive :=
    inferInstanceAs (integralExceptionalCoordinates l E T).Additive
  (integralExceptionalCoordinates l E T).asEquivalence.mapDerivedCategory

/-- The localized termwise shift on the quotient coordinate equivalence.
Source: Stacks 014E (blueprint: lem-sf-exceptional-integral-reconstruction). -/
instance coordinateShift (T : Scheme.{u}) :
    (coordinates l E T).functor.CommShift ℤ := by
  letI : (integralExceptionalCoordinates l E T).asEquivalence.functor.Additive :=
    inferInstanceAs (integralExceptionalCoordinates l E T).Additive
  exact inferInstanceAs
    ((integralExceptionalCoordinates l E T).asEquivalence.functor.mapDerivedCategory.CommShift ℤ)

attribute [-instance] coordinateShift
attribute [local instance] coordinateShift

/-- The localized termwise shift on the inverse quotient coordinate equivalence.
Source: Stacks 014E (blueprint: lem-sf-exceptional-integral-reconstruction). -/
instance coordinateInverseShift (T : Scheme.{u}) :
    (coordinates l E T).inverse.CommShift ℤ := by
  letI : (integralExceptionalCoordinates l E T).asEquivalence.functor.Additive :=
    inferInstanceAs (integralExceptionalCoordinates l E T).Additive
  exact inferInstanceAs
    ((integralExceptionalCoordinates l E T).asEquivalence.inverse.mapDerivedCategory.CommShift ℤ)

attribute [-instance] coordinateInverseShift
attribute [local instance] coordinateInverseShift

/-- The restriction of the actual reduction/total-limit adjunction. The two comparison
isomorphisms and their unit/counit equations fix its maps before finite evaluation.
Source: Zheng 4.1, 5.22 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
structure Reconstruction (T : Scheme.{u}) where
  coherence : CoefficientDerivedSystemCoherence l E T (calculus l E T)
  equivalence : finiteTorConstructibleIntegralCategory l E T ≌
    (normalized l E T).FullSubcategory
  reduction : equivalence.functor ⋙ (normalized l E T).ι ≅
    (finiteTorConstructibleIntegral l E T).ι ⋙ (calculus l E T).reduction
  limit : equivalence.inverse ⋙ (finiteTorConstructibleIntegral l E T).ι ≅
    (normalized l E T).ι ⋙ coefficientSequenceLimit l E T
  unit : ∀ K,
    (finiteTorConstructibleIntegral l E T).ι.map (equivalence.unitIso.hom.app K) ≫
        limit.hom.app (equivalence.functor.obj K) ≫
        (coefficientSequenceLimit l E T).map (reduction.hom.app K) =
      (calculus l E T).adjunction.unit.app K.obj
  counit : ∀ N,
    reduction.hom.app (equivalence.inverse.obj N) ≫
        (calculus l E T).reduction.map (limit.hom.app N) ≫
        (calculus l E T).adjunction.counit.app N.obj =
      (normalized l E T).ι.map (equivalence.counitIso.hom.app N)
  resolutions : PurSequenceResolutionData l E T (calculus l E T)
  resolutionShifts : PurSequenceAdjointShifts l E T (calculus l E T)
    resolutions.ordinary resolutions.derived
  shifts : PurReductionLimitShiftData l E T (calculus l E T)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The specified ordinary-etale system adjunction and its actual pro-etale transport.
These are conclusions of reconstruction, not additional hypotheses on the schemes.
Source: Zheng 5.22, 5.24 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
structure Systems where
  ordinary : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c
  right : StrictEtaleExceptionalAdjoint _ _ c ordinary
  siteX : ExceptionalSystemSiteComparison _ _ X ordinary.PX
  siteY : ExceptionalSystemSiteComparison _ _ Y ordinary.PY
  siteZ : ExceptionalSystemSiteComparison _ _ c.Z ordinary.PZ
  properOpen : ExceptionalProCompactSupport _ _ c
    siteX.proEvaluation siteY.proEvaluation siteZ.proEvaluation
  comparison : ExceptionalSystemCompactificationComparison ordinary siteX siteY siteZ properOpen
  transport : ExceptionalSystemTransport right siteX siteY siteZ properOpen comparison

/-- The actual proper/open word in the coefficient calculus coordinates.
Source: Zheng 5.15, 5.22 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def Systems.left (s : Systems l E c) : System l E X ⥤ System l E Y :=
  (coordinates l E X).functor ⋙ exceptionalProSupport s.properOpen ⋙
    (coordinates l E Y).inverse

/-- The transported ordinary-etale exceptional functor on the same strict systems.
Source: Zheng 5.22 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def Systems.exceptional (s : Systems l E c) : System l E Y ⥤ System l E X :=
  (coordinates l E Y).functor ⋙ exceptionalSystemRight s.right s.siteX s.siteY ⋙
    (coordinates l E X).inverse

/-- The shift transported from the specified proper/open system construction.
Source: Zheng 5.22; blueprint integral step 12
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
instance systemLeftShift (s : Systems l E c) : (s.left l E c).CommShift ℤ :=
  letI := s.transport.val.leftShift
  inferInstanceAs (((coordinates l E X).functor ⋙ exceptionalProSupport s.properOpen ⋙
    (coordinates l E Y).inverse).CommShift ℤ)

attribute [-instance] systemLeftShift
attribute [local instance] systemLeftShift

/-- The shift transported from the specified ordinary-etale right adjoint.
Source: Zheng 5.22; blueprint integral step 12
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
instance systemRightShift (s : Systems l E c) :
    (s.exceptional l E c).CommShift ℤ :=
  letI := s.transport.val.rightShift
  inferInstanceAs (((coordinates l E Y).functor ⋙
    exceptionalSystemRight s.right s.siteX s.siteY ⋙
      (coordinates l E X).inverse).CommShift ℤ)

attribute [-instance] systemRightShift
attribute [local instance] systemRightShift

/-- Preservation and the normalized whole-system Hom chain. The transpose equation
is the transport equation, followed by the canonical coordinate counits; it fixes
both adjunction maps on whole systems, without a faithfulness assumption on evaluation.
Source: Zheng 5.22, 5.24 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
structure SystemAdjunction (s : Systems l E c) where
  leftStable : ∀ N, normalized l E X N → normalized l E Y (s.left l E c |>.obj N)
  rightStable : ∀ N, normalized l E Y N → normalized l E X (s.exceptional l E c |>.obj N)
  adjunction :
    (normalized l E Y).lift ((normalized l E X).ι ⋙ s.left l E c)
        (fun N ↦ leftStable N.obj N.property) ⊣
      (normalized l E X).lift ((normalized l E Y).ι ⋙ s.exceptional l E c)
        (fun N ↦ rightStable N.obj N.property)
  originX : ∀ N, normalized l E X N → s.siteX.origin ((coordinates l E X).functor.obj N)
  originY : ∀ N, normalized l E Y N → s.siteY.origin ((coordinates l E Y).functor.obj N)
  transpose : ∀ (M : (normalized l E X).FullSubcategory)
    (N : (normalized l E Y).FullSubcategory)
    (h : ((normalized l E Y).lift ((normalized l E X).ι ⋙ s.left l E c)
      (fun M ↦ leftStable M.obj M.property)).obj M ⟶ N),
    s.siteX.image.system.adjunction.counit.app ((coordinates l E X).functor.obj M.obj) ≫
        (coordinates l E X).functor.map ((adjunction.homEquiv M N h).hom) ≫
        (coordinates l E X).counitIso.hom.app
          ((exceptionalSystemRight s.right s.siteX s.siteY).obj
            ((coordinates l E Y).functor.obj N.obj)) =
      s.siteX.image.system.inverse.map
        (s.right.adjunction.homEquiv _ _
          (s.siteY.image.system.adjunction.unit.app
              (s.ordinary.functor.obj
                (s.siteX.image.system.direct.obj ((coordinates l E X).functor.obj M.obj))) ≫
            s.siteY.image.system.direct.map
              ((exceptionalSystemOriginComparison s.comparison).app
                  ((coordinates l E X).functor.obj M.obj) ≫
                (coordinates l E Y).counitIso.inv.app
                  ((exceptionalProSupport s.properOpen).obj
                    ((coordinates l E X).functor.obj M.obj)) ≫
                (coordinates l E Y).functor.map h.hom)))

/-- Retain the normalized adjunction while choosing transport shifts on the same
ordinary, site and proper/open data. Every field is copied from the given adjunction.
Source: the definition of SystemAdjunction, which uses no transport shift field.
(blueprint: def-sf-exceptional-integral-reconstruction-interfaces). -/
def SystemAdjunction.withTransport (s : Systems l E c) (a : SystemAdjunction l E c s)
    (t : ExceptionalSystemTransport s.right s.siteX s.siteY s.siteZ
      s.properOpen s.comparison) :
    SystemAdjunction l E c { s with transport := t } where
  leftStable := a.leftStable
  rightStable := a.rightStable
  adjunction := a.adjunction
  originX := a.originX
  originY := a.originY
  transpose := a.transpose

/-- The literal restriction of the actual system left functor.
Source: Zheng 5.22 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def SystemAdjunction.F (s : Systems l E c) (a : SystemAdjunction l E c s) :=
  (normalized l E Y).lift ((normalized l E X).ι ⋙ s.left l E c)
    (fun N ↦ a.leftStable N.obj N.property)

/-- The literal restriction of the actual system right functor.
Source: Zheng 5.22 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def SystemAdjunction.G (s : Systems l E c) (a : SystemAdjunction l E c s) :=
  (normalized l E X).lift ((normalized l E Y).ι ⋙ s.exceptional l E c)
    (fun N ↦ a.rightStable N.obj N.property)

/-- Integral left operation: total limit of the proper/open operation on reductions.
Source: Zheng 5.25 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def integralLeft (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) :=
  rX.equivalence.functor ⋙ a.F l E c s ⋙ rY.equivalence.inverse

/-- Integral exceptional operation: total limit of the exceptional reduction system.
Source: Zheng 5.25 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def integralRight (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) :=
  rY.equivalence.functor ⋙ a.G l E c s ⋙ rX.equivalence.inverse

/-- The adjunction transported by the specified reconstruction equivalences.
Its unit is u_X followed by L_X(eta) and L_X G(e_Y inverse); its counit is
L_Y F(e_X) followed by L_Y(epsilon) and u_Y inverse.
Source: Zheng 5.25 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def integralAdjunction (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) :
    integralLeft l E c rX rY s a ⊣ integralRight l E c rX rY s a :=
  (rX.equivalence.toAdjunction.comp a.adjunction).comp rY.equivalence.symm.toAdjunction

/-- Inclusion of the literal integral left composite into its ambient realization.
Source: Zheng 5.25 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def leftComposite (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) :
    integralLeft l E c rX rY s a ⋙ (finiteTorConstructibleIntegral l E Y).ι ≅
      (finiteTorConstructibleIntegral l E X).ι ⋙ (calculus l E X).reduction ⋙
        s.left l E c ⋙ coefficientSequenceLimit l E Y :=
  Functor.isoWhiskerLeft (rX.equivalence.functor ⋙ a.F l E c s) rY.limit ≪≫
    Functor.isoWhiskerRight rX.reduction (s.left l E c ⋙ coefficientSequenceLimit l E Y)

/-- Inclusion of the literal integral right composite into its ambient realization.
Source: Zheng 5.25 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def rightComposite (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) :
    integralRight l E c rX rY s a ⋙ (finiteTorConstructibleIntegral l E X).ι ≅
      (finiteTorConstructibleIntegral l E Y).ι ⋙ (calculus l E Y).reduction ⋙
        s.exceptional l E c ⋙ coefficientSequenceLimit l E X :=
  Functor.isoWhiskerLeft (rY.equivalence.functor ⋙ a.G l E c s) rX.limit ≪≫
    Functor.isoWhiskerRight rY.reduction
      (s.exceptional l E c ⋙ coefficientSequenceLimit l E X)

/-- Canonical finite evaluation of the actual proper/open word, including the
coordinate-equivalence counit. Source: Zheng 5.22
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
def Systems.leftEvaluation (s : Systems l E c) (n : ℕ) :
    s.left l E c ⋙ (coordinates l E Y).functor ⋙ s.siteY.proEvaluation.evaluation n ≅
      (coordinates l E X).functor ⋙ s.siteX.proEvaluation.evaluation n ⋙
        (s.properOpen.val.levelDerivedOpen n ⋙
          (s.properOpen.val.properDerived.level n).direct) :=
  Functor.isoWhiskerLeft
      ((coordinates l E X).functor ⋙ exceptionalProSupport s.properOpen)
      (Functor.isoWhiskerRight (coordinates l E Y).counitIso
        (s.siteY.proEvaluation.evaluation n) ≪≫ Functor.leftUnitor _) ≪≫
    Functor.isoWhiskerLeft (coordinates l E X).functor
      (exceptionalProSupportEvaluation s.properOpen n)

/-- Canonical finite evaluation of the transported system exceptional operation.
Source: Zheng 5.22 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def Systems.rightEvaluation (s : Systems l E c) (n : ℕ) :
    s.exceptional l E c ⋙ (coordinates l E X).functor ⋙ s.siteX.proEvaluation.evaluation n ≅
      (coordinates l E Y).functor ⋙ s.siteY.proEvaluation.evaluation n ⋙
        ((s.siteY.image.level n).direct ⋙ s.right.levelRight n ⋙
          (s.siteX.image.level n).inverse) :=
  Functor.isoWhiskerLeft
      ((coordinates l E Y).functor ⋙ exceptionalSystemRight s.right s.siteX s.siteY)
      (Functor.isoWhiskerRight (coordinates l E X).counitIso
        (s.siteX.proEvaluation.evaluation n) ≪≫ Functor.leftUnitor _) ≪≫
    Functor.isoWhiskerLeft (coordinates l E Y).functor
      (exceptionalSystemRightEvaluation s.right s.siteX s.siteY n)

/-- Regard the existing site comparison in the fixed scalar realization interface.
Source: Zheng 4.10 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def Systems.siteRealization (T : Scheme.{u})
    (P : StrictEtaleEvaluation T (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (C : ExceptionalSystemSiteComparison _ _ T P) : IntegralExceptionalComparison l E T P where
  ordinary := C.ordinary
  evaluation := C.proEvaluation
  derived := C.image

/-- The actual site inverse image, expressed in the calculus coordinates.
Source: Zheng 4.10 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def Systems.etaleInput (s : Systems l E c)
    (A : DerivedCategory (strictEtaleCoefficientSystem X (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))) :=
  (coordinates l E X).inverse.obj (s.siteX.image.system.inverse.obj A)

/-- The proper mate and open comparison, before any finite evaluation.
Source: Zheng 5.22 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def Systems.supportMap (s : Systems l E c)
    (A : DerivedCategory (strictEtaleCoefficientSystem X (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))) :
    (coordinates l E Y).inverse.obj
      (s.siteY.image.system.inverse.obj (s.ordinary.functor.obj A)) ⟶
        (s.left l E c).obj (s.etaleInput l E c A) :=
  (coordinates l E Y).inverse.map ((exceptionalSystemComparison s.comparison).app A) ≫
    (coordinates l E Y).inverse.map
      ((exceptionalProSupport s.properOpen).map
        ((coordinates l E X).counitIso.inv.app (s.siteX.image.system.inverse.obj A)))

/-- The canonical finite proper/open projection: scalar-unit coordinates, site
localization, the etale support realization, and the fixed proper/open site mate.
Every factor is a published, normalized comparison; no scalar choice is made.
Source: Zheng 4.10, 5.22 and Stacks 099R
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
def Systems.supportProjection (s : Systems l E c)
    (A : DerivedCategory (strictEtaleCoefficientSystem X (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))) (n : ℕ)
    (h : DerivedCategory.TStructure.t.plus
      ((integralExceptionalEtaleRealization l E X n).mapDerivedCategory.obj
        ((s.ordinary.PX.evaluation n).obj A))) :
    (coefficientSequenceDerivedEvaluation l E Y n).obj
      ((coordinates l E Y).inverse.obj
        (s.siteY.image.system.inverse.obj (s.ordinary.functor.obj A))) ≅
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      ((coefficientSequenceDerivedEvaluation l E X n).obj (s.etaleInput l E c A)) :=
  let BX := Systems.siteRealization l E X s.ordinary.PX s.siteX
  let BY := Systems.siteRealization l E Y s.ordinary.PY s.siteY
  let RX := (integralExceptionalEtaleRealization l E X n).mapDerivedCategory
  let RY := (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory
  let NY := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) Y).mapDerivedCategory
  let EX := sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))
  let EY := sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))
  let eX := integralExceptionalCoordinatesInvFixed l E X s.siteX.proEvaluation
      (s.siteX.image.system.inverse.obj A) n ≪≫
    (integralExceptionalProRealization l E X n).mapDerivedCategory.mapIso
      ((s.siteX.image.inverseEvaluation n).app A) ≪≫
    (integralExceptionalSiteDerivedInverse l E X s.ordinary.PX BX n).app
      ((s.ordinary.PX.evaluation n).obj A)
  let eY := integralExceptionalCoordinatesInvFixed l E Y s.siteY.proEvaluation
      (s.siteY.image.system.inverse.obj (s.ordinary.functor.obj A)) n ≪≫
    (integralExceptionalProRealization l E Y n).mapDerivedCategory.mapIso
      ((s.siteY.image.inverseEvaluation n).app (s.ordinary.functor.obj A)) ≪≫
    (integralExceptionalSiteDerivedInverse l E Y s.ordinary.PY BY n).app
      ((s.ordinary.PY.evaluation n).obj (s.ordinary.functor.obj A)) ≪≫
    NY.mapIso (RY.mapIso ((s.ordinary.evaluation n).app A) ≪≫
      (integralExceptionalEtaleSupportComparison l E f c s.ordinary n).app
        ((s.ordinary.PX.evaluation n).obj A))
  let F := ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c
  EY.counitIso.symm.app _ ≪≫ EY.functor.mapIso
    (eY ≪≫
      ((ProEtale.compactSupportSiteComparison
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) c).app
            ⟨RX.obj ((s.ordinary.PX.evaluation n).obj A), h⟩).symm ≪≫
      F.mapIso eX.symm) ≪≫
    (ProEtale.sfIntrinsicCompactSupportComparison
      (Padic.coefficientExtensionRing l E (n + 1)) c).symm.app _ ≪≫
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).mapIso
      (EX.counitIso.app _)

/-- Canonical reduction comparison for the reconstructed right operation.
Source: Zheng 5.22, 5.25 (blueprint: lem-sf-exceptional-integral-reconstruction). -/
def rightEvaluation (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) (n : ℕ) :
    integralRight l E c rX rY s a ⋙ rX.equivalence.functor ⋙
        (normalized l E X).ι ⋙ (coordinates l E X).functor ⋙
          s.siteX.proEvaluation.evaluation n ≅
      rY.equivalence.functor ⋙ (normalized l E Y).ι ⋙ (coordinates l E Y).functor ⋙
        s.siteY.proEvaluation.evaluation n ⋙
          ((s.siteY.image.level n).direct ⋙ s.right.levelRight n ⋙
            (s.siteX.image.level n).inverse) :=
  Functor.isoWhiskerLeft (rY.equivalence.functor ⋙ a.G l E c s)
      (Functor.isoWhiskerRight rX.equivalence.counitIso
        ((normalized l E X).ι ⋙ (coordinates l E X).functor ⋙
          s.siteX.proEvaluation.evaluation n) ≪≫ Functor.leftUnitor _) ≪≫
    Functor.isoWhiskerLeft (rY.equivalence.functor ⋙ (normalized l E Y).ι)
      (s.rightEvaluation l E c n)

/-- One cohomological and one Tor interval enlargement for every coefficient level.
Source: Zheng 2.29, 3.16, 5.24
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
def UniformBounds {T U : Scheme.{u}} (F : System l E T ⥤ System l E U) : Prop :=
  ∃ cMinus cPlus tMinus tPlus : ℤ,
    (∀ (N : System l E T), normalized l E T N → ∀ (n : ℕ) (a b : ℤ),
      proEtaleCohomologicalSupport
          ((coefficientSequenceDerivedEvaluation l E T n).obj N) ⊆ Set.Icc a b →
        proEtaleCohomologicalSupport
          ((coefficientSequenceDerivedEvaluation l E U n).obj (F.obj N)) ⊆
            Set.Icc (a + cMinus) (b + cPlus)) ∧
    (∀ (N : System l E T), normalized l E T N → ∀ (n : ℕ) (a b : ℤ),
      HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (n + 1))
        ((coefficientSequenceDerivedEvaluation l E T n).obj N) a b →
      HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E (n + 1))
        ((coefficientSequenceDerivedEvaluation l E U n).obj (F.obj N))
          (a + tMinus) (b + tPlus))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The prescribed reduction-tower compact-support functor, with ambient inclusion.
Source: blueprint compact-support definition
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
def prescribed : finiteTorConstructibleIntegralCategory l E X ⥤ Integral l E Y :=
  PurCompactSupport.finiteTorIntegralInclusion l E X ⋙
    sfCompactSupportFiniteIntegralFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
      c E ⋙ (sfIntegralConstructible l E Y).ι

/-- The inverse canonical ambient-to-tower realization h_R, restricted to finite Tor.
Source: blueprint single proper/open word and its quotient-cone normalization
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
def prescribedRealization : prescribed l E c D hl ≅
    (finiteTorConstructibleIntegral l E X).ι ⋙ PurCompactSupport.image
      (PurCompactSupport.completed l E) c :=
  (Functor.isoWhiskerLeft (PurCompactSupport.finiteTorIntegralInclusion l E X)
    (sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c)).symm

/-- The proper/open ambient shift, using right derivation and exact localization.
Source: blueprint single proper/open word; Stacks 0941
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
instance ambientShift : ((finiteTorConstructibleIntegral l E X).ι ⋙
    PurCompactSupport.image (PurCompactSupport.completed l E) c).CommShift ℤ :=
  letI : (PurCompactSupport.image (PurCompactSupport.completed l E) c).CommShift ℤ :=
    (integralShifts l E).compactSupport f c
  inferInstanceAs (((finiteTorConstructibleIntegral l E X).ι ⋙
    PurCompactSupport.image (PurCompactSupport.completed l E) c).CommShift ℤ)

attribute [-instance] ambientShift
attribute [local instance] ambientShift

/-- Additivity, exactness, adjoint shifts, uniform bounds, and the actual integral
normalization against the prescribed compact-support tower. The primitive equation
fixes r before the equation involving u; it is not a comparison inferred from levels.
Source: Zheng 5.22, 5.24, 5.25; blueprint integral steps 10--12
(blueprint: lem-sf-exceptional-integral-reconstruction). -/
structure Realization (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) where
  operations : Operations l E
  model : RealizationModel l E operations
  systemLeft : s.left l E c ≅
    Operations.shriek l E operations c.i ⋙ Operations.push l E operations c.g
  systemLeft_normalization : ∀
    (A : DerivedCategory (strictEtaleCoefficientSystem X (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))) (n : ℕ)
    (h : DerivedCategory.TStructure.t.plus
      ((integralExceptionalEtaleRealization l E X n).mapDerivedCategory.obj
        ((s.ordinary.PX.evaluation n).obj A))),
    (coefficientSequenceDerivedEvaluation l E Y n).map
      (s.supportMap l E c A ≫ systemLeft.hom.app (s.etaleInput l E c A)) ≫
      (supportEvaluation l E operations c n).hom.app (s.etaleInput l E c A) =
    (s.supportProjection l E c A n h).hom
  systemLeftShift :
    letI := systemOpenShift l E operations c.i
    letI := systemPushShift l E operations c.g
    systemLeft.hom.CommShift ℤ
  leftBounds : UniformBounds l E (s.left l E c)
  rightBounds : UniformBounds l E (s.exceptional l E c)
  [leftAdditive : (integralLeft l E c rX rY s a).Additive]
  [rightAdditive : (integralRight l E c rX rY s a).Additive]
  [leftShift : (integralLeft l E c rX rY s a).CommShift ℤ]
  [rightShift : (integralRight l E c rX rY s a).CommShift ℤ]
  leftExact : (integralLeft l E c rX rY s a).IsTriangulated
  rightExact : (integralRight l E c rX rY s a).IsTriangulated
  unitShift : (integralAdjunction l E c rX rY s a).unit.CommShift ℤ
  counitShift : (integralAdjunction l E c rX rY s a).counit.CommShift ℤ
  rightShift_adjoint : rightShift = (integralAdjunction l E c rX rY s a).rightAdjointCommShift ℤ
  prescribedStable : ∀ K : finiteTorConstructibleIntegralCategory l E X,
    finiteTorConstructibleIntegral l E Y ((prescribed l E c D hl).obj K)
  identification : integralLeft l E c rX rY s a ≅
    (finiteTorConstructibleIntegral l E Y).lift (prescribed l E c D hl) prescribedStable
  realization : integralLeft l E c rX rY s a ⋙ (finiteTorConstructibleIntegral l E Y).ι ≅
    (finiteTorConstructibleIntegral l E X).ι ⋙ PurCompactSupport.image
      (PurCompactSupport.completed l E) c
  openUnit : ∀ K : finiteTorConstructibleIntegralCategory l E X,
    IsIso ((calculus l E c.Z).adjunction.unit.app ((ringedOpen l E c.i).obj K.obj))
  primitive : ∀ K : finiteTorConstructibleIntegralCategory l E X,
    realization.hom.app K = (leftComposite l E c rX rY s a).hom.app K ≫
      (coefficientSequenceLimit l E Y).map
        (systemLeft.hom.app ((calculus l E X).reduction.obj K.obj)) ≫
      (model.push l E c.g).hom.app
        ((Operations.shriek l E operations c.i).obj ((calculus l E X).reduction.obj K.obj)) ≫
      (ringedPush l E c.g).map
        ((coefficientSequenceLimit l E c.Z).map ((model.openReduction l E c.i).app K.obj) ≫
          @inv _ _ _ _ ((calculus l E c.Z).adjunction.unit.app
            ((ringedOpen l E c.i).obj K.obj)) (openUnit K))
  normalization : ∀ K : finiteTorConstructibleIntegralCategory l E X,
    (finiteTorConstructibleIntegral l E Y).ι.map (identification.hom.app K) =
      realization.hom.app K ≫ (prescribedRealization l E c D hl).inv.app K
  leftCompositeShift :
    letI := rX.shifts.reduction_shift
    letI := rY.shifts.limit_shift
    (leftComposite l E c rX rY s a).hom.CommShift ℤ
  rightCompositeShift :
    letI := rY.shifts.reduction_shift
    letI := rX.shifts.limit_shift
    (rightComposite l E c rX rY s a).hom.CommShift ℤ
  realizationShift :
    letI := ambientShift l E c
    realization.hom.CommShift ℤ
  [prescribedShift : (prescribed l E c D hl).CommShift ℤ]
  prescribedRealizationShift :
    letI := ambientShift l E c
    (prescribedRealization l E c D hl).hom.CommShift ℤ
  [prescribedLiftShift : ((finiteTorConstructibleIntegral l E Y).lift
    (prescribed l E c D hl) prescribedStable).CommShift ℤ]
  prescribedLiftShift_inclusion :
    ((finiteTorConstructibleIntegral l E Y).liftCompιIso
      (prescribed l E c D hl) prescribedStable).hom.CommShift ℤ
  identificationShift : identification.hom.CommShift ℤ

end WeilConjectures.ExceptionalIntegralReconstruction

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRestriction.NativeScalarOrdinaryRestrictionComparisons
public import WeilConjectures.CategoryTheory.EquivalenceCubeTransport.EquivalenceCubeTransport

/-! # Canonical derived comparisons for a scalar presentation

Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; Cohomology on Sites, Tag 0D6E.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.EquivalenceCubeTransport
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport.NativeScalarDerivedRestriction
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale

attribute [local instance] nativeScalarModuleClosed nativeScalarModuleSymmetric
  nativeScalarModuleFlatResolution nativeScalarModuleLeftColimits nativeScalarModuleRightColimits
  nativeScalarModuleTensorFour nativeScalarModuleGoodTensorLeft nativeScalarModuleGoodTensorRight
  nativeScalarIntegralExact

/-- The two localized restrictions, in the specified order.
Source: the scalar direct-image proof, exact coefficient restrictions.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons). -/
abbrev compositeRestriction (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) T)) :=
  (Mod.comap (coefficientMap
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T)).mapDerivedCategory ⋙
    (Mod.comap (padicIntegersToPadicSubfield T l E)).mapDerivedCategory

/-- The positive paste of the two specified condensed comparison isomorphisms.
Source: Stacks, Cohomology on Sites, Tag 0D6E.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons). -/
def positiveSquare (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) {U V : Scheme.{u}} (g : U ⟶ V) :
    CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) g ⋙
        compositeRestriction l E V ≅
      compositeRestriction l E U ⋙
        CondensedRing.moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.1) g :=
  Functor.isoWhiskerRight
    (CondensedRing.derivedComapLowerStarIso (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g)
    (Mod.comap (padicIntegersToPadicSubfield V l E)).mapDerivedCategory ≪≫
  Functor.isoWhiskerLeft
    ((Mod.comap (coefficientMap
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E) U)).mapDerivedCategory)
    (CondensedRing.derivedComapLowerStarIso (padicIntegersRingObjToContinuousMapRingObj l E) g)

variable (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
  {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
  (P : NativeScalarRingModel l E a)
  (k : ∀ T : Scheme.{u},
    NativeScalarRestriction.ordinaryCompositeRestriction l E T ⋙
        (P.integralEquivalence T).inverse ≅
      (P.closureEquivalence T).inverse ⋙ proEtaleRingRestrictScalars (a.map T))

/-- Localize the ordinary inverse restriction comparison with explicit composition factors.
Source: exact localization and composition of the two coefficient restrictions.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons). -/
def inverseRestriction (T : Scheme.{u}) :
    compositeRestriction l E T ⋙ (P.integralEquivalence T).inverse.mapDerivedCategory ≅
      (P.closureEquivalence T).inverse.mapDerivedCategory ⋙
        (proEtaleRingRestrictScalars (a.map T)).mapDerivedCategory :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T))
      (Mod.comap (padicIntegersToPadicSubfield T l E)))
    (P.integralEquivalence T).inverse.mapDerivedCategory ≪≫
      IndependentDerivedCube.localizedSquare
        (F := Mod.comap (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T) ⋙
            Mod.comap (padicIntegersToPadicSubfield T l E))
        (G := (P.integralEquivalence T).inverse)
        (H := (P.closureEquivalence T).inverse)
        (J := proEtaleRingRestrictScalars (a.map T)) (k T)

/-- The corresponding forward restriction comparison.
Source: transport through the derived presentation equivalences and their units.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons). -/
def forwardRestriction (T : Scheme.{u}) :
    (proEtaleRingRestrictScalars (a.map T)).mapDerivedCategory ⋙
        (P.integralEquivalence T).functor.mapDerivedCategory ≅
      (P.closureEquivalence T).functor.mapDerivedCategory ⋙ compositeRestriction l E T :=
  forwardOfInverse (liftEquivalence (P.closureEquivalence T))
    (liftEquivalence (P.integralEquivalence T))
    (proEtaleRingRestrictScalars (a.map T)).mapDerivedCategory
    (compositeRestriction l E T) (inverseRestriction l E a P k T)

variable {U V : Scheme.{u}} (g : U ⟶ V)

/-- The derived inverse integral direct-image comparison.
Source: canonical right derivation of the ordinary comparison through equivalences.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons). -/
def inverseIntegralPush
    (x : CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g ⋙
        (P.integralEquivalence V).inverse ≅
      (P.integralEquivalence U).inverse ⋙
        proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)) :
    (CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g).rightDerivedFunctor ⋙
        (P.integralEquivalence V).inverse.mapDerivedCategory ≅
      (P.integralEquivalence U).inverse.mapDerivedCategory ⋙
        (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).rightDerivedFunctor :=
  inverseDerivedPush (CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g)
    (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g))
    (P.integralEquivalence U) (P.integralEquivalence V) x

/-- The derived inverse closure direct-image comparison.
Source: canonical right derivation of the ordinary comparison through equivalences.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons). -/
def inverseClosurePush
    (y : CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g ⋙
        (P.closureEquivalence V).inverse ≅
      (P.closureEquivalence U).inverse ⋙
        proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)) :
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).rightDerivedFunctor ⋙
        (P.closureEquivalence V).inverse.mapDerivedCategory ≅
      (P.closureEquivalence U).inverse.mapDerivedCategory ⋙
        (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)).rightDerivedFunctor :=
  inverseDerivedPush (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g)
    (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g))
    (P.closureEquivalence U) (P.closureEquivalence V) y

/-- The forward integral direct-image comparison.
Source: equivalence units applied to inverseIntegralPush.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons). -/
def forwardIntegralPush
    (x : CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g ⋙
        (P.integralEquivalence V).inverse ≅
      (P.integralEquivalence U).inverse ⋙
        proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)) :
    (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).rightDerivedFunctor ⋙
        (P.integralEquivalence V).functor.mapDerivedCategory ≅
      (P.integralEquivalence U).functor.mapDerivedCategory ⋙
        (CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g).rightDerivedFunctor :=
  forwardOfInverse (liftEquivalence (P.integralEquivalence U))
    (liftEquivalence (P.integralEquivalence V))
    (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).rightDerivedFunctor
    (CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g).rightDerivedFunctor
    (inverseIntegralPush l E a P g x)

/-- The forward closure direct-image comparison.
Source: equivalence units applied to inverseClosurePush.
(blueprint: def-sf-native-scalar-derived-restriction-comparisons). -/
def forwardClosurePush
    (y : CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g ⋙
        (P.closureEquivalence V).inverse ≅
      (P.closureEquivalence U).inverse ⋙
        proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)) :
    (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)).rightDerivedFunctor ⋙
        (P.closureEquivalence V).functor.mapDerivedCategory ≅
      (P.closureEquivalence U).functor.mapDerivedCategory ⋙
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).rightDerivedFunctor :=
  forwardOfInverse (liftEquivalence (P.closureEquivalence U))
    (liftEquivalence (P.closureEquivalence V))
    (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)).rightDerivedFunctor
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).rightDerivedFunctor
    (inverseClosurePush l E a P g y)

end WeilConjectures.LocallyFiniteAdicCompactSupport.NativeScalarDerivedRestriction

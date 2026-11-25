/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarDerivedRestriction.NativeScalarDerivedRestrictionComparisons
import WeilConjectures.CategoryTheory.Right.RightDerivedExactRestrictionNormalization

/-! # Full-unit normalizations of the presentation comparisons

Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-native-scalar-derived-restriction-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false
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

/-- The inverse integral comparison has the full cochain-unit normalization.
Source: Stacks, Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-native-scalar-derived-restriction-normalization).
Proof: unfold the named comparison and apply the canonical exact-equivalence
normalization. This keeps the concrete comparison folded for the cube calculation. -/
theorem integral_normalized (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    (P : NativeScalarRingModel l E a) {U V : Scheme.{u}} (g : U ⟶ V)
    (x : CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g ⋙
        (P.integralEquivalence V).inverse ≅
      (P.integralEquivalence U).inverse ⋙
        proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)) :
    IndependentDerivedCube.unitNormalized
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g)
      (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g))
      (P.integralEquivalence U).inverse (P.integralEquivalence V).inverse
      (P.integralEquivalence U).inverse.mapDerivedCategory
      (P.integralEquivalence V).inverse.mapDerivedCategory
      (P.integralEquivalence U).inverse.mapDerivedCategoryFactors
      (P.integralEquivalence V).inverse.mapDerivedCategoryFactors
      x.hom (inverseIntegralPush l E a P g x).hom := by
  exact EquivalenceCubeTransport.inverseDerivedPush_normalized
    (CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g)
    (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g))
    (P.integralEquivalence U) (P.integralEquivalence V) x

/-- The inverse closure comparison has the full cochain-unit normalization.
Source: Stacks, Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-native-scalar-derived-restriction-normalization).
Proof: unfold the named comparison and apply the canonical exact-equivalence
normalization. This keeps the concrete comparison folded for the cube calculation. -/
theorem closure_normalized (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    (P : NativeScalarRingModel l E a) {U V : Scheme.{u}} (g : U ⟶ V)
    (x : CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g ⋙
        (P.closureEquivalence V).inverse ≅
      (P.closureEquivalence U).inverse ⋙
        proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)) :
    IndependentDerivedCube.unitNormalized
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g)
      (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g))
      (P.closureEquivalence U).inverse (P.closureEquivalence V).inverse
      (P.closureEquivalence U).inverse.mapDerivedCategory
      (P.closureEquivalence V).inverse.mapDerivedCategory
      (P.closureEquivalence U).inverse.mapDerivedCategoryFactors
      (P.closureEquivalence V).inverse.mapDerivedCategoryFactors
      x.hom (inverseClosurePush l E a P g x).hom := by
  exact EquivalenceCubeTransport.inverseDerivedPush_normalized
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g)
    (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g))
    (P.closureEquivalence U) (P.closureEquivalence V) x

/-- The canonical condensed comparison has its full right-derived unit normalization.
Source: Stacks, Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-native-scalar-derived-restriction-normalization).
Proof: unfold the specified derived comparison and use exact-restriction normalization. -/
theorem condensed_normalized
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]
    {U V : Scheme.{u}} (g : U ⟶ V) :
    IndependentDerivedCube.unitNormalized
      (CondensedRing.lowerStar Λ' g) (CondensedRing.lowerStar Λ g)
      (Mod.comap (coefficientMap a U)) (Mod.comap (coefficientMap a V))
      (Mod.comap (coefficientMap a U)).mapDerivedCategory
      (Mod.comap (coefficientMap a V)).mapDerivedCategory
      (Mod.comap (coefficientMap a U)).mapDerivedCategoryFactors
      (Mod.comap (coefficientMap a V)).mapDerivedCategoryFactors
      (CondensedRing.comapLowerStarIso a g).hom
      (CondensedRing.derivedComapLowerStarIso a g).hom := by
  intro I
  exact rightDerivedExactRestriction_normalization
    (CondensedRing.lowerStar Λ' g) (CondensedRing.lowerStar Λ g)
    (Mod.comap (coefficientMap a U)) (Mod.comap (coefficientMap a V))
    (CondensedRing.comapLowerStarIso a g) I

end WeilConjectures.LocallyFiniteAdicCompactSupport.NativeScalarDerivedRestriction

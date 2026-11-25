/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarDerivedRestriction.NativeScalarDerivedRestrictionNormalization
import WeilConjectures.CategoryTheory.Right.RightDerivedExactRestrictionNormalization

/-! # The inverse derived restriction cube

Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; Cohomology on Sites, Tag 0D6E.
(blueprint: lem-sf-native-scalar-inverse-derived-restriction-cube).
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

-- Use the public functor and equivalence APIs without expanding section-ring implementations.
attribute [local irreducible] CondensedRing.lowerStar proEtaleRingModuleDirectImage
  NativeScalarRingModel.integralEquivalence NativeScalarRingModel.closureEquivalence

-- Normalizing concrete site functors elaborates both ringed-site presentations.
/-- Exact localization carries the ordinary scalar cube to the specified inverse derived cube.
Source: Stacks, Cohomology on Sites, Tag 0D6E; step 4 of the native scalar cube.
(blueprint: lem-sf-native-scalar-inverse-derived-restriction-cube).

Proof: normalize the two condensed faces by their right-derived cochain units.
Normalize the inverse presentation faces by the exact-equivalence composition formula,
and the native face by its defining uniqueness theorem. The independent-universe
localization cube theorem pastes these normalized faces. Its ordinary hypothesis is
exactly h after composing the two ordinary coefficient restrictions. Thus the equality
holds on every unbounded derived object, without a boundedness assumption. -/
theorem inverseCube (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
  {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
  (P : NativeScalarRingModel l E a)
  (k : ∀ T : Scheme.{u},
    NativeScalarRestriction.ordinaryCompositeRestriction l E T ⋙
        (P.integralEquivalence T).inverse ≅
      (P.closureEquivalence T).inverse ⋙ proEtaleRingRestrictScalars (a.map T))
    {U V : Scheme.{u}} (g : U ⟶ V)
    (x : CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g ⋙
              (P.integralEquivalence V).inverse ≅
            (P.integralEquivalence U).inverse ⋙
              proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g))
    (y : CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g ⋙
              (P.closureEquivalence V).inverse ≅
            (P.closureEquivalence U).inverse ⋙
              proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g))
    (h : ∀ M,
            (k V).hom.app
                ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).obj M) ≫
              (proEtaleRingRestrictScalars (a.map V)).map (y.hom.app M) ≫
              (proEtaleRingRestrictionDirectImage g
                (R.ring V) (S.ring V) (R.ring U) (S.ring U)
                (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app
                  ((P.closureEquivalence U).inverse.obj M) =
            (P.integralEquivalence V).inverse.map
                ((NativeScalarRestriction.ordinaryCompositeSquare l E g).hom.app M) ≫
              x.hom.app ((NativeScalarRestriction.ordinaryCompositeRestriction l E U).obj M) ≫
              (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).map
                ((k U).hom.app M)) :
    ∀ M,
      (inverseRestriction l E a P k V).hom.app
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).rightDerivedFunctor.obj M) ≫
        (proEtaleRingRestrictScalars (a.map V)).mapDerivedCategory.map
          ((inverseClosurePush l E a P g y).hom.app M) ≫
        (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app
            ((P.closureEquivalence U).inverse.mapDerivedCategory.obj M) =
      (P.integralEquivalence V).inverse.mapDerivedCategory.map
          ((positiveSquare l E g).hom.app M) ≫
        (inverseIntegralPush l E a P g x).hom.app ((compositeRestriction l E U).obj M) ≫
        (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).rightDerivedFunctor.map
          ((inverseRestriction l E a P k U).hom.app M) := by
  let c₁ (T : Scheme.{u}) :
      Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj l) T) ⥤
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E.1) T) :=
    Mod.comap (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T)
  let c₂ (T : Scheme.{u}) :
      Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E.1) T) ⥤
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj l E.1) T) :=
    Mod.comap (padicIntegersToPadicSubfield T l E)
  let pC := CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g
  let pE := CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1) g
  let pI := CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g
  let qR := proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)
  let qS := proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)
  let r (T : Scheme.{u}) := proEtaleRingRestrictScalars (a.map T)
  let i (T : Scheme.{u}) := (P.integralEquivalence T).inverse
  let e (T : Scheme.{u}) := (P.closureEquivalence T).inverse
  let b₁ := CondensedRing.comapLowerStarIso (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g
  let b₂ := CondensedRing.comapLowerStarIso (padicIntegersRingObjToContinuousMapRingObj l E) g
  let B₁ := CondensedRing.derivedComapLowerStarIso
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g
  let B₂ := CondensedRing.derivedComapLowerStarIso
    (padicIntegersRingObjToContinuousMapRingObj l E) g
  let d := proEtaleRingRestrictionDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let D := proEtaleRingRestrictionDerivedDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let X : pI.rightDerivedFunctor ⋙ (P.integralEquivalence V).inverse.mapDerivedCategory ≅
      (P.integralEquivalence U).inverse.mapDerivedCategory ⋙ qR.rightDerivedFunctor :=
    inverseIntegralPush l E a P g x
  let Y : pC.rightDerivedFunctor ⋙ (P.closureEquivalence V).inverse.mapDerivedCategory ≅
      (P.closureEquivalence U).inverse.mapDerivedCategory ⋙ qS.rightDerivedFunctor :=
    inverseClosurePush l E a P g y
  have hn₁ := condensed_normalized (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g
  have hn₂ := condensed_normalized (padicIntegersRingObjToContinuousMapRingObj l E) g
  have hnD : IndependentDerivedCube.unitNormalized qS qR (r U) (r V)
      (r U).mapDerivedCategory (r V).mapDerivedCategory
      (r U).mapDerivedCategoryFactors (r V).mapDerivedCategoryFactors d.hom D.hom := by
    intro I
    exact (Classical.choose_spec (proEtaleRingRestrictionDerivedDirectImage_existsUnique g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))).1 I
  unfold inverseRestriction positiveSquare
  dsimp only [compositeRestriction]
  have hc := IndependentDerivedCube.normalized_composite_cube
    (F0 := pC) (F1 := pE) (F2 := pI) (G0 := qS) (G1 := qR)
    (sU := c₁ U) (sV := c₁ V) (tU := c₂ U) (tV := c₂ V)
    (iU := i U) (iV := i V) (eU := e U) (eV := e V) (rU := r U) (rV := r V)
    (b0 := b₁) (b1 := b₂) (x := x) (y := y) (d := d)
    (B0d := B₁) (B1d := B₂) (X := X) (Y := Y) (Dd := D) (hb0 := hn₁) (hb1 := hn₂)
    (hx := integral_normalized l E a P g x)
    (hy := closure_normalized l E a P g y)
    (hd := hnD) (kU := k U) (kV := k V)
    (h := fun M ↦ by
      simpa only [IndependentDerivedCube.compSquare,
        NativeScalarRestriction.ordinaryCompositeSquare,
        NativeScalarRestriction.ordinaryCompositeRestriction,
        c₁, c₂, pC, qR, r, i, e, d, b₁, b₂] using h M)
  exact hc

end WeilConjectures.LocallyFiniteAdicCompactSupport.NativeScalarDerivedRestriction

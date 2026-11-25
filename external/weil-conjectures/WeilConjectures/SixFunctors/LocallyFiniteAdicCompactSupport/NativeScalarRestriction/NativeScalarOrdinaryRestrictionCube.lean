/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRestriction.NativeScalarOrdinaryRestrictionComparisons
import all WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRestriction.NativeScalarOrdinaryRestrictionComparisons

/-! # Ordinary restriction and direct image under a coefficient-ring presentation

Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; Cohomology on Sites,
Tag 0D6E; blueprint scalar direct-image proof, Formal properties.
(blueprint: lem-sf-native-scalar-ordinary-restriction-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport.NativeScalarRestriction
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale
open TwoSquare

private theorem nativeSquare_apply
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) (N : pbcModules U (S.ring U))
    (W : V.ProEtᵒᵖ) (m : N.val.obj ((proEtaleBaseChange g).op.obj W)) :
    ((proEtaleRingRestrictionDirectImage g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app N).val.app W m = m := by
  exact (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))).1 N W m

-- Comparing concrete section-module functors requires elaborating the site transports.
private theorem inverseOrdinaryCube (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) (P : NativeScalarRingModel l E a)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) U)) :
    (inverseRestriction l E P V).hom.app
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).obj M) ≫
        (proEtaleRingRestrictScalars (a.map V)).map
          ((inversePushforward S _ P.closure P.closure_natural g).hom.app M) ≫
        (proEtaleRingRestrictionDirectImage g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app
          ((P.closureEquivalence U).inverse.obj M) =
      (P.integralEquivalence V).inverse.map ((ordinaryCompositeSquare l E g).hom.app M) ≫
        (inversePushforward R _ P.integral P.integral_natural g).hom.app
          ((ordinaryCompositeRestriction l E U).obj M) ≫
        (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).map
          ((inverseRestriction l E P U).hom.app M) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.X.obj.obj ((proEtaleBaseChange g).op.obj W) at m
  change ((proEtaleRingRestrictionDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app
    ((P.closureEquivalence U).inverse.obj M)).val.app W
      (((inversePushforward S _ P.closure P.closure_natural g).hom.app M).val.app W
        (((inverseRestriction l E P V).hom.app
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).obj M)).val.app W m)) = _
  erw [inverseRestriction_apply]
  change ((proEtaleRingRestrictionDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app
    ((P.closureEquivalence U).inverse.obj M)).val.app W
      (((inversePushforward S _ P.closure P.closure_natural g).hom.app M).val.app W m) = _
  erw [inversePushforward_apply]
  erw [nativeSquare_apply]
  change m = ((inverseRestriction l E P U).hom.app M).val.app
    ((proEtaleBaseChange g).op.obj W)
      (((inversePushforward R _ P.integral P.integral_natural g).hom.app
        ((ordinaryCompositeRestriction l E U).obj M)).val.app W
          (((ordinaryCompositeSquare l E g).hom.app M).hom.hom.app W m))
  have hb := ordinaryCompositeSquare_apply l E g M W m
  have hx := inversePushforward_apply R _ P.integral P.integral_natural g
    ((ordinaryCompositeRestriction l E U).obj M) W m
  have hr := inverseRestriction_apply l E P U M ((proEtaleBaseChange g).op.obj W) m
  exact (congrArg
    (fun z ↦ ((inverseRestriction l E P U).hom.app M).val.app
      ((proEtaleBaseChange g).op.obj W) z)
    ((congrArg
      (fun z ↦ ((inversePushforward R _ P.integral P.integral_natural g).hom.app
        ((ordinaryCompositeRestriction l E U).obj M)).val.app W z) hb).trans hx)).trans hr
    |>.symm

/-- Ordinary ring presentations transport restriction and direct image in a commuting cube.
Source: Stacks, Modules on Sites, Tags 03D6 and 03D7; the ordinary steps 1--2 of
lem-sf-native-scalar-restriction-cube.
(blueprint: lem-sf-native-scalar-ordinary-restriction-cube).

Proof: compose the two restrictions using comapComp and the section-module equivalence.
Transport the section rings through P.integral and P.closure. Their scalar square makes
this comparison linear. The naturality fields similarly identify the direct-image
coefficient maps; the pushforward composition isomorphisms give the two comparisons.
All comparisons are identity on underlying abelian sections. Evaluating both cube paths
at a site object and a section therefore proves equality, including on empty objects. -/
theorem nativeScalarOrdinaryRestrictionCube
    (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    (P : NativeScalarRingModel l E a) :
    ∃ k : ∀ T : Scheme.{u},
        ordinaryCompositeRestriction l E T ⋙ (P.integralEquivalence T).inverse ≅
          (P.closureEquivalence T).inverse ⋙ proEtaleRingRestrictScalars (a.map T),
      ∀ {U V : Scheme.{u}} (g : U ⟶ V),
        ∃ (x : CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g ⋙
              (P.integralEquivalence V).inverse ≅
            (P.integralEquivalence U).inverse ⋙
              proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g))
          (y : CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g ⋙
              (P.closureEquivalence V).inverse ≅
            (P.closureEquivalence U).inverse ⋙
              proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)),
          ∀ M,
            (k V).hom.app
                ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).obj M) ≫
              (proEtaleRingRestrictScalars (a.map V)).map (y.hom.app M) ≫
              (proEtaleRingRestrictionDirectImage g
                (R.ring V) (S.ring V) (R.ring U) (S.ring U)
                (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).hom.app
                  ((P.closureEquivalence U).inverse.obj M) =
            (P.integralEquivalence V).inverse.map
                ((ordinaryCompositeSquare l E g).hom.app M) ≫
              x.hom.app ((ordinaryCompositeRestriction l E U).obj M) ≫
              (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).map
                ((k U).hom.app M) := by
  refine ⟨inverseRestriction l E P, ?_⟩
  intro U V g
  exact ⟨inversePushforward R _ P.integral P.integral_natural g,
    inversePushforward S _ P.closure P.closure_natural g,
    inverseOrdinaryCube l E a P g⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport.NativeScalarRestriction

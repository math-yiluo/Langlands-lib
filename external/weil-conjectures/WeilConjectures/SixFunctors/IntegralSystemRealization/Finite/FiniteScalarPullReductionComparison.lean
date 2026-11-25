/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarOrdinaryReductionIso
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.FiniteScalarReductionCounitNormalization

/-! # Finite scalar target comparison on a good complex -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.scalarReductionTargetDerived WeilConjectures.scalarReductionSourceDerived
  AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem derived_iso_model
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (P : CochainComplex C ℤ) (K : DerivedCategory C)
    (ε : K ⟶ DerivedCategory.Q.obj P) :
    (Functor.mapDerivedCategoryNatIso e).hom.app K ≫
        G.mapDerivedCategory.map ε ≫ G.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategory.map ε ≫ F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  rw [← reassoc_of% ((Functor.mapDerivedCategoryNatIso e).hom.naturality ε),
    Functor.mapDerivedCategoryNatIso_fac]

/-- Normalize the target scalar presentation and geometric presentation on a good complex.
Source: Stacks Tags 07A6, 06YY and 0D6E
(blueprint: lem-sf-finite-scalar-pull-reduction-comparison).
Proof: naturality of the derived finite geometric presentation carries the finite
scalar computation map to its ordinary complex. Its localization factor identifies
the resulting map with the degreewise geometric presentation. The scalar counit
normalization replaces the finite scalar presentation followed by that computation
map by the pbc counit followed by the ordinary scalar presentation. Naturality of
the geometric localization factor moves the latter presentation to complexes.
Only the input complex on Y must be good; no condition on its pullback is used. -/
theorem finiteScalarPullReductionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    let := scalarReductionExtensionAdditive.{u, u} l E Y n
    let a := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
    let S := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
    let T := proEtaleRingModulePullback f (S.ring Y) (S.ring X) (S.pull f)
    let TD := PurCompactSupport.pull S f
    let I := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
    let CY := ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj
    let BY := ((pbcExtend (a.map Y)).mapHomologicalComplex (.up ℤ)).obj P.obj
    let αYc := (NatTrans.mapHomologicalComplex
      (finiteScalarOrdinaryReductionIso l E Y n).hom (.up ℤ)).app P.obj
    let lam := PurCompactSupport.finitePullbackIso l E n f
    TD.map ((PurCompactSupport.finiteReductionIso l E Y n).hom.app
        (DerivedCategory.Q.obj P.obj)) ≫
      (Functor.mapDerivedCategoryNatIso lam).hom.app
        ((scalarReductionDerivedExtension l E Y n).obj (DerivedCategory.Q.obj P.obj)) ≫
      (finiteDerivedPullback l E n f).map
        (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom ≫
      I.mapDerivedCategoryFactors.hom.app CY =
    TD.map (pbcComplexCounit (a.map Y) P.obj) ≫
      T.mapDerivedCategoryFactors.hom.app BY ≫
      DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map αYc) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex lam (.up ℤ)).hom.app CY) := by
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let := scalarReductionExtensionAdditive.{u, u} l E Y n
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
  let S := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
  let T := proEtaleRingModulePullback f (S.ring Y) (S.ring X) (S.pull f)
  let TD := PurCompactSupport.pull S f
  let I := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let CY := ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj
  let BY := ((pbcExtend (a.map Y)).mapHomologicalComplex (.up ℤ)).obj P.obj
  let αYc := (NatTrans.mapHomologicalComplex
    (finiteScalarOrdinaryReductionIso l E Y n).hom (.up ℤ)).app P.obj
  let lam := PurCompactSupport.finitePullbackIso l E n f
  let lamD := Functor.mapDerivedCategoryNatIso lam
  let lamc := (NatIso.mapHomologicalComplex lam (.up ℤ)).hom.app CY
  let ay := (PurCompactSupport.finiteReductionIso l E Y n).hom.app
    (DerivedCategory.Q.obj P.obj)
  let εy := (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom
  let cy := pbcComplexCounit (a.map Y) P.obj
  let fy := T.mapDerivedCategoryFactors.hom.app BY
  let hy := T.mapDerivedCategoryFactors.hom.app CY
  have hlam : lamD.hom.app ((scalarReductionDerivedExtension l E Y n).obj
          (DerivedCategory.Q.obj P.obj)) ≫ (finiteDerivedPullback l E n f).map εy ≫
        I.mapDerivedCategoryFactors.hom.app CY =
      TD.map εy ≫ hy ≫ DerivedCategory.Q.map lamc := by
    exact derived_iso_model lam CY _ εy
  have hY : ay ≫ εy = cy ≫ DerivedCategory.Q.map αYc :=
    finiteScalarReductionCounitNormalization l E Y n P
  have hn := T.mapDerivedCategoryFactors.hom.naturality αYc
  dsimp only [Functor.comp_map] at hn
  have hY' : TD.map ay ≫ TD.map εy =
      TD.map cy ≫ TD.map (DerivedCategory.Q.map αYc) := by
    simpa only [Functor.map_comp] using congrArg (fun k ↦ TD.map k) hY
  change TD.map ay ≫ lamD.hom.app
      ((scalarReductionDerivedExtension l E Y n).obj (DerivedCategory.Q.obj P.obj)) ≫
      (finiteDerivedPullback l E n f).map εy ≫ I.mapDerivedCategoryFactors.hom.app CY =
    TD.map cy ≫ fy ≫ DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map αYc) ≫
      DerivedCategory.Q.map lamc
  erw [hlam, reassoc_of% hY', reassoc_of% hn]
  rfl

end WeilConjectures.IntegralSystemRealization

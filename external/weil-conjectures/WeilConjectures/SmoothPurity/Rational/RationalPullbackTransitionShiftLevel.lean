/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftRoos
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelConstruction
import WeilConjectures.CategoryTheory.Limits.PreservesProductMapIso

/-! # Shift compatibility of the scalar/pullback chain comparison

The finite scalar pullback maps `scalarPullbackLevel` commute with the termwise shift
comparisons of the integral pullback towers (`scalarPullbackLevel_shift`), which gives the level
and product squares of the scalar pullback tower (`scalarPullbackTower_levelShift`,
`scalarPullbackTower_productSquare`). Feeding these, together with the signed Roos
coordinates (`roosShiftInl_of_shiftCoordinates`, `roosShiftInr_of_shiftCoordinates`), into
the Roos chain criterion of
`WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftRoos` shows that the
Roos scalar/pullback chain comparison commutes with the signed Roos shifts
(`scalarPullbackRoosChain_commShift`).

This is the level step of the proof of `rationalPullbackTransitionShift`.
Source: current blueprint sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, Weil-structures paragraph.
(blueprint: lem-sf-rational-pullback-transition-shift).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

section LevelShift
open CategoryTheory.Limits Opposite
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The finite scalar pullback map is the generator-normalized module map in each degree. -/
private theorem scalarPullbackLevel_app_f {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) :
    ((scalarPullbackLevel l E L ι f n).app P).f i = pullbackScalarModule l E L ι f n (P.X i) := by
  let α : integralOperationsPullbackLevel l E f n ⋙
      (integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ) ⟶
      (integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ) ⋙
        integralOperationsPullbackLevel l L f n :=
    { app := fun P ↦
        { f := fun i ↦ pullbackScalarModule l E L ι f n (P.X i)
          comm' := fun i j _ ↦ (pullbackScalarModule_naturality l E L ι f n (P.d i j)).symm }
      naturality := fun P Q a ↦ HomologicalComplex.hom_ext _ _
        (fun i ↦ pullbackScalarModule_naturality l E L ι f n (a.f i)) }
  have hα : scalarPullbackLevel l E L ι f n = α :=
    (scalarPullbackLevel_existsUnique l E L ι f n).unique
      (scalarPullbackLevel_existsUnique l E L ι f n).exists.choose_spec
      (fun P i V x ↦ pullbackScalarModule_unit l E L ι f n (P.X i) V x)
  rw [hα]

/-- The scalar pullback tower at a fixed level is the finite scalar pullback map. -/
theorem scalarPullbackTower_app_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    ((scalarPullbackTower l E L ι f).app P).app (op n) = (scalarPullbackLevel l E L ι f n).app P :=
  (scalarPullbackTower_existsUnique l E L ι f).exists.choose_spec P n

/-- The finite scalar pullback maps are compatible with degree reindexing. -/
theorem scalarPullbackLevel_app_shift_f {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (r k : ℤ) :
    ((scalarPullbackLevel l E L ι f n).app (P⟦r⟧)).f k =
      ((scalarPullbackLevel l E L ι f n).app P).f (k + r) := by
  rw [scalarPullbackLevel_app_f, scalarPullbackLevel_app_f]
  rfl

/-- The product shift comparison composed with a shifted projection is the level shift. -/
@[reassoc]
theorem productShift_hom_π {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (r : ℤ) (n : ℕ) :
    (IntegralCompletedComparison.productShift l E f P r).hom ≫
        (Limits.Pi.π (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj
          (op n)) n)⟦r⟧' =
      Limits.Pi.π (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj (P⟦r⟧)).obj
          (op n)) n ≫ (IntegralCompletedComparison.levelShift l E f P r n).hom := by
  unfold IntegralCompletedComparison.productShift
  exact Limits.PreservesProduct.mapIso_trans_iso_symm_hom_map_π _
    (fun n ↦ IntegralCompletedComparison.levelShift l E f P r n) n

/-- The finite scalar pullback maps commute with the termwise shift comparisons. -/
theorem scalarPullbackLevel_shift {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (r : ℤ) :
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).map
        (IntegralCompletedComparison.levelShift l E f P r n).hom ≫
      (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
        _ ≫ ((scalarPullbackLevel l E L ι f n).app P)⟦r⟧' =
    (scalarPullbackLevel l E L ι f n).app (P⟦r⟧) ≫
      (integralOperationsPullbackLevel l L f n).map
        ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
          r).hom.app P) ≫
      (IntegralCompletedComparison.levelShift l L f
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P) r n).hom := by
  apply HomologicalComplex.hom_ext
  intro k
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, IntegralCompletedComparison.levelShift,
    Iso.app_hom]
  rw [scalarPullbackLevel_app_shift_f]
  erw [Functor.mapHomologicalComplex_map_f, Functor.mapCochainComplexShiftIso_hom_app_f]
  have hD : ((integralOperationsPullbackLevel l L f n).map
      ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
        r).hom.app P)).f k = 𝟙 _ := by
    have hg : ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
        r).hom.app P).f k = 𝟙 _ := Functor.mapHomologicalComplex_commShiftIso_hom_app_f _ _ _ _
    have hm : ((integralOperationsPullbackLevel l L f n).map
        ((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
          r).hom.app P)).f k =
        (SheafOfModules.restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (completedIntegralCommRingProjectionUnrestricted l L X n))).map
          ((integralOperationsLevelPullback l L f n).map
            ((unrestrictedIntegralReductionFunctor l L Y n).map
              (((((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
                r).hom.app P).f k))) := rfl
    rw [hm, hg]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    rfl
  erw [HomologicalComplex.comp_f, hD, CategoryTheory.Functor.map_id,
    Functor.mapCochainComplexShiftIso_hom_app_f, Category.id_comp, Category.id_comp]

end LevelShift

section ChainInstance
open CategoryTheory.Limits Opposite

/-- The signed Roos coordinates of an integral pullback shift give the first-inclusion
coordinate equation of the Roos criterion. -/
theorem roosShiftInl_of_shiftCoordinates (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (hc : IntegralCompletedComparison.ShiftCoordinates l E f c) :
    @RoosShiftInl _ _ _ _ _ _ _ (integralOperationsPullbackTowerFunctor l E f) c
      (fun P r ↦ IntegralCompletedComparison.productShift l E f P r) :=
  fun P r j ↦ (hc P r).1 j

/-- The signed Roos coordinates of an integral pullback shift give the second-inclusion
coordinate equation of the Roos criterion. -/
theorem roosShiftInr_of_shiftCoordinates (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (hc : IntegralCompletedComparison.ShiftCoordinates l E f c) :
    @RoosShiftInr _ _ _ _ _ _ _ (integralOperationsPullbackTowerFunctor l E f) c
      (fun P r ↦ IntegralCompletedComparison.productShift l E f P r) :=
  fun P r i j h ↦ (hc P r).2 i j h

/-- The level squares of the Roos criterion for the scalar pullback tower. -/
theorem scalarPullbackTower_levelShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P : CochainComplex (integralTowerModules l E X) ℤ) (r : ℤ) (n : ℕ) :
    ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).map
        (IntegralCompletedComparison.levelShift l E f P r n).hom ≫
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
        r).hom.app _ ≫ (((scalarPullbackTower l E L ι f).app P).app (op n))⟦r⟧' =
    ((scalarPullbackTower l E L ι f).app (P⟦r⟧)).app (op n) ≫
      ((integralOperationsPullbackTowerFunctor l L f).map
        ((((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).commShiftIso
          r).hom.app P)).app (op n) ≫
      (IntegralCompletedComparison.levelShift l L f
        (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj P) r n).hom := by
  rw [scalarPullbackTower_app_app, scalarPullbackTower_app_app]
  exact scalarPullbackLevel_shift l E L ι f n P r

/-- The product square of the Roos criterion for the scalar pullback tower. -/
theorem scalarPullbackTower_productSquare (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P : CochainComplex (integralTowerModules l E X) ℤ) (r : ℤ) :
    ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).map
        (IntegralCompletedComparison.productShift l E f P r).hom ≫
      (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).commShiftIso
        r).hom.app _ ≫
      (piComparison ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ))
          (fun n ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n)) ≫
        Limits.Pi.map (fun n ↦ ((scalarPullbackTower l E L ι f).app P).app (op n)))⟦r⟧' =
    piComparison ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ))
        (fun n ↦ ((integralOperationsPullbackTowerFunctor l E f).obj (P⟦r⟧)).obj (op n)) ≫
      Limits.Pi.map (fun n ↦ ((scalarPullbackTower l E L ι f).app (P⟦r⟧)).app (op n)) ≫
      Limits.Pi.map (fun n ↦ ((integralOperationsPullbackTowerFunctor l L f).map
        ((((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).commShiftIso
          r).hom.app P)).app (op n)) ≫
      (IntegralCompletedComparison.productShift l L f
        (((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ)).obj P) r).hom :=
  scalarRoos_productSquare (integralOperationsPullbackTowerFunctor l E f)
    (integralOperationsPullbackTowerFunctor l L f)
    ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ))
    (integralOrdinaryScalar l E L ι Y)
    (fun P r ↦ IntegralCompletedComparison.productShift l E f P r)
    (fun P r ↦ IntegralCompletedComparison.productShift l L f P r)
    (scalarPullbackTower l E L ι f)
    (fun P r n ↦ IntegralCompletedComparison.levelShift l E f P r n)
    (fun P r n ↦ IntegralCompletedComparison.levelShift l L f P r n)
    (fun P r n ↦ productShift_hom_π l E f P r n)
    (fun P r n ↦ productShift_hom_π l L f P r n)
    (fun P r n ↦ scalarPullbackTower_levelShift l E L ι f P r n) P r

/-- The Roos scalar/pullback chain comparison commutes with the signed Roos shifts. -/
theorem scalarPullbackRoosChain_commShift (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (cE : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
    (hcE : IntegralCompletedComparison.ShiftCoordinates l E f cE)
    (cL : (integralOperationsPullbackComplexFunctor l L f).CommShift ℤ)
    (hcL : IntegralCompletedComparison.ShiftCoordinates l L f cL) :
    @NatTrans.CommShift _ _ _ _ _ _ (scalarRoosChain (integralOperationsPullbackTowerFunctor l E f)
      (integralOperationsPullbackTowerFunctor l L f)
      ((integralOrdinaryScalar l E L ι X).mapHomologicalComplex (.up ℤ))
      (integralOrdinaryScalar l E L ι Y) (scalarPullbackTower l E L ι f)) ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ cE _)
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ cL) :=
  scalarRoosChain_commShift (eC := cE) (eC' := cL)
    (p := fun P r ↦ IntegralCompletedComparison.productShift l E f P r)
    (p' := fun P r ↦ IntegralCompletedComparison.productShift l L f P r)
    (hl := roosShiftInl_of_shiftCoordinates l E f cE hcE)
    (hr := roosShiftInr_of_shiftCoordinates l E f cE hcE)
    (hl' := roosShiftInl_of_shiftCoordinates l L f cL hcL)
    (hr' := roosShiftInr_of_shiftCoordinates l L f cL hcL)
    (hprod := scalarPullbackTower_productSquare l E L ι f)

end ChainInstance

end WeilConjectures

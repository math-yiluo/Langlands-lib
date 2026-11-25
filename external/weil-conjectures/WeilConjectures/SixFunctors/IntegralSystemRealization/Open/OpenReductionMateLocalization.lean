/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.OrdinaryLimitModel.OrdinaryOpenReductionMate
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenExtensionGoodComplex

/-! # Localization formula for the fixed open reduction mate

Source: Stacks Tags 03DI, 06YS, 06YY, 0GL1 and 0941; fix-prop-coherence.
(blueprint: lem-sf-open-reduction-mate-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

local instance localizationReduction_additive (W : Scheme.{u}) :
    (pullbackTensorOrdinaryReduction l E W).Additive :=
  (pullbackTensorOrdinary_additive l E W).1

local instance localizationOpen_additive {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).Additive :=
  (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).left_adjoint_additive

private theorem localized_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (K : CochainComplex C ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  unfold Adjunction.mapExactDerivedCategory
  rw [Adjunction.localization_unit_app]
  simp only [Iso.symm_hom, CatCommSq.iso, Category.assoc]
  rw [← R.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  simp

private theorem localized_homEquiv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (K : CochainComplex C ℤ) (N : CochainComplex D ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    a.mapExactDerivedCategory.homEquiv _ _
        (L.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) ≫
        R.mapDerivedCategoryFactors.hom.app N =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := R.mapDerivedCategoryFactors.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map f))
    (localized_unit a K)

private theorem openReduction_localization_of_good (system : Operations l E)
    (realization : RealizationModel l E system) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (hJ : integralOperationsGoodComplex l E Y
      (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapHomologicalComplex
         (.up ℤ)).obj P.obj))
    (hRJ : integralOperationsGoodComplex l E X
      (((integralOrdinaryPull l E j).mapHomologicalComplex (.up ℤ)).obj
        (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapHomologicalComplex
           (.up ℤ)).obj P.obj))) :
    (realization.openReduction l E j).app (DerivedCategory.Q.obj P.obj) ≫
        (calculus l E Y).reduction.map
          ((PurCompactSupport.openExtension
            (PurCompactSupport.completed l E) j).mapDerivedCategoryFactors.hom.app
            P.obj) ≫
        (pullbackTensorReductionModel l E Y).hom.app ⟨_, hJ⟩ =
      (Operations.shriek l E system j).map
          ((pullbackTensorReductionModel l E X).hom.app P) ≫
        (system.extension j).ordinary.mapDerivedCategoryFactors.hom.app
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj
            P.obj) ≫
        DerivedCategory.Q.map
          (realization.ordinary.openReductionComplex l E j (system.extension j) P.obj) := by
  let J := PurCompactSupport.openExtension (PurCompactSupport.completed l E) j
  let R := integralOrdinaryPull l E j
  let T := pullbackTensorSequenceInverse l E j
  let A := (pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)
  let B := (pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)
  let JP : (integralOperationsGoodComplex l E Y).FullSubcategory := ⟨_, hJ⟩
  let RJP : (integralOperationsGoodComplex l E X).FullSubcategory := ⟨_, hRJ⟩
  let η := ((PurCompactSupport.openAdjunction
    (PurCompactSupport.completed l E) j).mapHomologicalComplex (.up ℤ)).unit.app P.obj
  have hη : (PurCompactSupport.openDerivedAdjunction
      (PurCompactSupport.completed l E) j).unit.app (DerivedCategory.Q.obj P.obj) ≫
      (ringedPull l E j).map (J.mapDerivedCategoryFactors.hom.app P.obj) ≫
      R.mapDerivedCategoryFactors.hom.app JP.obj = DerivedCategory.Q.map η :=
    localized_unit (PurCompactSupport.openAdjunction
      (PurCompactSupport.completed l E) j) P.obj
  have hnat := (pullbackTensorReductionModel l E X).hom.naturality
    ((integralOperationsGoodComplex l E X).homMk (Y := RJP) η)
  change (calculus l E X).reduction.map (DerivedCategory.Q.map η) ≫
    (pullbackTensorReductionModel l E X).hom.app RJP =
      (pullbackTensorReductionModel l E X).hom.app P ≫ DerivedCategory.Q.map (A.map η)
    at hnat
  have hmodel := realization.model j JP hRJ
  have hpull := (realization.reductionPull j).hom.naturality
    (J.mapDerivedCategoryFactors.hom.app P.obj)
  have hηmap := congrArg (calculus l E X).reduction.map hη
  erw [Functor.map_comp, Functor.map_comp] at hηmap
  have hord :
      ((system.extension j).adjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ _
        (realization.ordinary.openReductionComplex l E j (system.extension j) P.obj) =
      A.map η ≫ realization.ordinary.reductionPullComplex l E j JP.obj := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact (unit_mateEquiv_symm
      (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j)
      (system.extension j).adjunction (realization.ordinary.reductionPull l E j).hom
      (P.obj.X i)).symm
  apply ((system.extension j).adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_left]
  apply (cancel_mono (T.mapDerivedCategoryFactors.hom.app (B.obj JP.obj))).mp
  conv_rhs => erw [Category.assoc]
  erw [localized_homEquiv]
  erw [hord, Functor.map_comp]
  erw [Adjunction.homEquiv_unit]
  have hmate := unit_mateEquiv_symm
    (PurCompactSupport.openDerivedAdjunction (PurCompactSupport.completed l E) j)
    (system.extension j).adj (realization.reductionPull j).hom
    (DerivedCategory.Q.obj P.obj)
  change (calculus l E X).reduction.map
      ((PurCompactSupport.openDerivedAdjunction
        (PurCompactSupport.completed l E) j).unit.app (DerivedCategory.Q.obj P.obj)) ≫
      (realization.reductionPull j).hom.app _ = _ at hmate
  erw [← Category.assoc, ← hmate]
  simp only [Functor.map_comp]
  erw [Category.assoc, Category.assoc, Category.assoc]
  erw [← reassoc_of% hpull]
  erw [hmodel]
  erw [reassoc_of% hηmap]
  erw [← Category.assoc, hnat, Category.assoc]
  rfl

/-- Localizing the ordinary open mate gives the specified derived mate.
Source: Stacks 03DI, 06YS, 06YY and 0GL1; fix-prop-coherence, open-factor sentence
(blueprint: lem-sf-open-reduction-mate-localization).

Proof: open extension is exact and preserves flat modules: tensor with an
extended module is the extension of tensor after restriction, and both open
functors are exact. Its direct-sum total-tensor comparison shows that extension
also preserves K-flat complexes. Thus the extended flat-term K-flat complex is
a good representative. Write the inverse mate as extension of the open unit,
followed by reductionPull and the system open counit. Localization preserves
the units and counits of these exact open adjunctions. Apply realization.model
to the extended good complex; its ordinary comparison is fixed by projections.
Naturality of the two reduction-model isomorphisms and their augmentation
normalizations cancel the intervening pullback factors. The triangle identities
leave precisely the localization of the ordinary mate on the right below.
This is a calculation of whole-system arrows, before any finite evaluation. -/
theorem openReduction_mate_localization (system : Operations l E)
    (realization : RealizationModel l E system) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    ∃ (s : ((calculus l E X).reduction ⋙ Operations.shriek l E system j).obj
        (DerivedCategory.Q.obj P.obj) ≅
      DerivedCategory.Q.obj
        (((system.extension j).ordinary.mapHomologicalComplex (.up ℤ)).obj
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj
            P.obj)))
      (t : (ringedOpen l E j ⋙ (calculus l E Y).reduction).obj
          (DerivedCategory.Q.obj P.obj) ≅
        DerivedCategory.Q.obj
          (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
            ((Functor.mapHomologicalComplex
              (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j)
              (.up ℤ)).obj P.obj))),
      s.hom =
        (Operations.shriek l E system j).map
          ((pullbackTensorReductionModel l E X).hom.app P) ≫
        (system.extension j).ordinary.mapDerivedCategoryFactors.hom.app
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj P.obj) ∧
      (realization.openReduction l E j).app (DerivedCategory.Q.obj P.obj) ≫ t.hom =
        s.hom ≫ DerivedCategory.Q.map
          (realization.ordinary.openReductionComplex l E j (system.extension j) P.obj)
      := by
  obtain ⟨hJ, hRJ⟩ := openExtension_goodComplex l E j P
  let s := (Operations.shriek l E system j).mapIso
      ((pullbackTensorReductionModel l E X).app P) ≪≫
    (system.extension j).ordinary.mapDerivedCategoryFactors.app
      (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj P.obj)
  let t := (calculus l E Y).reduction.mapIso
      ((PurCompactSupport.openExtension
            (PurCompactSupport.completed l E) j).mapDerivedCategoryFactors.app P.obj) ≪≫
    (pullbackTensorReductionModel l E Y).app ⟨_, hJ⟩
  refine ⟨s, t, rfl, ?_⟩
  change (realization.openReduction l E j).app (DerivedCategory.Q.obj P.obj) ≫
      ((calculus l E Y).reduction.map
        ((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapDerivedCategoryFactors.hom.app P.obj) ≫
        (pullbackTensorReductionModel l E Y).hom.app ⟨_, hJ⟩) =
    ((Operations.shriek l E system j).map
        ((pullbackTensorReductionModel l E X).hom.app P) ≫
      (system.extension j).ordinary.mapDerivedCategoryFactors.hom.app
        (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
      DerivedCategory.Q.map
        (realization.ordinary.openReductionComplex l E j (system.extension j) P.obj)
  simpa only [Category.assoc] using
    openReduction_localization_of_good l E system realization j P hJ hRJ

end WeilConjectures.IntegralSystemRealization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData

/-! # Strict representative normalization of completed pullback

Source: Bhatt--Scholze, Lemma 6.5.9(4), Remark 6.8.15; Stacks Tags 0941 and 099N(5).
(blueprint: lem-weil-pbc-completed-pullback-strict-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] completedModulePullback HasDerivedCategory.standard
  SheafOfModules.monoidalCategory completedReductionModuleTowerFunctor

private local instance (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private theorem constantRlim_lift
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (U : Scheme.{u})
    (C : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ)
    (I : CochainComplex (pbcTowers U (pbcAdicCompletion U d)) ℤ) [I.IsKInjective]
    (a : ((completedTowerConstant d U).mapHomologicalComplex (.up ℤ)).obj C ⟶ I) :
    (completedConstantRlimUnit d U).app (DerivedCategory.Q.obj C) ≫
        (completedTowerRlim d U).map
          ((completedTowerConstant d U).mapDerivedCategoryFactors.hom.app C ≫
            DerivedCategory.Q.map a) ≫
        (Functor.rightDerivedFunctorObjQIso
          (lim : pbcTowers U (pbcAdicCompletion U d) ⥤
            pbcModules U (pbcAdicCompletion U d)) I).hom =
      DerivedCategory.Q.map
        (((constLimAdj : completedTowerConstant d U ⊣ lim).mapHomologicalComplex
          (.up ℤ)).homEquiv C I a) := by
  let L : pbcTowers U (pbcAdicCompletion U d) ⥤
      pbcModules U (pbcAdicCompletion U d) := lim
  dsimp only [completedConstantRlimUnit]
  rw [(completedConstantRlimUnit_exists d U).exists.choose_spec C]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  have hn := L.rightDerivedFunctorUnitQ_naturality a
  rw [L.rightDerivedFunctorUnitQ_eq I] at hn
  have hn' := congrArg
    (fun f ↦ f ≫ (L.rightDerivedFunctorObjQIso I).hom) hn
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hn'
  erw [← hn']
  rw [← DerivedCategory.Q.map_comp]
  rfl

private def strictPullbackAugmentation
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ((completedTowerConstant d U).mapHomologicalComplex (.up ℤ)).obj
      (((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj K) ⟶
    ((completedTowerModulePullback h d).mapHomologicalComplex (.up ℤ)).obj
      ((completedReductionComplexTowerFunctor T d).obj K) :=
  letI := completedReductionModuleTowerFunctor_additive T d
  eqToHom (completedPullbackConstantComplex_eq h d K) ≫
    ((completedTowerModulePullback h d).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app K)

private theorem reductionCounitOnComplex_eq
    {B D : Type*} [Category* B] [Abelian B] [Category* D] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    (F : B ⥤ D) [F.Additive] (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex B ℤ) :
    reductionComplexCounit F L ε K =
      ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) := by
  simp only [reductionComplexCounit,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    CategoryTheory.Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]

private theorem reductionUnit_onComplex
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (T : Scheme.{u})
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion T d) K) :
    letI := completedReductionModuleTowerFunctor_additive T d
    (completedReductionTowerUnit d T).app (DerivedCategory.Q.obj K) ≫
        completedReductionTowerComplexCounit T d K =
      (completedTowerConstant d T).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app K) := by
  have := completedReductionModuleTowerFunctor_additive T d
  unfold completedReductionTowerComplexCounit reductionComplexCounit
  exact (completedReductionTowerUnit_exists d T).exists.choose_spec K hK

private theorem constantPullback_onComplex
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion T d) K) :
    (completedDerivedConstant d U).map (completedOrdinaryPullbackComplexCounit h d K) ≫
        (completedTowerConstant d U).mapDerivedCategoryFactors.hom.app
          (((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq h d K)) =
      (completedPullbackConstantIso h d).hom.app (DerivedCategory.Q.obj K) ≫
        (completedTowerPullback h d).map
          ((completedTowerConstant d T).mapDerivedCategoryFactors.hom.app K) ≫
        completedTowerPullbackComplexCounit h d
          (((completedTowerConstant d T).mapHomologicalComplex (.up ℤ)).obj K) := by
  exact (completedPullbackConstantIso_exists h d).exists.choose_spec K hK

private theorem map_unit_normalization
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (Q : E ⥤ D)
    {X Y Z W : C} {V V' : D} {K L M : E}
    (u : X ⟶ Y) (v : Y ⟶ Z) (s : X ⟶ W) (t : W ⟶ Z)
    (a : V ⟶ F.obj X) (b : V ⟶ V') (p : V' ⟶ Q.obj K)
    (e : F.obj Z ⟶ Q.obj M) (e' : F.obj W ⟶ Q.obj L)
    (z : K ⟶ L) (w : L ⟶ M)
    (hu : u ≫ v = s ≫ t) (he : F.map t ≫ e = e' ≫ Q.map w)
    (ha : b ≫ p ≫ Q.map z = a ≫ F.map s ≫ e') :
    a ≫ F.map (u ≫ v) ≫ e = b ≫ p ≫ Q.map (z ≫ w) := by
  rw [hu, Functor.map_comp, Category.assoc, he, ← reassoc_of% ha]
  simp only [Functor.map_comp]

private theorem pullbackUnit_tower
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion T d) K) :
    (completedPullbackConstantIso h d).hom.app (DerivedCategory.Q.obj K) ≫
        (completedTowerPullback h d).map
          ((completedReductionTowerUnit d T).app (DerivedCategory.Q.obj K) ≫
            completedReductionTowerComplexCounit T d K) ≫
        completedTowerPullbackComplexCounit h d
          ((completedReductionComplexTowerFunctor T d).obj K) =
      (completedDerivedConstant d U).map (completedOrdinaryPullbackComplexCounit h d K) ≫
        (completedTowerConstant d U).mapDerivedCategoryFactors.hom.app
          (((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (strictPullbackAugmentation d h K) := by
  have := completedReductionModuleTowerFunctor_additive T d
  have hn := (completedReductionPullbackComplexNat h d).naturality
    ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app K)
  change (completedTowerPullback h d).map (DerivedCategory.Q.map _) ≫
      completedTowerPullbackComplexCounit h d _ =
    completedTowerPullbackComplexCounit h d _ ≫ DerivedCategory.Q.map _ at hn
  unfold strictPullbackAugmentation
  exact map_unit_normalization (completedTowerPullback h d) DerivedCategory.Q
    _ _ _ _ _ _ _ _ _ _ _ (reductionUnit_onComplex d T K hK) hn
    (constantPullback_onComplex d h K hK)

/-- Compute the completed pullback comparison by the strict quotient augmentation
on a K-flat representative, followed by any map to a K-injective strict tower.

Source: Stacks Tag 0941, proof of lemma-derived-limit-is-ok; Tag 099N(5).
(blueprint: lem-weil-pbc-completed-pullback-strict-normalization).

Proof: normalize the reduction unit and the constant/pullback comparison on the
K-flat complex. Naturality of the pullback counit identifies their composite
with the strict module augmentation. Naturality then transports the equation
along e. The representative formula for the constant/Rlim unit cancels the
constant-tower localization factors. Naturality of the universal right-derived
unit and its computation on K-injective I identify the result with the localized
constant/limit adjunct of the augmentation followed by r. -/
theorem completedPullbackComparison_strict_normalization
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion T d) K)
    (K₀ : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) (e : K₀ ⟶ DerivedCategory.Q.obj K)
    (I : CochainComplex (pbcTowers U (pbcAdicCompletion U d)) ℤ) [I.IsKInjective]
    (r : ((completedTowerModulePullback h d).mapHomologicalComplex (.up ℤ)).obj
      ((completedReductionComplexTowerFunctor T d).obj K) ⟶ I) :
    letI := completedReductionModuleTowerFunctor_additive T d
    completedPullbackComparison h d K₀ ≫
        (completedTowerRlim d U).map
          ((completedTowerPullback h d).map
              ((completedReductionTower T d).map e ≫
                completedReductionTowerComplexCounit T d K) ≫
            completedTowerPullbackComplexCounit h d
              ((completedReductionComplexTowerFunctor T d).obj K) ≫
            DerivedCategory.Q.map r) ≫
        (Functor.rightDerivedFunctorObjQIso
          (lim : pbcTowers U (pbcAdicCompletion U d) ⥤
            pbcModules U (pbcAdicCompletion U d)) I).hom =
      (completedOrdinaryPullback h d).map e ≫
        completedOrdinaryPullbackComplexCounit h d K ≫
        DerivedCategory.Q.map
          (((constLimAdj : completedTowerConstant d U ⊣ lim).mapHomologicalComplex
            (.up ℤ)).homEquiv _ I ((eqToHom (completedPullbackConstantComplex_eq h d K) ≫
              ((completedTowerModulePullback h d).mapHomologicalComplex (.up ℤ)).map
                ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T)
                  (.up ℤ)).app K)) ≫ r)) := by
  let τ : completedOrdinaryPullback h d ⋙ completedDerivedConstant d U ⟶
      completedReductionTower T d ⋙ completedTowerPullback h d :=
    (completedPullbackConstantIso h d).hom ≫
      Functor.whiskerRight (completedReductionTowerUnit d T) (completedTowerPullback h d)
  have hn := τ.naturality e
  dsimp only [τ, NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map] at hn
  have hp := pullbackUnit_tower d h K hK
  have hpre :
      (completedPullbackConstantIso h d).hom.app K₀ ≫
        (completedTowerPullback h d).map ((completedReductionTowerUnit d T).app K₀) ≫
        (completedTowerPullback h d).map
          ((completedReductionTower T d).map e ≫ completedReductionTowerComplexCounit T d K) ≫
        completedTowerPullbackComplexCounit h d
          ((completedReductionComplexTowerFunctor T d).obj K) =
      (completedDerivedConstant d U).map
          ((completedOrdinaryPullback h d).map e ≫ completedOrdinaryPullbackComplexCounit h d K) ≫
        (completedTowerConstant d U).mapDerivedCategoryFactors.hom.app
          (((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (strictPullbackAugmentation d h K) := by
    simp only [Functor.map_comp, Category.assoc] at hp ⊢
    simp only [Category.assoc] at hn
    erw [← reassoc_of% hn]
    erw [hp]
  let f := (completedOrdinaryPullback h d).map e ≫ completedOrdinaryPullbackComplexCounit h d K
  let g := (completedTowerConstant d U).mapDerivedCategoryFactors.hom.app
      (((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (strictPullbackAugmentation d h K ≫ r)
  have hw :
      ((completedPullbackConstantIso h d).hom.app K₀ ≫
          (completedTowerPullback h d).map ((completedReductionTowerUnit d T).app K₀)) ≫
        ((completedTowerPullback h d).map
            ((completedReductionTower T d).map e ≫ completedReductionTowerComplexCounit T d K) ≫
          completedTowerPullbackComplexCounit h d
            ((completedReductionComplexTowerFunctor T d).obj K) ≫ DerivedCategory.Q.map r) =
      (completedDerivedConstant d U).map f ≫ g := by
    dsimp only [f, g]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ z ≫ DerivedCategory.Q.map r) hpre
  have hu := (completedConstantRlimUnit d U).naturality f
  change f ≫ (completedConstantRlimUnit d U).app (DerivedCategory.Q.obj _) =
    (completedConstantRlimUnit d U).app _ ≫
      (completedTowerRlim d U).map ((completedDerivedConstant d U).map f) at hu
  dsimp only [completedPullbackComparison]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  erw [hw]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hu]
  rw [constantRlim_lift]
  simp only [f, strictPullbackAugmentation, Category.assoc]

end WeilConjectures

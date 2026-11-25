/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullModel
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralPullbackModuleIdentification
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Identification of the ordinary cochain pullback model -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local implicit_reducible] PurCompactSupport.completed
  completedIntegralCommRingSheafUnrestricted
  ordinaryIntegralModulePush ordinaryIntegralPullComplex IntegralOnSlice.Site
attribute [-instance] OpenFactorCoherence.siteLocallyBijective
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] integralOperationsSiteSmall scalarReductionSourceDerived
  scalarReductionTargetDerived integralOperationsCommHasDerivedCategory
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance 4000] ordinaryIntegralModulePull_additive
attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted SheafOfModules.monoidalCategory
  ordinaryIntegralModulePull
  Functor.mapDerivedCategory proEtaleRingDerivedPullbackFactors
  ordinaryIntegralPullComplexCounit sfCompletedCoefficientMap ordinaryIntegralDirectRingMap

-- Check this identity before instantiating the large localization models.
private theorem iso_map_id_cancel {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {K : C} {L A B : D} (e : F.obj K ≅ L) (a : A ⟶ B) (b : B ⟶ L) :
    a ≫ b ≫ e.inv ≫ F.map (𝟙 K) ≫ e.hom = a ≫ b := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

private instance ordinary_pull_zero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    @Functor.PreservesZeroMorphisms
      (proEtaleRingModules Y ((PurCompactSupport.completed l E).ring Y)) _
      (proEtaleRingModules X ((PurCompactSupport.completed l E).ring X)) _ _ _
      (ordinaryIntegralModulePull l E f) :=
  Functor.preservesZeroMorphisms_of_iso (pullbackModuleIso l E f)

private theorem pullIso_factor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (pullIso l E f).hom.app (DerivedCategory.Q.obj P) ≫
        ordinaryIntegralPullComplexCounit l E f P =
      (proEtaleRingDerivedPullbackFactors f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).hom.app P ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pullbackModuleIso l E f).hom (.up ℤ)).app P) := by
  let b := pullbackModuleIso l E f
  have := preservesFiniteLimits_of_natIso b
  have := (ordinaryIntegralModuleAdjunction l E f).leftAdjoint_preservesColimits
  have := ordinaryIntegralModulePull_additive l E f
  let F := ordinaryIntegralModulePull l E f
  let W := HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)
  let : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  let ε := ordinaryIntegralPullCounit l E f
  let : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor ε W := by
    dsimp only [ε, ordinaryIntegralPullCounit, ordinaryIntegralDerivedPull]
    infer_instance
  let c : F.mapDerivedCategory ≅ ordinaryIntegralDerivedPull l E f :=
    Functor.leftDerivedUnique (ordinaryIntegralDerivedPull l E f) F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh.hom ε W
  have hc := Functor.leftDerivedNatTrans_app F.mapDerivedCategory
    (ordinaryIntegralDerivedPull l E f) F.mapDerivedCategoryFactorsh.hom ε W
    (𝟙 _) ((HomotopyCategory.quotient _ _).obj P)
  have hfac := Functor.mapDerivedCategoryNatIso_fac b P
  change c.hom.app _ ≫ (ordinaryIntegralPullCounit l E f).app _ = _ at hc
  simp only [NatTrans.id_app, Category.comp_id] at hc
  have he : (pullIso l E f).hom = (Functor.mapDerivedCategoryNatIso b ≪≫ c).hom := by
    unfold pullIso
    dsimp only [b, pullbackModuleIso]
    rfl
  rw [he]
  simp only [Iso.trans_hom, NatTrans.comp_app]
  unfold ordinaryIntegralPullComplexCounit
  rw [Category.assoc, ← NatTrans.naturality_assoc]
  erw [reassoc_of% hc]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [F, ordinaryIntegralPullComplex]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  let T := (ordinaryIntegralPullComplex l E f).obj P
  unfold proEtaleRingDerivedPullbackFactors
  exact (iso_map_id_cancel
    (K := ((HomotopyCategory.quotient (integralTowerModules l E X) (.up ℤ)).obj T))
    DerivedCategory.Qh
    ((DerivedCategory.quotientCompQhIso (integralTowerModules l E X)).app T)
    ((Functor.mapDerivedCategoryNatIso b).hom.app (DerivedCategory.Q.obj P))
    (F.mapDerivedCategoryFactors.hom.app P)).trans hfac

/-- The ordinary and ringed cochain pullbacks agree, preserving inverse unit sections
and the derived computation map.
Source: Stacks 03D2 and 06YY.
(blueprint: lem-sf-integral-pullback-complex-identification).

Proof: the direct-image ring maps agree, and the resulting pushforward isomorphism
is identity on sections. Uniqueness of left adjoints therefore identifies module
pullback and preserves unit sections. Apply it degreewise to complexes. The canonical
comparison of derived functors preserves their universal computation maps; naturality
across the cochain-to-homotopy quotient and cancellation of its comparison isomorphisms
give the displayed factorization. The inverse complex comparison carries ordinary unit
sections back to ringed unit sections by the inverse identity. -/
theorem pullbackComplexIdentification {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ b : OpenFactorCoherence.pullCx l E f ≅ ordinaryIntegralPullComplex l E f,
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
        (V : Y.ProEt) (x : (P.X i).val.obj (op V)),
        (((b.inv.app P).f i).val.app (op ((proEtaleBaseChange f).obj V)))
          ((((ordinaryIntegralModuleAdjunction l E f).unit.app (P.X i)).val.app (op V)) x) =
        (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull f)).unit.app (P.X i)).val.app (op V)) x) ∧
      (∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        (pullIso l E f).hom.app (DerivedCategory.Q.obj P) ≫
            ordinaryIntegralPullComplexCounit l E f P =
          (proEtaleRingDerivedPullbackFactors f ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull f)).hom.app P ≫
          DerivedCategory.Q.map (b.hom.app P)) := by
  refine ⟨NatIso.mapHomologicalComplex (pullbackModuleIso l E f) (.up ℤ), ?_, ?_⟩
  · intro P i V x
    exact pullbackModuleIso_inv_unit l E f (P.X i) V x
  · intro P
    exact pullIso_factor l E f P

end WeilConjectures.IntegralOrdinary

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement

/-! # Coefficient comparison for augmented strict integral towers

Source: Bhatt--Scholze Remark 6.8.15; Stacks 03D3, 03EL and 099N(5).
(blueprint: lem-weil-pbc-integral-coefficient-strict-tower-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard

attribute [local instance] completedReductionModuleTowerFunctor_additive
  completedTowerModulePullback_additive completedModulePullback_additive

private theorem completedTowerZero (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionModuleTowerFunctor W d).PreservesZeroMorphisms := by
  let := completedReductionModuleTowerFunctor_additive W d
  exact Functor.preservesZeroMorphisms_of_additive
    (F := completedReductionModuleTowerFunctor W d)

private theorem pbcTowerZero (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (show pbcModules W (pbcAdicCompletion W d) ⥤
        pbcTowers W (pbcAdicCompletion W d) from
      completedReductionModuleTowerFunctor W d).PreservesZeroMorphisms := by
  exact completedTowerZero W d

private theorem reductionCoefficientSquare
    (W : Scheme.{u})
    {R S Rn Sn : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (e : R ≅ S) (b : Rn ≅ Sn) (π : R ⟶ Rn) (ρ : S ⟶ Sn)
    (h : π ≫ b.hom = e.hom ≫ ρ) :
    ∃ β : pbcRestrict e.hom ⋙ pbcExtend π ⋙ pbcRestrict π ≅
        (pbcExtend ρ ⋙ pbcRestrict ρ) ⋙ pbcRestrict e.hom,
      ∀ M : pbcModules W S,
        (pbcScalarAdjunction π).unit.app ((pbcRestrict e.hom).obj M) ≫
            β.hom.app M = (pbcRestrict e.hom).map ((pbcScalarAdjunction ρ).unit.app M) := by
  let := (IntegralCoefficientPresentation.restrict_equivalence e).1
  let := (IntegralCoefficientPresentation.restrict_equivalence b).1
  let r := IntegralCoefficientPresentation.restrictionSquare π b.hom e.hom ρ h
  obtain ⟨α, hα⟩ := IntegralCoefficientPresentation.square_iso
    (pbcScalarAdjunction π) (pbcScalarAdjunction ρ)
    (pbcRestrict e.hom) (pbcRestrict b.hom) r
  refine ⟨Functor.isoWhiskerRight α (pbcRestrict π) ≪≫
    Functor.isoWhiskerLeft (pbcExtend ρ) r, ?_⟩
  intro M
  exact hα M

private theorem integralCoefficientLevelSquare
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) (n : ℕ) :
    ∃ β : pbcIntegralTransportModules W l E ⋙
          completedReductionLevel W (pbcIntegralDatum l E) n ≅
        (pbcExtend (completedIntegralCommRingProjectionUnrestricted l E W n) ⋙
          pbcRestrict (completedIntegralCommRingProjectionUnrestricted l E W n)) ⋙
            pbcIntegralTransportModules W l E,
      ∀ M : integralTowerModules l E W,
        ((completedReductionModuleUnit (pbcIntegralDatum l E) W).app
            ((pbcIntegralTransportModules W l E).obj M)).app (op n) ≫ β.hom.app M =
          (pbcIntegralTransportModules W l E).map
            ((pbcScalarAdjunction
              (completedIntegralCommRingProjectionUnrestricted l E W n)).unit.app M) := by
  let c := purCoefficientIso l E W
  let b := IntegralCoefficientPresentation.level l E W (integralCoefficientULift l E) n
  let π := pbcAdicProjection W (pbcIntegralDatum l E) n
  let ρ := completedIntegralCommRingProjectionUnrestricted l E W n
  have hc : (adicLisseForget W).mapIso c = integralDetailedCoefficientComparison W l E :=
    (purCoefficientIso_existsUnique l E W).exists.choose_spec
  have h : π ≫ b.hom = c.hom ≫ ρ := by
    apply (adicLisseForget W).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    have hn := (integralDetailedCoefficientComparison_exists W l E).exists.choose_spec n
    change (integralDetailedCoefficientComparison W l E).hom ≫ _ = _ at hn
    rw [← hc] at hn
    exact hn.symm
  obtain ⟨β, hβ⟩ := reductionCoefficientSquare W c b π ρ h
  have hr : pbcIntegralTransportModules W l E = pbcRestrict c.hom := by
    change SheafOfModules.restrictScalars (integralDetailedCoefficientComparison W l E).hom = _
    rw [← hc]
    rfl
  rw [hr]
  refine ⟨β, ?_⟩
  intro M
  rw [stratumModuleUnit_component]
  exact hβ M

private theorem sliceAugmentation_component
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (i : ℤ) :
    ((((IntegralOnSlice.augmentation l E W none).app P).app (op n)).f i) =
      (pbcScalarAdjunction
        (completedIntegralCommRingProjectionUnrestricted l E W n)).unit.app (P.X i) := by
  ext V x
  exact ((IntegralOnSlice.augmentation_existsUnique l E W none).exists.choose_spec
    P n i V x).trans
      ((pbcScalarAdjunction_exists
        (completedIntegralCommRingProjectionUnrestricted l E W n)).exists.choose_spec
          (P.X i) V x).symm

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

/-- The canonical completed/ordinary coefficient comparison of augmented strict towers.
Source: Bhatt--Scholze Remark 6.8.15; Stacks 03D3, 03EL and 099N(5).
(blueprint: lem-weil-pbc-integral-coefficient-strict-tower-comparison).

Proof: the completed coefficient comparison and its finite-level versions commute with
quotient projections. Scalar restriction along each coefficient isomorphism is an
equivalence. The adjunction square for extension and restriction therefore gives an
isomorphism between the two reductions preserving their tensor units. Lift it degreewise
to cochain complexes. Quotient units are epimorphisms, so their normalization forces both
tower-transition compatibility and naturality in the input complex. The resulting strict
tower isomorphism satisfies the displayed degreewise augmentation formula. -/
theorem integralCoefficientStrictTowerComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    ∃ c : pbcIntegralTransportComplex W l E ⋙
        completedReductionComplexTowerFunctor W (pbcIntegralDatum l E) ⋙
          HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      IntegralOnSlice.tower l E W none ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcIntegralTransportComplex W l E),
      ∀ (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (i : ℤ),
        ((completedReductionModuleUnit (pbcIntegralDatum l E) W).app
            ((pbcIntegralTransportModules W l E).obj (P.X i))).app (op n) ≫
            ((c.hom.app P).app (op n)).f i =
          (pbcIntegralTransportModules W l E).map
            ((((IntegralOnSlice.augmentation l E W none).app P).app (op n)).f i) := by
  let := pbcTowerZero W (pbcIntegralDatum l E)
  let F := pbcIntegralTransportComplex W l E
  let H := HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (T := ℕᵒᵖ) (V := pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
      (c := .up ℤ)
  let R := F ⋙ completedReductionComplexTowerFunctor W (pbcIntegralDatum l E) ⋙ H
  let S := IntegralOnSlice.tower l E W none ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj F
  let U := F ⋙ (Functor.const ℕᵒᵖ)
  let α : U ⟶ R :=
    { app P := H.map ((NatTrans.mapHomologicalComplex
        (completedReductionModuleUnit (pbcIntegralDatum l E) W) (.up ℤ)).app (F.obj P))
      naturality P Q f := by
        apply NatTrans.ext
        funext n
        apply HomologicalComplex.hom_ext
        intro i
        exact NatTrans.congr_app
          ((completedReductionModuleUnit (pbcIntegralDatum l E) W).naturality
            ((F.map f).f i)) n }
  let β : U ⟶ S :=
    Functor.whiskerRight (IntegralOnSlice.augmentation l E W none)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)
  obtain ⟨c, hc, _⟩ := isoOfEpiAugmentations U R S α β (fun P n ↦ by
    apply HomologicalComplex.epi_of_epi_f
    intro i
    exact stratumModuleUnit_epi (pbcIntegralDatum l E) W ((F.obj P).X i) n.unop)
    (fun P n ↦ by
      obtain ⟨e, he⟩ := integralCoefficientLevelSquare l E W n.unop
      refine ⟨HomologicalComplex.Hom.isoOfComponents (fun i ↦ e.app (P.X i))
        (by
          intro i j hij
          exact (e.hom.naturality (P.d i j)).symm), ?_⟩
      apply HomologicalComplex.hom_ext
      intro i
      change _ ≫ e.hom.app (P.X i) =
        (pbcIntegralTransportModules W l E).map
          ((((IntegralOnSlice.augmentation l E W none).app P).app n).f i)
      rw [sliceAugmentation_component]
      exact he (P.X i))
  refine ⟨c, fun P n i ↦ ?_⟩
  exact congrArg (fun f ↦ f.f i) (NatTrans.congr_app (hc P) (op n))

end WeilConjectures

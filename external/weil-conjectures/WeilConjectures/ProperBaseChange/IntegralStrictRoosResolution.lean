/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoosComparisonSupplement
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Resolution normalization for the actual completed-coefficient Roos functor

Source: Stacks Tag 0941, lemma-derived-limit-is-ok.
(blueprint: lem-weil-pbc-integral-strict-roos-resolution).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local implicit_reducible] integralOperationsRoos integralOperationsTowerStep
  integralOperationsRoosFunctor CochainComplex.mappingCocone CochainComplex.mappingCone
  roosF roosConeFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The literal Roos functor agrees with the canonical right derived limit, with
normalization on every K-injective resolution of an entire strict tower.

Source: Stacks 0941, proof of lemma-derived-limit-is-ok.
(blueprint: lem-weil-pbc-integral-strict-roos-resolution).

Proof: use the existing normalizedRoosIso, which resolves the whole diagram and
inverts the zero-coordinate ordinary-limit inclusion. Transport its source by the
identity between the shifted mapping cone and integralOperationsRoos. The ordinary
limit of the complex diagram is canonically the termwise limit. Its comparison
with the derived limit is the universal right-derived unit. On a K-injective
complex that unit is inverse to rightDerivedFunctorObjQIso. Naturality along r
and cancellation of this unit give the displayed equation. The two coordinates
of the inclusion are respectively the limit projections and zero. -/
theorem pbc_integral_strict_roos_resolution
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (U : Scheme.{u}) :
    ∃ ρ : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ completedTowerRlim d U,
      ∀ (X I : CochainComplex (pbcTowers U (pbcAdicCompletion U d)) ℤ)
        (r : X ⟶ I) [QuasiIso r] [I.IsKInjective]
        (_hi : ∀ i : ℤ, Injective (I.X i)),
        ∃ ι : ((lim : pbcTowers U (pbcAdicCompletion U d) ⥤
              pbcModules U (pbcAdicCompletion U d)).mapHomologicalComplex (.up ℤ)).obj I ⟶
            integralOperationsRoos I.asFunctor,
          (∀ (n : ℕ) (i : ℤ),
            ι.f i ≫ (CochainComplex.mappingCocone.fst
                (towerTransitionEndomorphism (K := fun n : ℕ ↦ I.asFunctor.obj (op n))
                  (integralOperationsTowerStep I.asFunctor))).f i ≫
              (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i =
            ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I).f i) ∧
          (∀ (i j : ℤ) (hij : i + -1 = j),
            ι.f i ≫ (CochainComplex.mappingCocone.snd
                (towerTransitionEndomorphism (K := fun n : ℕ ↦ I.asFunctor.obj (op n))
                  (integralOperationsTowerStep I.asFunctor))).v i j hij = 0) ∧
          ρ.hom.app X ≫ (completedTowerRlim d U).map (DerivedCategory.Q.map r) ≫
              (Functor.rightDerivedFunctorObjQIso
                (lim : pbcTowers U (pbcAdicCompletion U d) ⥤
                  pbcModules U (pbcAdicCompletion U d)) I).hom ≫ DerivedCategory.Q.map ι =
            DerivedCategory.Q.map (integralOperationsRoosFunctor.map
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) := by
  classical
  let B := pbcModules U (pbcAdicCompletion U d)
  let : HasSheafify (ProEt.topology U) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} U
  let : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} U
  let : IsGrothendieckAbelian.{u + 1} B :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology U) ((adicLisseForget U).obj (pbcAdicCompletion U d))
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ B) :=
    reductionTower_isGrothendieckAbelian U ((adicLisseForget U).obj (pbcAdicCompletion U d))
  let : HasExactLimitsOfShape (Discrete ℕ) B :=
    ProEt.products_exact.{u, u, 0} U
      ((adicLisseForget U).obj (pbcAdicCompletion U d)) ℕ
  let F : (ℕᵒᵖ ⥤ B) ⥤ B := lim
  let η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  let eL := strictTowerLimitIso (A := B)
  let β := (Functor.isoWhiskerRight eL DerivedCategory.Q).hom ≫ η
  obtain ⟨e, he⟩ := normalizedRoosIso F.rightDerivedFunctor β (fun I hI ↦ by
    have := hI
    dsimp only [β, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, η]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance)
  let eF : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor (A := B) ≅ roosF :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro X Y f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      change integralOperationsRoosMap
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) = roosF.map f
      unfold integralOperationsRoosMap
      rw [WeilConjectures.cofiberMap_eq_coneMap _ _ _ _
        (integralOperationsRoos_square _)]
      rfl)
  let ρ := Functor.isoWhiskerRight eF DerivedCategory.Q ≪≫ e
  refine ⟨ρ, ?_⟩
  intro X I r _ _ hi
  let ι : (F.mapHomologicalComplex (.up ℤ)).obj I ⟶ integralOperationsRoos I.asFunctor :=
    eL.inv.app I ≫ roosι I
  have hunit : ρ.hom.app I ≫ (F.rightDerivedFunctorObjQIso I).hom ≫
      DerivedCategory.Q.map ι = 𝟙 _ := by
    have hc := congr_app he I
    change DerivedCategory.Q.map (roosι I) ≫ e.hom.app I = β.app I at hc
    have : QuasiIso (roosι I) := roos_inclusion_quasiIso I
    apply (cancel_epi (DerivedCategory.Q.map (roosι I))).1
    change DerivedCategory.Q.map (roosι I) ≫
        (DerivedCategory.Q.map (𝟙 (roosF.obj I)) ≫ e.hom.app I) ≫
          (F.rightDerivedFunctorObjQIso I).hom ≫ DerivedCategory.Q.map ι =
      DerivedCategory.Q.map (roosι I) ≫ 𝟙 _
    rw [DerivedCategory.Q.map_id, Category.id_comp, ← Category.assoc,
      ← Category.assoc, hc]
    dsimp only [β, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, η]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id]
    dsimp only [ι]
    rw [DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp_assoc,
      eL.hom_inv_id_app, DerivedCategory.Q.map_id, Category.id_comp]
  refine ⟨ι, ?_, ?_, ?_⟩
  · intro n i
    simp only [ι, HomologicalComplex.comp_f, Category.assoc]
    change (eL.inv.app I).f i ≫ (roosι I).f i ≫
      (CochainComplex.mappingCocone.fst (roosU I)).f i ≫
        (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i = _
    have hfst : roosι I ≫ CochainComplex.mappingCocone.fst (roosU I) ≫
        Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n =
        limit.π I.asFunctor (op n) := by
      simp [roosι, roosLift]
    have hh := congrArg (fun f ↦ (eL.inv.app I ≫ f).f i) hfst
    have hp := congrArg (fun f ↦ f.f i)
      (limit.isoLimitCone_inv_π
        ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩ (op n))
    have hp' : (eL.inv.app I ≫ limit.π I.asFunctor (op n)).f i =
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I).f i := by
      change ((limit.isoLimitCone
          ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
            HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩).inv ≫
          limit.π I.asFunctor (op n)).f i =
        ((HomologicalComplex.coneOfHasLimitEval I.asFunctor).π.app (op n)).f i
      exact hp
    simpa only [HomologicalComplex.comp_f, Category.assoc] using hh.trans hp'
  · intro i j hij
    simp only [ι, HomologicalComplex.comp_f, Category.assoc]
    change (eL.inv.app I).f i ≫ (roosι I).f i ≫
      (CochainComplex.mappingCocone.snd (roosU I)).v i j hij = _
    simp [roosι, roosLift]
  · have hn := ρ.hom.naturality r
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, ← Category.assoc, ← hn]
    rw [Category.assoc, Category.assoc, hunit, Category.comp_id]

end WeilConjectures

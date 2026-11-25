/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison

/-! # Natural transformation data for scalar Roos comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction
  integralScalarExtensionOfUniverses completedScalarChangeData

attribute [local implicit_reducible] completedOrdinaryScalarComplex integralOperationsRoos
  integralOperationsRoosFunctor completedScalarRoosEndomorphism
  completedDerivedScalarExtension completedOrdinaryScalarExtension completedScalarCounit
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  integralTowerHasDerivedCategory scalarReductionSourceDerived

private theorem fraction_naturality
    {A H : Type*} [Category A] [Abelian A] [HasDerivedCategory A] [Category H]
    (U V : DerivedCategory A ⥤ H) (G : CochainComplex A ℤ ⥤ H)
    (β : DerivedCategory.Q ⋙ U ⟶ G) (ε : DerivedCategory.Q ⋙ V ⟶ G)
    (res : ∀ Z : CochainComplex A ℤ, ∃ (K : CochainComplex A ℤ) (f : K ⟶ Z),
      IsIso (DerivedCategory.Q.map f) ∧ IsIso (ε.app K))
    {C D : CochainComplex A ℤ} [IsIso (ε.app C)]
    (h : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj D) :
    β.app C ≫ inv (ε.app C) ≫ V.map h ≫ ε.app D = U.map h ≫ β.app D := by
  obtain ⟨Z, s, hs, g, hh⟩ := DerivedCategory.right_fac h
  let := hs
  obtain ⟨K, f, hf, hK⟩ := res Z
  let := hf
  let := hK
  let p := f ≫ s
  let q := f ≫ g
  have hp : IsIso (DerivedCategory.Q.map p) := by
    dsimp only [p]
    rw [Functor.map_comp]
    infer_instance
  have hpq : DerivedCategory.Q.map p ≫ h = DerivedCategory.Q.map q := by
    simp only [p, q, Functor.map_comp, hh, Category.assoc, IsIso.hom_inv_id_assoc]
  apply (cancel_epi (U.map (DerivedCategory.Q.map p))).1
  have hb := β.naturality p
  have hep := ε.naturality p
  have heq := ε.naturality q
  have hbq := β.naturality q
  dsimp only [Functor.comp_map] at hb hep heq hbq
  rw [reassoc_of% hb]
  have hε : G.map p ≫ inv (ε.app C) =
      inv (ε.app K) ≫ V.map (DerivedCategory.Q.map p) := by
    apply (cancel_mono (ε.app C)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, hep,
      IsIso.inv_hom_id_assoc]
  rw [reassoc_of% hε]
  rw [← V.map_comp_assoc, hpq, heq]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← U.map_comp_assoc, hpq, hbq]

private def restrictedTower
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (X : Scheme.{u}) :=
  (coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

private def scalarRoosBridgeNat
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (X : Scheme.{u}) (ρ : IntegralComparisonRoosModel l L X) :
    DerivedCategory.Q ⋙ coefficientSequenceLimit l L X ≅
      restrictedTower l L X ⋙ integralOperationsRoosFunctor ⋙ DerivedCategory.Q := by
  unfold coefficientSequenceLimit coefficientSequenceDerivedRestriction
  exact Functor.isoWhiskerRight (coefficientSequenceRestriction l L X).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l L X) ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)) ρ.comparison

section
attribute [local implicit_reducible] coefficientSequenceLimit
/-- The natural bridge has precisely the specified pointwise Roos normalization.
Source: Stacks Tag 0941, functoriality of the derived comparison.
(blueprint: lem-trf-scalar-roos-naturality-data)
Proof: whiskering and composition of natural isomorphisms evaluate pointwise. -/
theorem scalarRoosBridgeNat_app
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (X : Scheme.{u}) (ρ : IntegralComparisonRoosModel l L X)
    (C : CochainComplex (coefficientSequenceModules l L X) ℤ) :
    (Functor.isoWhiskerRight
        (coefficientSequenceRestriction l L X).mapDerivedCategoryFactors
        (coefficientConstantTowerLimit l L X) ≪≫
      Functor.isoWhiskerLeft
        ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ))
        ρ.comparison).hom.app C =
        (integralComparisonRoosBridge l L X ρ C).hom ∧
      (Functor.isoWhiskerRight
        (coefficientSequenceRestriction l L X).mapDerivedCategoryFactors
        (coefficientConstantTowerLimit l L X) ≪≫
      Functor.isoWhiskerLeft
        ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ))
        ρ.comparison).inv.app C =
        (integralComparisonRoosBridge l L X ρ C).inv := by
  exact ⟨rfl, rfl⟩
end

attribute [local irreducible] coefficientSequenceLimit
attribute [local implicit_reducible] restrictedTower

private def roosScalarNat
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (α : restrictedTower l L X ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (completedOrdinaryScalarComplex l L F j X) ⟶
      (integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex (.up ℤ) ⋙
        restrictedTower l F X) :=
  scalarRoosTransformation (restrictedTower l L X) (restrictedTower l F X)
    ((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex (.up ℤ))
    (completedOrdinaryScalarExtension l L F j X) α

private def completedCounitNat
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u}) :
    DerivedCategory.Q ⋙ completedDerivedScalarExtension l L F j X ⟶
      completedOrdinaryScalarComplex l L F j X ⋙ DerivedCategory.Q where
  app C := completedScalarCounit l L F j X C
  naturality C D f := by
    change (completedDerivedScalarExtension l L F j X).map (DerivedCategory.Q.map f) ≫
        completedScalarCounit l L F j X D =
      completedScalarCounit l L F j X C ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l L F j X).map f)
    dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]
    with_unfolding_all
      exact homotopyCounit_naturality
        (completedOrdinaryScalarExtension.{u, u} l L F j X)
        (completedDerivedScalarExtension.{u, u} l L F j X)
        ((completedScalarChangeData.{u, u} l L F j X).choose_spec.choose_spec.choose_spec
          |>.choose_spec.2.2.choose_spec.choose) f

attribute [local irreducible] completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

private def scalarLimitComparison
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (α : restrictedTower l L X ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (completedOrdinaryScalarComplex l L F j X) ⟶
      (integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex (.up ℤ) ⋙
        restrictedTower l F X) :
    DerivedCategory.Q ⋙ coefficientSequenceLimit l L X ⋙
      completedDerivedScalarExtension l L F j X ⟶
    (integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⋙ coefficientSequenceLimit l F X :=
  Functor.whiskerRight (scalarRoosBridgeNat l L X ρL).hom
      (completedDerivedScalarExtension l L F j X) ≫
    Functor.whiskerLeft (restrictedTower l L X ⋙ integralOperationsRoosFunctor)
      (completedCounitNat l L F j X) ≫
    Functor.whiskerRight (roosScalarNat l L F j X α) DerivedCategory.Q ≫
    Functor.whiskerLeft
      ((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex (.up ℤ))
      (scalarRoosBridgeNat l F X ρF).inv

end WeilConjectures

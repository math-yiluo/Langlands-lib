/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.TraceFormula.Scalar.ScalarRoosNaturalityData
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison

/-! # Derived naturality of scalar Roos comparison -/

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
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  integralTowerHasDerivedCategory scalarReductionSourceDerived restrictedTower

attribute [local implicit_reducible] coefficientSequenceLimit
attribute [local irreducible] completedDerivedScalarExtension
  completedOrdinaryScalarExtension completedScalarCounit

private theorem scalarRoos_naturality_of_bridge
    {A B : Type*} [Category A] [Category B] (G : A ⥤ B)
    {C D C' D' : A} (eC : C ≅ C') (eD : D ≅ D')
    {KC KD TC TD VC VD : B}
    (cC : G.obj C' ⟶ KC) (cD : G.obj D' ⟶ KD)
    (rC : KC ⟶ TC) (rD : KD ⟶ TD) (bC : VC ≅ TC) (bD : VD ≅ TD)
    {UC UD : B} (a : VC ⟶ UC) (h : UC ⟶ UD) (d : UD ⟶ VD) (f : C ⟶ D)
    (w : (G.map eC.hom ≫ cC ≫ rC ≫ bC.inv) ≫ a ≫ h ≫ d =
      G.map f ≫ (G.map eD.hom ≫ cD ≫ rD ≫ bD.inv)) :
    cC ≫ rC ≫ bC.inv ≫ a ≫ h ≫ d ≫ bD.hom =
      G.map (eC.inv ≫ f ≫ eD.hom) ≫ cD ≫ rD := by
  have w' := congrArg (fun k ↦ G.map eC.inv ≫ k ≫ bD.hom) w
  simp only [Category.assoc, ← Functor.map_comp_assoc] at w'
  simp only [eC.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    bD.inv_hom_id, Category.comp_id] at w'
  simpa only [Functor.map_comp, Category.assoc] using w'

/-- A natural ordinary scalar map of whole towers is natural on derived morphisms
once the source cochain counit becomes invertible after total limit.

Source: Stacks Project, Tags 06YY and 0941, calculus of fractions and K-flat resolutions.
(blueprint: lem-trf-scalar-roos-derived-naturality)

Proof: form the natural transformation on complexes by the source Roos bridge,
the universal scalar counit, the diagonal scalar Roos map, the given tower map,
and the inverse target bridge. The system scalar counit is a second natural
transformation to the same functor. Represent a derived morphism by a right
fraction and resolve its intermediate complex by a K-flat complex. Both the
localized denominator and the system counit on that resolution are invertible.
Naturality for the two chain maps in the fraction and cancellation then give
the displayed equality. No exactness of ordinary system scalar extension is used.
-/
theorem scalarRoosDerivedNaturality
    (l : ℕ) [Fact l.Prime]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (X : Scheme.{u})
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (α : ((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (completedOrdinaryScalarComplex l L F j X) ⟶
      (integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex (.up ℤ) ⋙
        (coefficientSequenceRestriction l F X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex)
    (C D : CochainComplex (coefficientSequenceModules l L X) ℤ)
    [IsIso ((coefficientSequenceLimit l F X).map
      ((integralComparisonSequenceScalarModel l L F j X).ε.app C))]
    (h : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj D) :
    completedScalarCounit l L F j X
        (integralOperationsRoos
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor) ≫
      DerivedCategory.Q.map
        (scalarRoosMap (completedOrdinaryScalarExtension l L F j X)
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            C).asFunctor ≫ integralOperationsRoosMap (α.app C)) ≫
      (integralComparisonRoosBridge l F X ρF _).inv ≫
      inv ((coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l L F j X).ε.app C)) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map h) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSequenceScalarModel l L F j X).ε.app D) ≫
      (integralComparisonRoosBridge l F X ρF _).hom =
    (completedDerivedScalarExtension l L F j X).map
      ((integralComparisonRoosBridge l L X ρL C).inv ≫
        (coefficientSequenceLimit l L X).map h ≫
        (integralComparisonRoosBridge l L X ρL D).hom) ≫
      completedScalarCounit l L F j X
        (integralOperationsRoos
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            D).asFunctor) ≫
      DerivedCategory.Q.map
        (scalarRoosMap (completedOrdinaryScalarExtension l L F j X)
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            D).asFunctor ≫ integralOperationsRoosMap (α.app D)) := by
  let HF := coefficientSequenceLimit l F X
  let m := integralComparisonSequenceScalarModel l L F j X
  let β := scalarLimitComparison l L F j X ρL ρF α
  let ε := Functor.whiskerRight m.ε HF
  have res (Z : CochainComplex (coefficientSequenceModules l L X) ℤ) :
      ∃ (K : CochainComplex (coefficientSequenceModules l L X) ℤ) (f : K ⟶ Z),
        IsIso (DerivedCategory.Q.map f) ∧ IsIso (ε.app K) := by
    obtain ⟨K, f, hK, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l L X) Z
    have hKε : IsIso (m.ε.app K) := m.computes K hK
    exact ⟨K, f, (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf,
      Functor.map_isIso HF (m.ε.app K)⟩
  have : IsIso (ε.app C) :=
    inferInstanceAs (IsIso (HF.map (m.ε.app C)))
  have hn := fraction_naturality
    (coefficientSequenceLimit l L X ⋙ completedDerivedScalarExtension l L F j X)
    (m.T ⋙ HF) _ β ε res h
  have hb (Z : CochainComplex (coefficientSequenceModules l L X) ℤ) :
      β.app Z = (completedDerivedScalarExtension l L F j X).map
          (integralComparisonRoosBridge l L X ρL Z).hom ≫
        completedScalarCounit l L F j X (integralOperationsRoos
          (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
            Z).asFunctor) ≫
        DerivedCategory.Q.map
          (scalarRoosMap (completedOrdinaryScalarExtension l L F j X)
            (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
              Z).asFunctor ≫ integralOperationsRoosMap (α.app Z)) ≫
        (integralComparisonRoosBridge l F X ρF _).inv := by
    have hL := (scalarRoosBridgeNat_app l L X ρL Z).1
    have hF := (scalarRoosBridgeNat_app l F X ρF
      (((integralComparisonSequenceScalarModel l L F j X).E.mapHomologicalComplex
        (.up ℤ)).obj Z)).2
    change (scalarRoosBridgeNat l L X ρL).hom.app Z = _ at hL
    change (scalarRoosBridgeNat l F X ρF).inv.app _ = _ at hF
    dsimp only [β, scalarLimitComparison, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, roosScalarNat, scalarRoosTransformation, completedCounitNat]
    rw [hL, hF]
    dsimp only [restrictedTower, Functor.comp_obj, integralOperationsRoosFunctor]
    rfl
  have hε (Z : CochainComplex (coefficientSequenceModules l L X) ℤ) :
      ε.app Z = HF.map (m.ε.app Z) := rfl
  simp only [hb, hε, Functor.comp_map] at hn
  exact scalarRoos_naturality_of_bridge (completedDerivedScalarExtension l L F j X)
    (integralComparisonRoosBridge l L X ρL C) (integralComparisonRoosBridge l L X ρL D)
    _ _ _ _ (integralComparisonRoosBridge l F X ρF _)
    (integralComparisonRoosBridge l F X ρF _) _ _ _ _ hn

end WeilConjectures

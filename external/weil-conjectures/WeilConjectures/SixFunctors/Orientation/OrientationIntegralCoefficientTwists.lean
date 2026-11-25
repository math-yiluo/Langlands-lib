/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.PuritySourceTransports
import all WeilConjectures.SixFunctors.Supporting.PositiveRootGeneratorExt
import WeilConjectures.SixFunctors.Supporting.PositiveRootTensorProduct
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SixFunctors.Integral.IntegralPullbackAugmentationAmbient
import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

set_option linter.privateModule false

/-! # Canonical positive coefficient-line comparisons

Source: main-20261015, definition-tate-twists, completed tensor and
scheme pullback conventions (blueprint: def-sf-orientation-integral-line-comparisons).
The original coefficient lines are reexported. Their normalized inverse-image
maps are supplied for arbitrary scheme morphisms, as required by orientations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] WeilConjectures.IntegralOnSlice.completion
  WeilConjectures.IntegralOnSlice.completionComparison
  WeilConjectures.IntegralOnSlice.completionUnit
  WeilConjectures.IntegralOnSlice.duality WeilConjectures.IntegralOnSlice.roosUnit
  WeilConjectures.IntegralAmbient.tensorTowerIso HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientTotalTensor SheafOfModules.monoidalCategory
  WeilConjectures.IntegralOnSlice.tower WeilConjectures.IntegralOnSlice.augmentation
  WeilConjectures.integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] WeilConjectures.completedIntegralCommRingSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

section IntegralLinePullbackProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
attribute [local implicit_reducible] PurCompactSupport.completed

end IntegralLinePullbackProof

section SingleTensor
open CategoryTheory.MonoidalCategory
variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
  [HasZeroObject C] [HasCountableCoproducts C]
  [(curriedTensor C).PreservesZeroMorphisms]
  [∀ M : C, ((curriedTensor C).obj M).PreservesZeroMorphisms]

private abbrev singleAt (M : C) (p : ℤ) :=
  (HomologicalComplex.single C (.up ℤ) p).obj M

private abbrev totalSingles (M N : C) (p q : ℤ) :=
  HomologicalComplex.mapBifunctor (singleAt M p) (singleAt N q) (curriedTensor C) (.up ℤ)

omit [HasCountableCoproducts C] in
private theorem singleTensorTermZero (M N : C) (p q a b : ℤ)
    (h : a ≠ p ∨ b ≠ q) :
    IsZero ((singleAt M p).X a ⊗ (singleAt N q).X b) := by
  rcases h with h | h
  · exact (tensorRight _).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  · exact (tensorLeft _).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

omit [HasCountableCoproducts C] in
private theorem singleTensorSupportZero (M N : C) (p q n : ℤ) (h : n ≠ p + q) :
    IsZero ((totalSingles M N p q).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  apply (singleTensorTermZero M N p q a b ?_).eq_of_src
  by_cases ha : a = p
  · right
    intro hb
    subst a
    subst b
    exact h hab.symm
  · exact Or.inl ha

private def singleTensorSummandIso (M N : C) (p q : ℤ) :
    (singleAt M p).X p ⊗ (singleAt N q).X q ≅
      (totalSingles M N p q).X (p + q) where
  hom := HomologicalComplex.ιMapBifunctor _ _ (curriedTensor C) (.up ℤ) p q (p + q) rfl
  inv := HomologicalComplex.mapBifunctorDesc (fun a b _ ↦
    if h : a = p ∧ b = q then
      (HomologicalComplex.XIsoOfEq _ h.1).hom ⊗ₘ
        (HomologicalComplex.XIsoOfEq _ h.2).hom
    else 0)
  hom_inv_id := by
    erw [HomologicalComplex.ι_mapBifunctorDesc]
    simp
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    by_cases ha : a = p
    · subst a
      have hb : b = q := by change p + b = p + q at hab; omega
      subst b
      erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
      simp
    · apply (singleTensorTermZero M N p q a b (Or.inl ha)).eq_of_src

private def singleTensorDegreeIso (M N : C) (p q : ℤ) :
    M ⊗ N ≅ (totalSingles M N p q).X (p + q) :=
  tensorIso (HomologicalComplex.singleObjXSelf (.up ℤ) p M).symm
      (HomologicalComplex.singleObjXSelf (.up ℤ) q N).symm ≪≫
    singleTensorSummandIso M N p q

private def singleTensorIso (M N : C) (p q : ℤ) :
    totalSingles M N p q ≅ singleAt (M ⊗ N) (p + q) := by
  let e := singleTensorDegreeIso M N p q
  let f : singleAt (M ⊗ N) (p + q) ⟶ totalSingles M N p q :=
    HomologicalComplex.mkHomFromSingle e.hom (by
      intro n hn
      apply (singleTensorSupportZero M N p q n
        (by change p + q + 1 = n at hn; omega)).eq_of_tgt)
  have hf (n : ℤ) : IsIso (f.f n) := by
    by_cases hn : n = p + q
    · subst n
      dsimp only [f]
      rw [HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) (p + q)
        (M ⊗ N) n hn).isIso (singleTensorSupportZero M N p q n hn) _
  let : ∀ n, IsIso (f.f n) := hf
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact (asIso f).symm

end SingleTensor

section RootTensor
attribute [local semireducible] coefficientTotalTensor
attribute [local implicit_reducible] coefficientTotalTensor
open CategoryTheory.MonoidalCategory

end RootTensor

private theorem isIso_map_comp_of_isIso_maps
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B C' : C} (f : A ⟶ B) (g : B ⟶ C')
    (hf : IsIso (F.map f)) (hg : IsIso (F.map g)) : IsIso (F.map (f ≫ g)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' hf hg

end WeilConjectures

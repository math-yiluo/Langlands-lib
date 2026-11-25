/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRawComposition

import Mathlib.Tactic.CategoryTheory.Slice
import WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexDerivedFactors

/-! # Exact derived-functor factors and the ordinary compositor

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindex-derived-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Preserve sharing of the dependent functor and representative aliases.
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus isoReductionCompletedMap
  integralOperationsTensorTowerFunctor
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Localization of three supplied chain maps with their defining equations.
Source: blueprint Steps 1 and 5; Stacks 015F
(blueprint: lem-pod-reindex-derived-pasting).
Proof: substitute the supplied equations, move the first chain map past the
second exact-functor factor by naturality, then apply factor composition and
functoriality of localization to the supplied chain square. -/
theorem podReindexDerivedPastingMaps
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ≅ F ⋙ G) (K : CochainComplex C₀ ℤ)
    {KF : CochainComplex C₁ ℤ} {KG KH : CochainComplex C₂ ℤ}
    (cf : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ KF)
    (cg : (G.mapHomologicalComplex (.up ℤ)).obj KF ⟶ KG)
    (cc : (H.mapHomologicalComplex (.up ℤ)).obj K ⟶ KH) (d : KH ⟶ KG)
    (df : F.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj KF)
    (dg : G.mapDerivedCategory.obj (DerivedCategory.Q.obj KF) ⟶ DerivedCategory.Q.obj KG)
    (dc : H.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj KH)
    (hdf : df = F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map cf)
    (hdg : dg = G.mapDerivedCategoryFactors.hom.app KF ≫ DerivedCategory.Q.map cg)
    (hdc : dc = H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map cc)
    (hK :
      (Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
          (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).symm).hom.app K))
    (hc :
      PodCompositionEquation (G.mapHomologicalComplex (.up ℤ))
        ((NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).symm).hom.app K)
        cf cg cc d) :
    PodCompositionEquation G.mapDerivedCategory
      ((Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
        (DerivedCategory.Q.obj K)) df dg dc (DerivedCategory.Q.map d) := by
  unfold PodCompositionEquation at hc ⊢
  rw [hdf, hdg, hdc]
  have hn := G.mapDerivedCategoryFactors.hom.naturality cf
  simp only [CategoryTheory.Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [hn]
  simp only [Category.assoc]
  slice_lhs 1 3 => exact hK
  simp only [Category.assoc]
  slice_lhs 2 4 =>
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, hc]
  rw [DerivedCategory.Q.map_comp]

end WeilConjectures

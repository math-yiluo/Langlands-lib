/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence

import Mathlib.Tactic.CategoryTheory.Slice

/-! # Exact derived-functor factors and the ordinary compositor

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindex-derived-factors).
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

private theorem composition_derived_factors
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ≅ F ⋙ G) (K : CochainComplex C₀ ℤ) :
    (Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
        (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).symm).hom.app K) := by
  have hc := Functor.mapDerivedCategoryCompIso_fac F G K
  have ha := Functor.mapDerivedCategoryNatIso_fac a K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  rw [hid] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [hc, ha]
  congr 2
  change _ = (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app K ≫ 𝟙 _
  exact (Category.comp_id _).symm

/-- The ordinary derived compositor agrees with the exact-functor factors.
Source: blueprint Steps 1 and 5; Stacks 015F
(blueprint: lem-pod-reindex-derived-factors).
Proof: use the factor formulas for deriving a natural isomorphism and a composite
functor. The homological-complex comparison for the identity is the identity.
Associativity yields the displayed equation on every complex. -/
theorem podReindexDerivedFactors
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [(isoReductionIntegralInverse l E f).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E f)]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E f)]
    [(isoReductionIntegralInverse l E h).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E h)]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E h)]
    [(isoReductionIntegralInverse l E (h ≫ f)).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E (h ≫ f))]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E (h ≫ f))]
    (K : CochainComplex (scalarReductionSource l E V) ℤ) :
    let α := NatIso.mapHomologicalComplex (A.composition h f) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h))
        (.up ℤ)).symm
    (A.compositionDerived l E h f).hom.app (DerivedCategory.Q.obj K) ≫
      (podOrdinaryReindex l E h).map
        ((isoReductionIntegralInverse l E f).mapDerivedCategoryFactors.hom.app K) ≫
      (isoReductionIntegralInverse l E h).mapDerivedCategoryFactors.hom.app
        ((isoReductionIntegralComplex l E f).obj K) =
    (isoReductionIntegralInverse l E (h ≫ f)).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map (α.hom.app K) := by
  intro α
  exact composition_derived_factors (isoReductionIntegralInverse l E f)
    (isoReductionIntegralInverse l E h) (isoReductionIntegralInverse l E (h ≫ f))
    (A.composition h f) K

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The identity comparison at a localized complex -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace WeilConjectures

/-- The derived identity comparison on a complex is its localized degreewise comparison.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5
(blueprint: lem-pod-identity-derived-factors).

Proof: the factor formula for the derived identity functor evaluates its comparison
at Q(K). The factor formula for mapDerivedCategoryNatIso then gives the composite.
The identity comparison on complexes has identity hom, so functoriality and the
right identity law identify the remaining factor. -/
theorem podIdentityDerivedFactors
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ≅ 𝟭 C) (K : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app
        (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app K) := by
  have hId : (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app K := by
    have h₂ : (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app K = 𝟙 _ := rfl
    rw [Functor.mapDerivedCategoryIdIso_hom_app, h₂]
    erw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  change (Functor.mapDerivedCategoryNatIso a).hom.app (DerivedCategory.Q.obj K) ≫
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj K) = _
  erw [hId, Functor.mapDerivedCategoryNatIso_fac]
  congr 2
  change _ = (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app K ≫ 𝟙 _
  exact (Category.comp_id _).symm

end WeilConjectures

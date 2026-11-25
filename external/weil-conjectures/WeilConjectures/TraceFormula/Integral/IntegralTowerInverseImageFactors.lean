/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# The tower inverse-image comparisons on complexes

The diagonal comparison and the whole-tower unit of exact inverse image, evaluated on
the localization of a complex, are the localizations of the corresponding strict maps.

Source: Stacks Project, Tags 03D6 and 0941
(blueprint: def-trf-integral-tower-inverse-image-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

section Coherence

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (F' : A ⥤ C) (G' : C ⥤ D)
  [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (e : F ⋙ G ≅ F' ⋙ G') (K : CochainComplex A ℤ)

/-- The derived image of a square of exact functors, evaluated on a complex. -/
private theorem derivedSquare_fac :
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) =
      (Functor.mapDerivedCategoryCompIso F G ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso F' G').symm).hom.app (DerivedCategory.Q.obj K) ≫
        G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
        G'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F G]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The same square with the source factor isomorphism moved to the other side. -/
private theorem derivedSquare_fac_inv :
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) ≫
        (Functor.mapDerivedCategoryCompIso F G ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso F' G').symm).hom.app (DerivedCategory.Q.obj K) ≫
        G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
        G'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) =
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  rw [← derivedSquare_fac, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

end Coherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The diagonal comparison of exact inverse image, on the localization of a complex,
is the localization of the levelwise identity `compConstIso`.
Source: Stacks 0941 (blueprint: def-trf-integral-tower-inverse-image-unit).

Proof: the diagonal is the composite of two composition isomorphisms and the
isomorphism induced by `compConstIso`; each is characterized by its compatibility
with the factorizations through the localization functors. -/
theorem integralTowerInverseImageDiagonal_hom_app_factors
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (integralComparisonConstantTower l E X).map
        ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P) ≫
      (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors.hom.app
          (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E g)).hom (.up ℤ)).app P) =
    (integralTowerInverseImageDiagonal l E g).hom.app (DerivedCategory.Q.obj P) ≫
      (integralDerivedTowerInverseImage l E g).map
        ((Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤
          ℕᵒᵖ ⥤ scalarReductionSource l E Y).mapDerivedCategoryFactors.hom.app P) ≫
      (integralTowerInverseImage l E g).mapDerivedCategoryFactors.hom.app
        (((Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤
          ℕᵒᵖ ⥤ scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ)).obj P) :=
  derivedSquare_fac _ _ _ _ (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E g)) P

/-- The whole-tower unit of exact inverse image, on the localization of a complex of
quotient systems, is the localization of the strict tensor-unit map.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit).

Proof: the derived unit is the composite of two composition isomorphisms and the
isomorphism induced by the strict unit; each is characterized by its compatibility
with the factorizations through the localization functors. -/
theorem integralDerivedTowerInverseImageUnit_hom_app_factors
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (integralDerivedTowerInverseImage l E g).map
        ((coefficientSequenceRestriction l E Y).mapDerivedCategoryFactors.inv.app C) ≫
      (integralDerivedTowerInverseImageUnit l E g).hom.app (DerivedCategory.Q.obj C) ≫
      (coefficientSequenceDerivedRestriction l E X).map
        ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C) ≫
      (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.hom.app
        (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C) =
    (integralTowerInverseImage l E g).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (integralTowerInverseImageUnit l E g).hom (.up ℤ)).app C) :=
  derivedSquare_fac_inv _ _ _ _ (integralTowerInverseImageUnit l E g) C

/-- Exact inverse image of the localization of a strict family from a constant tower
into a restricted quotient system, followed by the whole-tower unit, is the
localization of the strict composite family.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit).

Proof: compose the diagonal and unit formulas, using naturality of the factor
isomorphism of the tower inverse image for the strict family. -/
theorem integralTowerInverseImage_strictFamily_factors
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)).obj C) :
    (integralComparisonConstantTower l E X).map
        ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P) ≫
      (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors.hom.app
          (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E g)).hom (.up ℤ)).app P ≫
        ((integralTowerInverseImage l E g).mapHomologicalComplex (.up ℤ)).map b ≫
        (NatTrans.mapHomologicalComplex (integralTowerInverseImageUnit l E g).hom
          (.up ℤ)).app C) =
    (integralTowerInverseImageDiagonal l E g).hom.app (DerivedCategory.Q.obj P) ≫
      (integralDerivedTowerInverseImage l E g).map
        ((Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤
            ℕᵒᵖ ⥤ scalarReductionSource l E Y).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map b ≫
          (coefficientSequenceRestriction l E Y).mapDerivedCategoryFactors.inv.app C) ≫
      (integralDerivedTowerInverseImageUnit l E g).hom.app (DerivedCategory.Q.obj C) ≫
      (coefficientSequenceDerivedRestriction l E X).map
        ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C) ≫
      (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.hom.app
        (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C) := by
  have p1 := integralTowerInverseImageDiagonal_hom_app_factors l E g P
  have p2 := (integralTowerInverseImage l E g).mapDerivedCategoryFactors_hom_naturality b
  have p3 := integralDerivedTowerInverseImageUnit_hom_app_factors l E g C
  simp only [Functor.map_comp, Category.assoc]
  rw [p3]
  erw [reassoc_of% p2]
  rw [reassoc_of% p1]

end WeilConjectures

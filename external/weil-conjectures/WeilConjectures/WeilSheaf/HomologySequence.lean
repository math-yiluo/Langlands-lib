/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.WeilSheaf.Triangle

/-!
# The long exact sequence of cohomology sheaves of a triangle of Weil complexes

A distinguished triangle `K₁ → K₂ → K₃ → K₁[1]` of Weil complexes gives a long exact sequence

`⋯ → 𝓗ⁿK₁ → 𝓗ⁿK₂ → 𝓗ⁿK₃ --δ--> 𝓗ⁿ⁺¹K₁ → ⋯`

of Weil sheaves. It is that of the underlying triangle in the derived category of pro-étale Weil
sheaves (`DerivedCategory.HomologySequence`), the Weil sheaves forming an abelian subcategory
closed under kernels and cokernels, in which exactness is tested in the ambient category.

## Main definitions

- `AlgebraicGeometry.WeilComplex.homologySheafδ`: the connecting morphism.
- `AlgebraicGeometry.WeilComplex.homologySheaf_exact₁`, `homologySheaf_exact₂`,
  `homologySheaf_exact₃`: exactness of the long exact sequence.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

instance : Functor.Faithful (C := WeilSheaf k₀ l X) (WeilSheaf.objectProperty k₀ l X).ι :=
  inferInstanceAs (WeilSheaf.objectProperty k₀ l X).ι.Faithful

/-- A short complex of Weil sheaves is exact if and only if it is exact as a short complex of
pro-étale Weil sheaves. -/
lemma WeilSheaf.exact_iff_exact_map_ι (S : ShortComplex (WeilSheaf k₀ l X)) :
    S.Exact ↔ (S.map (WeilSheaf.objectProperty k₀ l X).ι).Exact :=
  (S.exact_map_iff_of_faithful _).symm

namespace WeilComplex

variable (T : Triangle (WeilComplex k₀ l X)) (n₀ n₁ : ℤ)

/-- The underlying triangle of pro-étale Weil complexes of a distinguished triangle of Weil
complexes is distinguished. -/
lemma map_ι_distinguished (hT : T ∈ distTriang _) :
    (WeilComplex.objectProperty k₀ l X).ι.mapTriangle.obj T ∈ distTriang _ :=
  (WeilComplex.objectProperty k₀ l X).ι.map_distinguished T hT

/-- The connecting morphism `𝓗ⁿ⁰K₃ ⟶ 𝓗ⁿ¹K₁`, `n₁ = n₀ + 1`, of the long exact sequence of
cohomology sheaves of a triangle `K₁ → K₂ → K₃ → K₁[1]` of Weil complexes. -/
noncomputable def homologySheafδ (h : n₀ + 1 = n₁) :
    (homologySheaf n₀).obj T.obj₃ ⟶ (homologySheaf n₁).obj T.obj₁ :=
  ObjectProperty.homMk (_root_.DerivedCategory.HomologySequence.δ
    ((WeilComplex.objectProperty k₀ l X).ι.mapTriangle.obj T) n₀ n₁ h)

variable (hT : T ∈ distTriang _)
include hT

@[reassoc (attr := simp)]
lemma homologySheaf_map_mor₂_comp_δ (h : n₀ + 1 = n₁) :
    (homologySheaf n₀).map T.mor₂ ≫ homologySheafδ T n₀ n₁ h = 0 :=
  ObjectProperty.hom_ext _ (_root_.DerivedCategory.HomologySequence.comp_δ _
    (map_ι_distinguished T hT) n₀ n₁ h)

@[reassoc (attr := simp)]
lemma homologySheafδ_comp_map_mor₁ (h : n₀ + 1 = n₁) :
    homologySheafδ T n₀ n₁ h ≫ (homologySheaf n₁).map T.mor₁ = 0 :=
  ObjectProperty.hom_ext _ (_root_.DerivedCategory.HomologySequence.δ_comp _
    (map_ι_distinguished T hT) n₀ n₁ h)

/-- Exactness of `𝓗ⁿK₁ → 𝓗ⁿK₂ → 𝓗ⁿK₃`. -/
lemma homologySheaf_exact₂ :
    (ShortComplex.mk ((homologySheaf n₀).map T.mor₁) ((homologySheaf n₀).map T.mor₂)
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])).Exact :=
  (WeilSheaf.exact_iff_exact_map_ι _).2
    (_root_.DerivedCategory.HomologySequence.exact₂ _ (map_ι_distinguished T hT) n₀)

/-- Exactness of `𝓗ⁿ⁰K₂ → 𝓗ⁿ⁰K₃ → 𝓗ⁿ¹K₁`. -/
lemma homologySheaf_exact₃ (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (homologySheaf_map_mor₂_comp_δ T n₀ n₁ hT h)).Exact :=
  (WeilSheaf.exact_iff_exact_map_ι _).2
    (_root_.DerivedCategory.HomologySequence.exact₃ _ (map_ι_distinguished T hT) n₀ n₁ h)

/-- Exactness of `𝓗ⁿ⁰K₃ → 𝓗ⁿ¹K₁ → 𝓗ⁿ¹K₂`. -/
lemma homologySheaf_exact₁ (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (homologySheafδ_comp_map_mor₁ T n₀ n₁ hT h)).Exact :=
  (WeilSheaf.exact_iff_exact_map_ι _).2
    (_root_.DerivedCategory.HomologySequence.exact₁ _ (map_ι_distinguished T hT) n₀ n₁ h)

end WeilComplex

end AlgebraicGeometry

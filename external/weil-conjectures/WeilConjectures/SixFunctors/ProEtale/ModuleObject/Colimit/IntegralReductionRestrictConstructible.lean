/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionTriangleNatural
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulatedBasic

/-!
# Restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` on bounded constructible complexes

Let `E ⊆ ℚ̄_ℓ` with ring of integers `𝒪_E`, `n : ℕ` and `X` a scheme. Write
`red : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧` for the reduction modulo `ℓⁿ` on bounded constructible
complexes (`ProEtale.CondensedRing.boundedConstructibleIntegersModPowReduction`).

Assume that the restriction of scalars `D(Res)` along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` sends bounded
constructible `𝒪_E ⧸ ℓⁿ`-complexes to bounded constructible `𝒪_E`-complexes
(`ProEtale.CondensedRing.RestrictScalarsIntegersModPowBoundedConstructible`). Then this file
restricts to the categories `Dᵇc(X)⟦-⟧`:

* the restriction of scalars `Res`
  (`ProEtale.CondensedRing.boundedConstructibleIntegersModPowRestriction`), which reflects
  isomorphisms;
* the adjunction `red ⊣ Res`
  (`ProEtale.CondensedRing.boundedConstructibleIntegersModPowAdjunction`), whose unit is, on the
  underlying complexes, the unit of `Mod.derivedExtendMapDerivedCategoryAdjunction`;
* the natural connecting morphism `δ : Res (red M) ⟶ M[1]` of the reduction triangle
  (`ProEtale.CondensedRing.boundedConstructibleIntegersModPowReductionδ`), for which
  `M --ℓⁿ--> M --η--> Res (red M) --δ--> M[1]` is distinguished in `Dᵇc(X)⟦𝒪_E⟧`
  (`ProEtale.CondensedRing.boundedConstructibleIntegersModPowReduction_distinguished`).

These are the inputs (`red ⊣ Res`, natural reduction triangles) of the formal mate arguments of
`WeilConjectures.CategoryTheory.Triangulated.ReductionTriangleMate` and
`WeilConjectures.CategoryTheory.Triangulated.ReductionTriangleDoubleMate` on the categories
`Dᵇc(X)⟦-⟧`, where the exceptional inverse images live.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

/-- **Restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` preserves bounded constructible
complexes** on `X`: for a bounded constructible `𝒪_E ⧸ ℓⁿ`-complex `M`, the `𝒪_E`-complex
`D(Res) M` is bounded constructible. (`D(Res)` is exact, so this amounts to: the restriction of
scalars of a constructible `𝒪_E ⧸ ℓⁿ`-module is a constructible `𝒪_E`-module.) -/
def RestrictScalarsIntegersModPowBoundedConstructible : Prop :=
  ∀ M, boundedConstructible (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) M →
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      ((Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory.obj M)

variable {ℓ E n X} (hX : RestrictScalarsIntegersModPowBoundedConstructible ℓ E n X)

/-- The restriction of scalars `Res : Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ ⥤ Dᵇc(X)⟦𝒪_E⟧` along
`𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` on bounded constructible complexes. -/
noncomputable def boundedConstructibleIntegersModPowRestriction :
    Dᵇc(X)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤ Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory)
    fun M ↦ hX M.obj M.property

/-- The restriction of scalars on bounded constructible complexes is compatible with the
inclusions. -/
noncomputable def boundedConstructibleIntegersModPowRestrictionCompatibility :
    boundedConstructibleIntegersModPowRestriction hX ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙
        (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

/-- The restriction of scalars on bounded constructible complexes reflects isomorphisms, as the
restriction of scalars on the derived categories does. -/
instance reflectsIsomorphisms_boundedConstructibleIntegersModPowRestriction :
    (boundedConstructibleIntegersModPowRestriction hX).ReflectsIsomorphisms where
  reflects {K L} f _ := by
    have : IsIso ((Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory.map f.hom) :=
      inferInstanceAs (IsIso ((boundedConstructible _).ι.map
        ((boundedConstructibleIntegersModPowRestriction hX).map f)))
    have : IsIso ((boundedConstructible _).ι.map f) :=
      isIso_of_reflects_iso f.hom (Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategory
    exact isIso_of_reflects_iso f (boundedConstructible _).ι

/-- The adjunction `red ⊣ Res` on bounded constructible complexes: the restriction of
`Mod.derivedExtendMapDerivedCategoryAdjunction` along the fully faithful inclusions. -/
noncomputable def boundedConstructibleIntegersModPowAdjunction :
    boundedConstructibleIntegersModPowReduction X ℓ E n ⊣
      boundedConstructibleIntegersModPowRestriction hX :=
  Adjunction.restrictFullyFaithful
    (Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction X ℓ E n))
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).symm
    (boundedConstructibleIntegersModPowRestrictionCompatibility hX).symm

/-- The unit of `red ⊣ Res` on bounded constructible complexes is, on the underlying complexes,
the unit of the derived adjunction. -/
lemma boundedConstructibleIntegersModPowAdjunction_unit_app_hom
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ((boundedConstructibleIntegersModPowAdjunction hX).unit.app K).hom =
      (Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction X ℓ E n)).unit.app
        K.obj := by
  simpa [boundedConstructibleIntegersModPowAdjunction, ObjectProperty.liftCompιIso,
    boundedConstructibleIntegersModPowReductionCompatibility,
    boundedConstructibleIntegersModPowRestrictionCompatibility] using
    Adjunction.map_restrictFullyFaithful_unit_app
      (Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowReduction X ℓ E n))
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E n).symm
      (boundedConstructibleIntegersModPowRestrictionCompatibility hX).symm K

/-- The connecting morphism `δ : Res (red M) ⟶ M[1]` of the reduction triangle on bounded
constructible complexes: the natural connecting morphism `integersModPowReductionδ` of the
derived categories, read through the inclusion, which commutes with the shifts. -/
noncomputable def boundedConstructibleIntegersModPowReductionδ :
    boundedConstructibleIntegersModPowReduction X ℓ E n ⋙
        boundedConstructibleIntegersModPowRestriction hX ⟶
      shiftFunctor (Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) (1 : ℤ) where
  app K := (ObjectProperty.fullyFaithfulι _).preimage
    ((integersModPowReductionδ ℓ E n X).app K.obj ≫
      ((boundedConstructible _).ι.commShiftIso (1 : ℤ)).inv.app K)
  naturality {K L} f := (ObjectProperty.fullyFaithfulι _).map_injective (by
    have h₁ := (integersModPowReductionδ ℓ E n X).naturality f.hom
    have h₂ := ((boundedConstructible _).ι.commShiftIso (1 : ℤ)).inv.naturality f
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_map] at h₁ h₂
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_map,
      ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    rw [← h₂]
    exact (Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans (Category.assoc _ _ _)))

/-- The connecting morphism on bounded constructible complexes is, on the underlying complexes,
`integersModPowReductionδ`, followed by the commutation of the inclusion with the shift. -/
lemma boundedConstructibleIntegersModPowReductionδ_app_hom
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ((boundedConstructibleIntegersModPowReductionδ hX).app K).hom =
      (integersModPowReductionδ ℓ E n X).app K.obj ≫
        ((boundedConstructible _).ι.commShiftIso (1 : ℤ)).inv.app K :=
  rfl

/-- **The natural reduction triangle on bounded constructible complexes**:
`M --ℓⁿ--> M --η--> Res (red M) --δ--> M[1]` is distinguished in `Dᵇc(X)⟦𝒪_E⟧`, its image in
the derived category being the natural reduction triangle
(`integersModPowReduction_distinguished`). -/
lemma boundedConstructibleIntegersModPowReduction_distinguished
    (M : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Triangle.mk (((ℓ : ℤ) ^ n) • 𝟙 M) ((boundedConstructibleIntegersModPowAdjunction hX).unit.app M)
      ((boundedConstructibleIntegersModPowReductionδ hX).app M) ∈ distTriang _ := by
  refine isomorphic_distinguished _ (integersModPowReduction_distinguished ℓ E n M.obj) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · dsimp [Functor.mapTriangle]
    simp only [Category.comp_id, Category.id_comp]
    exact (boundedConstructible _).ι.map_zsmul.trans (by simp)
  · dsimp [Functor.mapTriangle]
    simp [boundedConstructibleIntegersModPowAdjunction_unit_app_hom]
  · dsimp [Functor.mapTriangle]
    simp only [boundedConstructibleIntegersModPowReductionδ_app_hom,
      Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc, CategoryTheory.Functor.map_id,
      Category.comp_id,
      Category.id_comp]
    exact (congrArg _ (((boundedConstructible _).ι.commShiftIso (1 : ℤ)).inv_hom_id_app M)).trans
      (Category.comp_id _)

end AlgebraicGeometry.ProEtale.CondensedRing

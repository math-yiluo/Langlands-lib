/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekToLowerStarBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-!
# The derived comparison `D(j_!) ⟶ Rj_*` for a clopen immersion

For an immersion `j` that is both open and closed, the sheaf-level comparison `j_! ⟶ j_*` is
an isomorphism and `j_*` is exact. This file identifies the derived comparison
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekToLowerStar` with the levelwise
comparison `D(j_! ⟶ j_*)` followed by `D(j_*) ≅ Rj_*`, and identifies the derived composition
isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerStarComp` with the generic composition
isomorphism `CategoryTheory.Functor.rightDerivedFunctorCompIso'` of right derived functors.

## Main statements

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekToLowerStar_eq_of_isClosedImmersion`
- `AlgebraicGeometry.Etale.rightDerivedLowerStarComp_hom_comp_congr_hom_eq_compIso'`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Comp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁₂)_*` is the conjugate of the composition
isomorphism `(h₁₂)^* ≅ (h₂)^* ⋙ (h₁)^*` of pullbacks. -/
lemma lowerStarComp_hom_eq_conjugateEquiv {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    (lowerStarComp A h₁ h₂ h₁₂ hh).hom =
      conjugateEquiv ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))
        (upperStarLowerStarAdjunction A h₁₂) (upperStarComp A h₁ h₂ h₁₂ hh).hom := by
  simp only [upperStarComp, Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  exact (Equiv.apply_symm_apply _ _).symm

/-- The derived composition isomorphism `Rh₁_* ⋙ Rh₂_* ≅ R(h₁ ≫ h₂)_*`, transported along
`h₁₂ = h₁ ≫ h₂`, is the generic composition isomorphism of right derived functors attached to
the composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁₂)_*` of sheaf pushforwards. -/
lemma rightDerivedLowerStarComp_hom_comp_congr_hom_eq_compIso' {T S R : Scheme.{u}}
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh : h₁₂ = h₁ ≫ h₂) :
    (rightDerivedLowerStarComp A h₁ h₂).hom ≫ (rightDerivedLowerStarCongr A hh.symm).hom =
      (Functor.rightDerivedFunctorCompIso' (h₁)_*[A] (h₂)_*[A]
        (lowerStarComp A h₁ h₂ h₁₂ hh)).hom := by
  subst hh
  rw [rightDerivedLowerStarCongr_refl, Iso.refl_hom, Category.comp_id,
    Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
      (upperStarLowerStarAdjunction A h₁) (upperStarLowerStarAdjunction A h₂)
      (upperStarLowerStarAdjunction A (h₁ ≫ h₂)) _ (upperStarComp A h₁ h₂)
      (lowerStarComp_hom_eq_conjugateEquiv A h₁ h₂ _ rfl)]
  simp only [rightDerivedLowerStarComp, conjugateIsoEquiv_apply_inv, Iso.symm_hom,
    Iso.symm_inv]
  rfl

end Comp

section Clopen

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- For an immersion `j` that is both open and closed, the unit of `D(j_!) ⊣ D(j^*)`, followed
by `D(j^*)` of `D(j_! ⟶ j_*)` and `D(j_*) ≅ Rj_*`, and by the counit of `D(j^*) ⊣ Rj_*`, is the
identity. This is the derived counterpart of
`AlgebraicGeometry.Etale.unit_map_openImmersionLowerShriekToLowerStar_app_counit`. -/
lemma unit_map_mapDerivedCategory_openImmersionLowerShriekToLowerStar_counit {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] :
    haveI := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j
      j.isClosedEmbedding.isClosed_range
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit ≫
      Functor.whiskerRight ((Functor.mapDerivedCategoryNatIso
        (asIso (openImmersionLowerShriekToLowerStar A j))).hom ≫
          ((j)_*[A]).rightDerivedFunctorIsoMapDerivedCategory.inv) D((j)^*[A]) ≫
      (mapDerivedUpperStarLowerStarAdjunction A j).counit = 𝟙 _ := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j
    j.isClosedEmbedding.isClosed_range
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))
  intro Y
  have ha := Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj
    (openImmersionLowerShriekUpperStarAdjunction A j) Y
  have hb := Functor.mapDerivedCategoryNatIso_fach
    (asIso (openImmersionLowerShriekToLowerStar A j)) Y
  have hc : ((j)_*[A]).rightDerivedFunctorIsoMapDerivedCategory.inv.app
      (DerivedCategory.Qh.obj Y) =
        ((j)_*[A]).mapDerivedCategoryFactorsh.hom.app Y ≫
          ((j)_*[A]).rightDerivedFunctorUnit.app Y := by
    rw [← cancel_mono (((j)_*[A]).rightDerivedFunctorIsoMapDerivedCategory.hom.app _),
      Iso.inv_hom_id_app, Category.assoc]
    have h₃ := NatTrans.congr_app ((j)_*[A]).rightDerivedFunctorIsoMapDerivedCategory_hom_fac Y
    dsimp at h₃
    rw [h₃, Iso.hom_inv_id_app]
    rfl
  have hd : D((j)^*[A]).map (((j)_*[A]).rightDerivedFunctorUnit.app Y) ≫
      (mapDerivedUpperStarLowerStarAdjunction A j).counit.app (DerivedCategory.Qh.obj Y) = _ :=
    ((upperStarLowerStarAdjunction A j).mapHomotopyCategory (.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) ((j)^*[A]).mapDerivedCategoryFactorsh.hom
      ((j)_*[A]).rightDerivedFunctorUnit Y
  have he := ((j)^*[A]).mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory (openImmersionLowerShriekToLowerStar A j) (.up ℤ)).app Y)
  dsimp at ha hb hd he ⊢
  rw [hc, reassoc_of% hb, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hd,
    reassoc_of% he]
  erw [reassoc_of% ha]
  clear ha hb hc hd he
  rw [← Functor.map_comp, ← Functor.map_comp, ← CategoryTheory.Functor.map_id]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  erw [Functor.mapHomotopyCategory_map]
  rw [← Functor.map_comp, ← Functor.map_comp, ← CategoryTheory.Functor.map_id]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, HomologicalComplex.id_f]
  exact unit_map_openImmersionLowerShriekToLowerStar_app_counit A j (K.X n)

/-- For an immersion `j` that is both open and closed, the derived comparison
`D(j_!) ⟶ Rj_*` is the levelwise comparison `D(j_! ⟶ j_*)` followed by the identification
`D(j_*) ≅ Rj_*` of the exact functor `j_*`. -/
lemma derivedOpenImmersionLowerShriekToLowerStar_eq_of_isClosedImmersion {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] :
    haveI := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j
      j.isClosedEmbedding.isClosed_range
    derivedOpenImmersionLowerShriekToLowerStar A j =
      (Functor.mapDerivedCategoryNatIso
        (asIso (openImmersionLowerShriekToLowerStar A j))).hom ≫
          ((j)_*[A]).rightDerivedFunctorIsoMapDerivedCategory.inv := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j
    j.isClosedEmbedding.isClosed_range
  ext K
  apply ((mapDerivedUpperStarLowerStarAdjunction A j).homEquiv _ _).symm.injective
  rw [derivedOpenImmersionLowerShriekToLowerStar_app]
  erw [Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit]
  symm
  apply IsIso.eq_inv_of_hom_inv_id
  simpa using NatTrans.congr_app
    (unit_map_mapDerivedCategory_openImmersionLowerShriekToLowerStar_counit A j) K

end Clopen

end AlgebraicGeometry.Etale

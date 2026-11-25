/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidalUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift
import all Mathlib.Algebra.Homology.Localization

import all Mathlib.Algebra.Homology.Localization

/-!
# Left unitality of the tensor comparison of the derived pullback

For `g : Z ⟶ Y`, the tensor comparison `μ : Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`) and the unit comparison
`ε : Lg^* Λ_Y ≅ Λ_Z` (`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`) satisfy the left
unitality axiom of monoidal functors
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_leftUnitor_hom`). It is deduced
from the left unitality of the comparison of `g^*` on the homotopy category
(`CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_leftUnitor`).
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

open _root_.DerivedCategory

/-- The unit comparison `Lg^* Λ_Y ≅ Λ_Z` is induced by the counit `η` of `g^*`. -/
lemma leftDerivedUpperStarUnitIso_hom_comp_ε :
    (leftDerivedUpperStarUnitIso A g).hom ≫
        Functor.LaxMonoidal.ε (Qh (C := Sheaf Z.smallEtaleTopology A)) =
    L((g)^*[A]).map (Functor.LaxMonoidal.ε (Qh (C := Sheaf Y.smallEtaleTopology A))) ≫
      (g)^*[A].leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (Functor.OplaxMonoidal.mapHomotopyCategoryη (.up ℤ) (g)^*[A]) := by
  have h₁ : Functor.LaxMonoidal.ε (Qh (C := Sheaf Z.smallEtaleTopology A)) = 𝟙 _ := rfl
  have h₂ : Functor.LaxMonoidal.ε (Qh (C := Sheaf Y.smallEtaleTopology A)) = 𝟙 _ := rfl
  rw [← (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  dsimp [leftDerivedUpperStarUnitIso]
  simp only [h₁, h₂, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc]
  change _ ≫ _ = (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫ _
  congr 1
  erw [(g)^*[A].mapDerivedCategoryFactorsh_hom_app (𝟙_ _)]
  simp only [Functor.OplaxMonoidal.mapHomotopyCategoryη,
    Functor.OplaxMonoidal.mapHomologicalComplexη, Functor.map_comp,
    Q_obj_single_obj, Functor.comp_obj, Category.assoc]
  have h₃ : ∀ K, (quotientCompQhIso (Sheaf Y.smallEtaleTopology A)).hom.app K = 𝟙 _ :=
    fun _ ↦ rfl
  have h₄ : ∀ K, (quotientCompQhIso (Sheaf Z.smallEtaleTopology A)).inv.app K = 𝟙 _ :=
    fun _ ↦ rfl
  have h₅ : ∀ K, ((g)^*[A].mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K = 𝟙 _ :=
    fun _ ↦ rfl
  erw [h₃, h₄, h₅, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp]
  have h₆ : ∀ {K L : CochainComplex (Sheaf Z.smallEtaleTopology A) ℤ} (f : K ⟶ L),
      Qh.map ((HomotopyCategory.quotient _ _).map f) = Q.map f := fun f ↦ by
    have h := quotientCompQhIso_hom_naturality f
    have h₃' : ∀ K, (quotientCompQhIso (Sheaf Z.smallEtaleTopology A)).hom.app K = 𝟙 _ :=
      fun _ ↦ rfl
    rw [h₃', h₃'] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  erw [Category.id_comp, h₆, h₆]
  rw [h₆]
  erw [Category.comp_id, Category.id_comp]
  rfl

variable [(g)^*[A].PreservesFlat]

/-- Left unitality of the tensor comparison of `Lg^*` on objects of the homotopy category. -/
lemma leftDerivedUpperStarTensorComparison_leftUnitor_hom_Qh
    (M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (𝟙_ _)).app (Qh.obj M) ≫
        (leftDerivedUpperStarUnitIso A g).hom ▷ L((g)^*[A]).obj (Qh.obj M) ≫
          (λ_ (L((g)^*[A]).obj (Qh.obj M))).hom =
      L((g)^*[A]).map (λ_ (Qh.obj M)).hom := by
  have hεZ : Functor.LaxMonoidal.ε (Qh (C := Sheaf Z.smallEtaleTopology A)) = 𝟙 _ := rfl
  have hεY : Functor.LaxMonoidal.ε (Qh (C := Sheaf Y.smallEtaleTopology A)) = 𝟙 _ := rfl
  have hε := leftDerivedUpperStarUnitIso_hom_comp_ε A g
  rw [hεZ, hεY, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hε
  have hlY : ∀ M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ),
      (λ_ (Qh.obj M)).hom = Functor.LaxMonoidal.μ Qh (𝟙_ _) M ≫ Qh.map (λ_ M).hom := fun M ↦ by
    rw [Functor.LaxMonoidal.left_unitality, hεY, id_whiskerRight, Category.id_comp]
  have hlZ : ∀ M : HomotopyCategory (Sheaf Z.smallEtaleTopology A) (.up ℤ),
      (λ_ (Qh.obj M)).hom = Functor.LaxMonoidal.μ Qh (𝟙_ _) M ≫ Qh.map (λ_ M).hom := fun M ↦ by
    rw [Functor.LaxMonoidal.left_unitality, hεZ, id_whiskerRight, Category.id_comp]
  have hδ := Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_leftUnitor (.up ℤ) (g)^*[A] M
  have hδ' : ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]).app
        (𝟙_ _)).app M ≫
      Functor.OplaxMonoidal.mapHomotopyCategoryη (.up ℤ) (g)^*[A] ▷
        ((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M ≫
      (λ_ (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj M)).hom =
        ((g)^*[A].mapHomotopyCategory (.up ℤ)).map (λ_ M).hom := by
    rw [← cancel_epi (((g)^*[A].mapHomotopyCategory (.up ℤ)).map (λ_ M).inv),
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, reassoc_of% hδ,
      Iso.inv_hom_id]
  have fac := leftDerivedUpperStarTensorComparison_app_app_fac A g (𝟙_ _) M
  simp only [Functor.postcompose₂_obj_obj_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    curriedTensor_obj_obj, derivedTensorLeftDerivedUpperStarCounit, NatTrans.comp_app,
    Functor.comp_obj, Functor.whiskeringLeft₂_map_app_app_app_app,
    Functor.whiskeringLeft₂_obj_map_app_app_app, Functor.whiskeringLeft₂_obj_obj_map_app_app,
    Functor.LaxMonoidal.μNatTrans_app_app, leftDerivedUpperStarDerivedTensorCounit,
    Functor.postcompose₂_obj_map_app_app, Functor.postcompose₂_map_app_app_app,
    Functor.postcompose₂MapWhiskeringLeft₂_app_app, Category.assoc] at fac
  rw [← cancel_mono ((g)^*[A].leftDerivedFunctorCounit.app M)]
  have hnat := (g)^*[A].leftDerivedFunctorCounit.naturality (λ_ M).hom
  dsimp at hnat
  rw [hlY, Functor.map_comp]
  simp only [Category.assoc]
  rw [hnat, ← hδ', Functor.map_comp, Functor.map_comp, ← reassoc_of% fac]
  erw [← Functor.LaxMonoidal.μ_natural_left_assoc, ← hlZ]
  rw [hε, comp_whiskerRight, Category.assoc]
  erw [← leftUnitor_naturality]
  erw [whisker_exchange_assoc]
  rfl

/-- **Left unitality of the tensor comparison of `Lg^*`**: for `K` in `D(Y_ét)`,
`μ_{Λ, K} ≫ (ε ▷ Lg^* K) ≫ λ = Lg^*(λ)`, for the tensor comparison
`μ : Lg^*(Λ_Y ⊗ᴸ K) ⟶ Lg^* Λ_Y ⊗ᴸ Lg^* K` and the unit comparison `ε : Lg^* Λ_Y ≅ Λ_Z`. -/
lemma leftDerivedUpperStarTensorComparison_leftUnitor_hom
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparison A g).app (𝟙_ _)).app K ≫
        (leftDerivedUpperStarUnitIso A g).hom ▷ L((g)^*[A]).obj K ≫
          (λ_ (L((g)^*[A]).obj K)).hom =
      L((g)^*[A]).map (λ_ K).hom := by
  obtain ⟨M, ⟨e⟩⟩ : ∃ M, Nonempty (Qh.obj M ≅ K) := ⟨_, ⟨Qh.objObjPreimageIso K⟩⟩
  rw [← cancel_epi (L((g)^*[A]).map (𝟙_ _ ◁ e.hom))]
  have h := ((leftDerivedUpperStarTensorComparison A g).app (𝟙_ _)).naturality e.hom
  dsimp at h
  calc _ = (((leftDerivedUpperStarTensorComparison A g).app (𝟙_ _)).app (Qh.obj M) ≫
        (leftDerivedUpperStarUnitIso A g).hom ▷ L((g)^*[A]).obj (Qh.obj M) ≫
          (λ_ (L((g)^*[A]).obj (Qh.obj M))).hom) ≫ L((g)^*[A]).map e.hom := by
        erw [reassoc_of% h]
        simp only [Category.assoc]
        erw [whisker_exchange_assoc, leftUnitor_naturality]
    _ = _ := by
        rw [leftDerivedUpperStarTensorComparison_leftUnitor_hom_Qh, ← Functor.map_comp,
          ← Functor.map_comp, leftUnitor_naturality]

/-- **Left unitality of the tensor comparison of `Lg^*`**, inverse form:
`Lg^*(λ⁻¹) ≫ μ_{Λ, K} ≫ (ε ▷ Lg^* K) = λ⁻¹`. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_leftUnitor_inv
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (λ_ K).inv ≫ ((leftDerivedUpperStarTensorComparison A g).app (𝟙_ _)).app K ≫
        (leftDerivedUpperStarUnitIso A g).hom ▷ L((g)^*[A]).obj K =
      (λ_ (L((g)^*[A]).obj K)).inv := by
  rw [← cancel_mono (λ_ (L((g)^*[A]).obj K)).hom, Iso.inv_hom_id, Category.assoc,
    Category.assoc, leftDerivedUpperStarTensorComparison_leftUnitor_hom, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

end Etale

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DoubleDual

/-!
# The derived pullback is braided

Let `g : Z ⟶ Y` be a morphism of schemes. This file proves that the derived pullback
`Lg^* : D(Y_ét) ⥤ D(Z_ét)`, with its monoidal structure
`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`, is braided for the derived braidings
`AlgebraicGeometry.Etale.derivedBraidedCategory` (the Koszul braiding of complexes descended
along K-flat resolutions). This is the hypothesis `hbr` of the double-dual statements in
`WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.DoubleDual`, used for blueprint
`lemma-double-dual-geometric-generic-fibre--1` and `definition-verdier-dual-evaluation--4`.

## Main statements

- `CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_braiding`: an additive
  oplax monoidal functor `G` compatible with the braidings induces, on cochain complexes, a
  comparison compatible with the Koszul braidings.
- `CategoryTheory.Functor.mapHomotopyCategory_map_braiding_hom_δ`: the same on homotopy
  categories.
- `AlgebraicGeometry.Etale.upperStar_map_braiding_hom_δ`: the pullback `g^*` of étale sheaves
  is compatible with the braidings (by doctrinal adjunction, `g_*` being lax braided).
- `AlgebraicGeometry.Etale.leftDerivedUpperStar_μ_map_braiding_hom`: the braided axiom for
  `Lg^*`, and `AlgebraicGeometry.Etale.leftDerivedUpperStarLaxBraidedOfPreservesFlat`: the
  corresponding lax braided structure.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarBraided`: the proposition
  `AlgebraicGeometry.Etale.LeftDerivedUpperStarBraided A g` holds.

## Implementation notes

Both sides of the braided axiom are compared on objects `Qh P`, `Qh Q` where the pullback of
`P` is K-flat (`AlgebraicGeometry.Etale.kFlatUpperStar`). There the comparison of `Lg^*` is
computed by `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_app_app_comp`, the
derived braiding by `CategoryTheory.DerivedMonoidal.braiding_hom_μ`, and the composite with
`μ Qh` at the K-flat complex `g^* P` is an isomorphism, so that the axiom reduces to the
compatibility of `g^*` with the Koszul braidings on homotopy categories. The general case
follows since every object of `D(Y_ét)` is isomorphic to such a `Qh P`.

The derived braiding identity `DerivedMonoidal.braiding_hom_μ` is first instantiated for a
general category (`DerivedCategory.braidedCategory_braiding_hom_μ_Qh`), and only then at étale
sheaves: instantiating it directly at étale sheaves makes the elaborator compare two
elaborations of the monoidal structure (see the implementation notes of
`WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D)

open OplaxMonoidal in
/-- The compatibility of the comonoidal structure `δ` of an oplax monoidal functor with the
braidings, `F β_{X, Y} ≫ δ_{Y, X} = δ_{X, Y} ≫ β_{F X, F Y}`, is invariant under replacing `X`
and `Y` by isomorphic objects. -/
lemma OplaxMonoidal.map_braiding_hom_δ_of_iso [F.OplaxMonoidal] {X X' Y Y' : C} (eX : X' ≅ X)
    (eY : Y' ≅ Y)
    (h : F.map (β_ X' Y').hom ≫ δ F Y' X' = δ F X' Y' ≫ (β_ (F.obj X') (F.obj Y')).hom) :
    F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom := by
  rw [← cancel_epi (F.map (eX.hom ⊗ₘ eY.hom)), ← F.map_comp_assoc,
    BraidedCategory.braiding_naturality, F.map_comp_assoc, ← δ_natural, reassoc_of% h,
    ← δ_natural_assoc, BraidedCategory.braiding_naturality]

open LaxMonoidal OplaxMonoidal in
/-- For a monoidal functor, the compatibility of `δ` with the braidings implies the braided
axiom `μ_{X, Y} ≫ F β_{X, Y} = β_{F X, F Y} ≫ μ_{Y, X}` for `μ`. -/
lemma Monoidal.μ_map_braiding_hom_of_δ [F.Monoidal] (X Y : C)
    (h : F.map (β_ X Y).hom ≫ δ F Y X = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) :
    μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
  rw [← cancel_mono (δ F Y X), assoc, h, Monoidal.μ_δ_assoc, assoc, Monoidal.μ_δ, comp_id]

end CategoryTheory.Functor

namespace CategoryTheory.Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

/-- If the comonoidal structure of an additive oplax monoidal functor `G` is compatible with the
braidings, then so is the comonoidal structure of `G` on cochain complexes, for the Koszul
braidings: on the summand `K.X p ⊗ L.X q` both sides are `(-1)^(pq)` times the corresponding
maps for `G`. -/
lemma mapHomologicalComplexδNatTrans_braiding
    (hG : ∀ X Y : C, G.map (β_ X Y).hom ≫ δ G Y X = δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom)
    (K L : CochainComplex C ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom ≫
        ((mapHomologicalComplexδNatTrans (.up ℤ) G).app L).app K =
      ((mapHomologicalComplexδNatTrans (.up ℤ) G).app K).app L ≫
        (β_ ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L)).hom := by
  ext n
  refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
  simp only [mapHomologicalComplexδNatTrans_app_app, comp_f, mapBifunctorComparison_f,
    Functor.mapHomologicalComplex_map_f]
  have h₁ := CochainComplex.Monoidal.ι_braiding_hom (K := K) (L := L) p q n h
  have h₂ := CochainComplex.Monoidal.ι_braiding_hom (K := (G.mapHomologicalComplex (.up ℤ)).obj K)
    (L := (G.mapHomologicalComplex (.up ℤ)).obj L) p q n h
  erw [← G.map_comp_assoc, h₁, map_ιMapBifunctor_mapBifunctorComparisonX_assoc, h₂]
  rw [G.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, G.map_comp, assoc]
  erw [map_ιMapBifunctor_mapBifunctorComparisonX]
  simp only [mapBifunctorComparisonApp, δNatTrans_app_app]
  rw [reassoc_of% hG]
  rfl

end CategoryTheory.Functor.OplaxMonoidal

namespace CategoryTheory.Functor

open OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.Monoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

/-- If the comonoidal structure of an additive monoidal functor `G` is compatible with the
braidings, then so is the comonoidal structure of `G.mapHomotopyCategory`, for the Koszul
braidings of the homotopy categories. -/
lemma mapHomotopyCategory_map_braiding_hom_δ
    (hG : ∀ X Y : C, G.map (β_ X Y).hom ≫ δ G Y X = δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom)
    (K L : HomotopyCategory C (.up ℤ)) :
    (G.mapHomotopyCategory (.up ℤ)).map (β_ K L).hom ≫ δ (G.mapHomotopyCategory (.up ℤ)) L K =
      δ (G.mapHomotopyCategory (.up ℤ)) K L ≫
        (β_ ((G.mapHomotopyCategory (.up ℤ)).obj K)
          ((G.mapHomotopyCategory (.up ℤ)).obj L)).hom := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  have h := (HomotopyCategory.quotient D (.up ℤ)).congr_map
    (mapHomologicalComplexδNatTrans_braiding G hG K L)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

end CategoryTheory.Functor

namespace DerivedCategory

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- (Implementation) The colimits needed for the derived monoidal structure. -/
local instance hasColimitsOfSize_braided : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

open Functor.LaxMonoidal in
/-- The braiding `DerivedCategory.braidedCategory'` on objects `Qh K`, `Qh M`:
`β_{Qh K, Qh M} ≫ μ_{M, K} = μ_{K, M} ≫ Qh β_{K, M}`, where `β_{K, M}` is the Koszul braiding of
the homotopy category. -/
lemma braidedCategory_braiding_hom_μ_Qh (K M : HomotopyCategory C (.up ℤ)) :
    letI := braidedCategory' C
    (β_ (Qh.obj K) (Qh.obj M)).hom ≫ μ Qh M K = μ Qh K M ≫ Qh.map (β_ K M).hom :=
  DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso C (.up ℤ)) K M

end DerivedCategory

universe u' u

namespace AlgebraicGeometry

open Scheme Functor.LaxMonoidal Functor.OplaxMonoidal

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

omit [MonoidalPreadditive A] in
/-- The pullback `g^*` of étale sheaves is compatible with the braidings:
`g^* β_{F, G} ≫ δ_{G, F} = δ_{F, G} ≫ β_{g^* F, g^* G}`. Its comonoidal structure is obtained
by doctrinal adjunction from the lax monoidal structure of `g_*`
(`AlgebraicGeometry.Etale.upperStar_δ`), and `g_*` is lax braided. -/
lemma upperStar_map_braiding_hom_δ (F G : Sheaf Y.smallEtaleTopology A) :
    (g)^*[A].map (β_ F G).hom ≫ δ (g)^*[A] G F = δ (g)^*[A] F G ≫ (β_ _ _).hom := by
  have hb := Functor.LaxBraided.braided (F := (g)_*[A]) ((g)^*[A].obj F) ((g)^*[A].obj G)
  rw [upperStar_δ, upperStar_δ, ← Functor.map_comp_assoc,
    ← BraidedCategory.braiding_naturality_assoc]
  erw [← hb]
  rw [Functor.map_comp, Functor.map_comp, assoc, assoc, Adjunction.counit_naturality,
    Functor.map_comp, assoc, assoc]

variable [Abelian.HasFunctorialFlatResolution A]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

open _root_.DerivedCategory

/-- The derived braiding of `D(X_ét)` on objects `Qh K`, `Qh M`: the square
`β_{Qh K, Qh M} ≫ μ_{M, K} = μ_{K, M} ≫ Qh β_{K, M}` commutes. -/
lemma derivedBraiding_hom_μ_Qh (X : Scheme.{u})
    (K M : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ)) :
    (β_ (Qh.obj K) (Qh.obj M)).hom ≫ μ Qh M K = μ Qh K M ≫ Qh.map (β_ K M).hom :=
  braidedCategory_braiding_hom_μ_Qh _ K M

section PreservesFlat

variable [(g)^*[A].PreservesFlat]

/-- The comonoidal structure of the monoidal functor `Lg^*` is
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`. -/
lemma leftDerivedUpperStar_δ_eq (K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A g
    δ L((g)^*[A]) K M = ((leftDerivedUpperStarTensorComparison A g).app K).app M :=
  rfl

/-- The comonoidal structure of `Lg^*` is compatible with the derived braidings at `Qh P` and
`Qh Q`, when the pullback of `P` is K-flat. -/
lemma leftDerivedUpperStar_map_braiding_hom_δ_Qh
    (P Q : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ))
    (hP : kFlatUpperStar A g P) :
    letI := leftDerivedUpperStarMonoidal A g
    L((g)^*[A]).map (β_ (Qh.obj P) (Qh.obj Q)).hom ≫ δ L((g)^*[A]) (Qh.obj Q) (Qh.obj P) =
      δ L((g)^*[A]) (Qh.obj P) (Qh.obj Q) ≫
        (β_ (L((g)^*[A]).obj (Qh.obj P)) (L((g)^*[A]).obj (Qh.obj Q))).hom := by
  let := leftDerivedUpperStarMonoidal A g
  have : IsIso (μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj Q)
      (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P)) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hP
  rw [← cancel_mono (((g)^*[A].leftDerivedFunctorCounit.app Q ⊗ₘ
    (g)^*[A].leftDerivedFunctorCounit.app P) ≫
    μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj Q)
      (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P))]
  simp only [leftDerivedUpperStar_δ_eq, assoc]
  rw [leftDerivedUpperStarTensorComparison_app_app_comp,
    ← BraidedCategory.braiding_naturality_assoc]
  have hβ : (β_ (((g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ Qh).obj P)
      (((g)^*[A].mapHomotopyCategory (.up ℤ) ⋙ Qh).obj Q)).hom ≫
        μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj Q)
          (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P) =
      μ Qh (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P)
          (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj Q) ≫
        Qh.map (β_ (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj P)
          (((g)^*[A].mapHomotopyCategory (.up ℤ)).obj Q)).hom :=
    derivedBraiding_hom_μ_Qh A Z _ _
  rw [hβ]
  rw [reassoc_of% (leftDerivedUpperStarTensorComparison_app_app_comp A g P Q)]
  rw [← Functor.map_comp_assoc]
  rw [derivedBraiding_hom_μ_Qh A Y P Q]
  rw [Functor.map_comp_assoc]
  have hn : L((g)^*[A]).map (Qh.map (β_ P Q).hom) ≫
      (g)^*[A].leftDerivedFunctorCounit.app (Q ⊗ P) =
      (g)^*[A].leftDerivedFunctorCounit.app (P ⊗ Q) ≫
        Qh.map (((g)^*[A].mapHomotopyCategory (.up ℤ)).map (β_ P Q).hom) :=
    (g)^*[A].leftDerivedFunctorCounit.naturality _
  erw [reassoc_of% hn]
  rw [← Qh.map_comp, ← Qh.map_comp,
    Functor.mapHomotopyCategory_map_braiding_hom_δ _ (upperStar_map_braiding_hom_δ A g) P Q]


/-- The comonoidal structure of `Lg^*` is compatible with the derived braidings:
`Lg^* β_{K, M} ≫ δ_{M, K} = δ_{K, M} ≫ β_{Lg^* K, Lg^* M}`. -/
theorem leftDerivedUpperStar_map_braiding_hom_δ
    (K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A g
    L((g)^*[A]).map (β_ K M).hom ≫ δ L((g)^*[A]) M K =
      δ L((g)^*[A]) K M ≫ (β_ (L((g)^*[A]).obj K) (L((g)^*[A]).obj M)).hom := by
  let := leftDerivedUpperStarMonoidal A g
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_kFlatUpperStar_iso A g K
  obtain ⟨Q, -, ⟨eQ⟩⟩ := exists_kFlatUpperStar_iso A g M
  exact Functor.OplaxMonoidal.map_braiding_hom_δ_of_iso _ eP eQ
    (leftDerivedUpperStar_map_braiding_hom_δ_Qh A g P Q hP)

/-- **The derived pullback is braided.** For the monoidal structure
`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal` of `Lg^*` and the derived braidings
`AlgebraicGeometry.Etale.derivedBraidedCategory`,
`μ_{K, M} ≫ Lg^* β_{K, M} = β_{Lg^* K, Lg^* M} ≫ μ_{M, K}`. This is used for blueprint
`lemma-double-dual-geometric-generic-fibre--1` and `definition-verdier-dual-evaluation--4`. -/
theorem leftDerivedUpperStar_μ_map_braiding_hom
    (K M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A g
    μ L((g)^*[A]) K M ≫ L((g)^*[A]).map (β_ K M).hom =
      (β_ (L((g)^*[A]).obj K) (L((g)^*[A]).obj M)).hom ≫ μ L((g)^*[A]) M K := by
  let := leftDerivedUpperStarMonoidal A g
  exact Functor.Monoidal.μ_map_braiding_hom_of_δ _ K M
    (leftDerivedUpperStar_map_braiding_hom_δ A g K M)

/-- The lax braided structure on the derived pullback `Lg^*`, whose lax monoidal structure is
that of `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_μ_map_braiding_hom`). -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarLaxBraidedOfPreservesFlat : (L((g)^*[A])).LaxBraided :=
  letI := leftDerivedUpperStarMonoidal A g
  { braided := leftDerivedUpperStar_μ_map_braiding_hom A g }

end PreservesFlat

/-- Blueprint `lemma-double-dual-geometric-generic-fibre--1` and
`definition-verdier-dual-evaluation--4` (input): the braided axiom
`AlgebraicGeometry.Etale.LeftDerivedUpperStarBraided` holds for every morphism `g`, i.e. `Lg^*` is
braided for its monoidal structure `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`. -/
theorem leftDerivedUpperStarBraided [UpperStarPreservesFlat A] :
    LeftDerivedUpperStarBraided A g :=
  leftDerivedUpperStar_μ_map_braiding_hom A g

end Etale

end AlgebraicGeometry

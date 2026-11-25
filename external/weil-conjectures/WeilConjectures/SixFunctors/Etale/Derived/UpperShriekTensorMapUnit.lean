/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The tensor maps of the exceptional inverse image at the unit

For a right adjoint `G` of `Rf_!` (for finite coefficients, `G = Rf^!`), the tensor map
`G M ⊗ᴸ Lf^* N ⟶ G(M ⊗ᴸ N)` (`AlgebraicGeometry.Etale.lowerShriekRightAdjointTensorMap`) at
`N = Λ_Y` is the right unitor, read through `Lf^* Λ_Y ≅ Λ_X`: this is the right unitality of the
projection map (`AlgebraicGeometry.Etale.projectionMap_rightUnitality`). In particular the
canonical map `ω_f ⊗ᴸ Lf^* Λ_Y ⟶ Rf^! Λ_Y = ω_f`
(`AlgebraicGeometry.Etale.lowerShriekRightAdjointUnitTensorMap`) is the right unitor.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y} [HasCompactification f]
  [IsIso (projectionMap A f)]
  {G : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (adj : R(f)_![A] ⊣ G)

/-- The tensor map `G M ⊗ᴸ Lf^* Λ_Y ⟶ G(M ⊗ᴸ Λ_Y)` is the right unitor, read through
`Lf^* Λ_Y ≅ Λ_X`. -/
lemma lowerShriekRightAdjointTensorMap_unit_right
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    lowerShriekRightAdjointTensorMap adj M (𝟙_ _) =
      G.obj M ◁ (leftDerivedUpperStarUnitIso A f).hom ≫ (ρ_ _).hom ≫ G.map (ρ_ M).inv := by
  apply Adjunction.ext_of_comp_counit (adj := adj)
  rw [Adjunction.map_projectionTensorMap_comp_counit]
  have hU := projectionMap_rightUnitality A f (G.obj M)
  have hU' : (R(f)_![A]).map (G.obj M ◁ (leftDerivedUpperStarUnitIso A f).hom ≫
      (ρ_ (G.obj M)).hom) = inv (((projectionMap A f).app (G.obj M)).app (𝟙_ _)) ≫
        (ρ_ ((R(f)_![A]).obj (G.obj M))).hom := by
    rw [IsIso.eq_inv_comp, hU]
  rw [Functor.map_comp, Functor.map_comp, ← Functor.map_comp_assoc, hU', Category.assoc,
    Category.assoc]
  erw [adj.counit_naturality]
  rw [← rightUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The canonical map `G Λ_Y ⊗ᴸ Lf^* Λ_Y ⟶ G Λ_Y`
(`AlgebraicGeometry.Etale.lowerShriekRightAdjointUnitTensorMap`) is the right unitor, read
through `Lf^* Λ_Y ≅ Λ_X`. -/
lemma lowerShriekRightAdjointUnitTensorMap_unit :
    lowerShriekRightAdjointUnitTensorMap adj (𝟙_ _) =
      G.obj (𝟙_ _) ◁ (leftDerivedUpperStarUnitIso A f).hom ≫ (ρ_ _).hom := by
  rw [lowerShriekRightAdjointUnitTensorMap, lowerShriekRightAdjointTensorMap_unit_right,
    Category.assoc, Category.assoc, ← G.map_comp, unitors_equal, Iso.inv_hom_id,
    G.map_id, Category.comp_id]

/-- The canonical map `G Λ_Y ⊗ᴸ Lf^* K ⟶ G K`
(`AlgebraicGeometry.Etale.lowerShriekRightAdjointUnitTensorMap`) is natural in `K`. -/
@[reassoc]
lemma lowerShriekRightAdjointUnitTensorMap_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (φ : K ⟶ K') :
    lowerShriekRightAdjointUnitTensorMap adj K ≫ G.map φ =
      G.obj (𝟙_ _) ◁ (L((f)^*[A])).map φ ≫ lowerShriekRightAdjointUnitTensorMap adj K' := by
  have hπ : ∀ (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
      {N N' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (ψ : N ⟶ N'),
      (R(f)_![A]).obj M ◁ ψ ≫ ((projectionMap A f).app M).app N' =
        ((projectionMap A f).app M).app N ≫ (R(f)_![A]).map (M ◁ (L((f)^*[A])).map ψ) :=
    fun M _ _ ψ ↦ projectionMap_naturality_right A f M ψ
  rw [lowerShriekRightAdjointUnitTensorMap, lowerShriekRightAdjointUnitTensorMap,
    lowerShriekRightAdjointTensorMap, lowerShriekRightAdjointTensorMap, Category.assoc,
    ← G.map_comp, ← leftUnitor_naturality, G.map_comp,
    Adjunction.projectionTensorMap_naturality_right_assoc adj _ hπ]

end AlgebraicGeometry.Etale

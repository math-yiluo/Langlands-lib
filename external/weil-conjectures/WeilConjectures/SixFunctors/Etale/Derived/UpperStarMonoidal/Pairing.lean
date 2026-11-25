/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Pairings of classes and the derived pullback

For `h : Y ⟶ Y`, objects `A₁, B, C` of `D(Y_ét)` with maps `ψ : Lh^*(-) ⟶ (-)` and a pairing
`Q : A₁ ⊗ᴸ B ⟶ C` compatible with them, the product
`Hom(Λ_Y, A₁[i]) × Hom(Λ_Y, B[j]) ⟶ Hom(Λ_Y, C[i + j])` induced by `Q` intertwines the
operators `x ↦ ψ[n] ∘ Lh^* x ∘ ε⁻¹`
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_pairing_comm`). This is the Frobenius
equivariance of the degreewise pairing of a Weil pairing.
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

variable {Y : Scheme.{u}} (h : Y ⟶ Y) [(h)^*[A].PreservesFlat]

/-- The product of classes `x : Λ_Y ⟶ A₁[i]` and `y : Λ_Y ⟶ B[j]` along a pairing
`Q : A₁ ⊗ᴸ B ⟶ C` intertwines the operators `x ↦ ψ[n] ∘ Lh^* x ∘ ε⁻¹`, provided `Q`
intertwines `ψ_{A₁} ⊗ ψ_B` (read through the tensor comparison of `Lh^*`) and `ψ_C`. -/
lemma leftDerivedUpperStar_pairing_comm
    {A₁ B C : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (ψA : L((h)^*[A]).obj A₁ ⟶ A₁) (ψB : L((h)^*[A]).obj B ⟶ B) (ψC : L((h)^*[A]).obj C ⟶ C)
    (Q : ((-⊗ᴸ-(Y)[A]).obj A₁).obj B ⟶ C)
    (hQ : L((h)^*[A]).map Q ≫ ψC = ((leftDerivedUpperStarTensorIso A h A₁ B).hom ≫
      ((-⊗ᴸ-(Y)[A]).map ψA).app _ ≫ ((-⊗ᴸ-(Y)[A]).obj A₁).map ψB) ≫ Q) (i j : ℤ)
    (x : 𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A)) ⟶ A₁⟦i⟧)
    (y : 𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A)) ⟶ B⟦j⟧) :
    (derivedTensorLeftUnitor A Y (𝟙_ _)).inv ≫
        ((-⊗ᴸ-(Y)[A]).flip.obj (𝟙_ _)).map ((leftDerivedUpperStarUnitIso A h).inv ≫
          L((h)^*[A]).map x ≫ (L((h)^*[A]).commShiftIso i).hom.app A₁ ≫ ψA⟦i⟧') ≫
        ((-⊗ᴸ-(Y)[A]).obj (A₁⟦i⟧)).map ((leftDerivedUpperStarUnitIso A h).inv ≫
          L((h)^*[A]).map y ≫ (L((h)^*[A]).commShiftIso j).hom.app B ≫ ψB⟦j⟧') ≫
        (derivedTensorShiftIso A A₁ B i j).hom ≫ Q⟦i + j⟧' =
      (leftDerivedUpperStarUnitIso A h).inv ≫ L((h)^*[A]).map
        ((derivedTensorLeftUnitor A Y (𝟙_ _)).inv ≫
          ((-⊗ᴸ-(Y)[A]).flip.obj (𝟙_ _)).map x ≫ ((-⊗ᴸ-(Y)[A]).obj (A₁⟦i⟧)).map y ≫
          (derivedTensorShiftIso A A₁ B i j).hom ≫ Q⟦i + j⟧') ≫
        (L((h)^*[A]).commShiftIso (i + j)).hom.app C ≫ ψC⟦i + j⟧' := by
  simp only [leftDerivedUpperStarTensorIso_hom, Category.assoc] at hQ
  have hε := leftDerivedUpperStarTensorComparison_leftUnitor_inv A h
    (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A)))
  have hε' : L((h)^*[A]).map (λ_ (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A)))).inv ≫
      ((leftDerivedUpperStarTensorComparison A h).app (𝟙_ _)).app (𝟙_ _) =
      (λ_ _).inv ≫ (leftDerivedUpperStarUnitIso A h).inv ▷ _ := by
    rw [← reassoc_of% hε, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight]
    erw [Category.comp_id]
  have hx := congr_app ((leftDerivedUpperStarTensorComparison A h).naturality x)
    (𝟙_ (DerivedCategory (Sheaf Y.smallEtaleTopology A)))
  have hy := ((leftDerivedUpperStarTensorComparison A h).app (A₁⟦i⟧)).naturality y
  dsimp at hx hy
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc L((h)^*[A]) Q (i + j),
    ← Functor.map_comp, hQ, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    leftDerivedUpperStarTensorComparison_derivedTensorShiftIso_assoc,
    ← derivedTensorShiftIso_hom_naturality_left_assoc,
    ← derivedTensorShiftIso_hom_naturality_right_assoc, reassoc_of% hy]
  simp only [Functor.flip_obj_map] at hx ⊢
  rw [reassoc_of% hx]
  simp only [derivedTensorLeftUnitor]
  rw [reassoc_of% hε', leftUnitor_inv_naturality_assoc]
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map]
  simp only [whisker_exchange_assoc]

end Etale

end AlgebraicGeometry

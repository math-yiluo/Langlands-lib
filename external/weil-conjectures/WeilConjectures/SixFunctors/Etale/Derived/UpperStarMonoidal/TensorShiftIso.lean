/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift

/-!
# The tensor comparison of the derived pullback and the shifts of both factors

* `AlgebraicGeometry.Etale.derivedTensorShiftIso_hom_naturality_left`,
  `AlgebraicGeometry.Etale.derivedTensorShiftIso_hom_naturality_right`: the isomorphism
  `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧` is natural in `K` and `M`.
* `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_derivedTensorShiftIso`: the
  tensor comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` is compatible with these isomorphisms and
  the shift compatibility of `Lg^*`.
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

section

variable {X : Scheme.{u}}

/-- The isomorphism `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧` is natural in `K`. -/
@[reassoc]
lemma derivedTensorShiftIso_hom_naturality_left
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : K ⟶ K')
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (a b : ℤ) :
    ((-⊗ᴸ-(X)[A]).map (f⟦a⟧')).app (M⟦b⟧) ≫ (derivedTensorShiftIso A K' M a b).hom =
      (derivedTensorShiftIso A K M a b).hom ≫ (((-⊗ᴸ-(X)[A]).map f).app M)⟦a + b⟧' := by
  have h₁ := ((-⊗ᴸ-(X)[A]).flip.obj (M⟦b⟧)).commShiftIso_hom_naturality f a
  have : NatTrans.CommShift ((-⊗ᴸ-(X)[A]).map f) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map f) ℤ)
  have h₂ := NatTrans.shift_app_comm ((-⊗ᴸ-(X)[A]).map f) b M
  have h₃ := (shiftFunctorAdd' (DerivedCategory (Sheaf X.smallEtaleTopology A)) b a (a + b)
    (add_comm b a)).inv.naturality (((-⊗ᴸ-(X)[A]).map f).app M)
  dsimp at h₁ h₂ h₃
  simp only [derivedTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp_assoc, ← h₂, Functor.map_comp_assoc, h₃]

/-- The isomorphism `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧` is natural in `M`. -/
@[reassoc]
lemma derivedTensorShiftIso_hom_naturality_right
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (f : M ⟶ M') (a b : ℤ) :
    ((-⊗ᴸ-(X)[A]).obj (K⟦a⟧)).map (f⟦b⟧') ≫ (derivedTensorShiftIso A K M' a b).hom =
      (derivedTensorShiftIso A K M a b).hom ≫ (((-⊗ᴸ-(X)[A]).obj K).map f)⟦a + b⟧' := by
  have : NatTrans.CommShift ((-⊗ᴸ-(X)[A]).flip.map (f⟦b⟧')) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).flip.map (f⟦b⟧')) ℤ)
  have h₁ := NatTrans.shift_app_comm ((-⊗ᴸ-(X)[A]).flip.map (f⟦b⟧')) a K
  have h₂ := ((-⊗ᴸ-(X)[A]).obj K).commShiftIso_hom_naturality f b
  have h₃ := (shiftFunctorAdd' (DerivedCategory (Sheaf X.smallEtaleTopology A)) b a (a + b)
    (add_comm b a)).inv.naturality (((-⊗ᴸ-(X)[A]).obj K).map f)
  dsimp at h₁ h₂ h₃
  simp only [derivedTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [← reassoc_of% h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc, h₃]

/-- `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧` is natural in both factors:
```
  K⟦a⟧ ⊗ᴸ M⟦b⟧ -------> (K ⊗ᴸ M)⟦a + b⟧
       |                       |
  f⟦a⟧ ⊗ g⟦b⟧             (f ⊗ g)⟦a + b⟧
       v                       v
  K'⟦a⟧ ⊗ᴸ M'⟦b⟧ -----> (K' ⊗ᴸ M')⟦a + b⟧
```
-/
@[reassoc]
lemma derivedTensorHom_shift_comp_derivedTensorShiftIso_hom
    {K K' M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (f : K ⟶ K') (g : M ⟶ M') (a b : ℤ) :
    derivedTensorHom A (f⟦a⟧') (g⟦b⟧') ≫ (derivedTensorShiftIso A K' M' a b).hom =
      (derivedTensorShiftIso A K M a b).hom ≫ (derivedTensorHom A f g)⟦a + b⟧' := by
  simp only [derivedTensorHom, Category.assoc, Functor.map_comp]
  rw [derivedTensorShiftIso_hom_naturality_right, derivedTensorShiftIso_hom_naturality_left_assoc]

end

section

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [(g)^*[A].PreservesFlat]

/-- The tensor comparison of `Lg^*` commutes with a shift of the first factor. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_shift_left
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (n : ℤ) :
    L((g)^*[A]).map ((((-⊗ᴸ-(Y)[A]).flip.obj M).commShiftIso n).hom.app K) ≫
        (L((g)^*[A]).commShiftIso n).hom.app _ ≫
        (((leftDerivedUpperStarTensorComparison A g).app K).app M)⟦n⟧' =
      ((leftDerivedUpperStarTensorComparison A g).app (K⟦n⟧)).app M ≫
        ((-⊗ᴸ-(Z)[A]).map ((L((g)^*[A]).commShiftIso n).hom.app K)).app (L((g)^*[A]).obj M) ≫
        (((-⊗ᴸ-(Z)[A]).flip.obj (L((g)^*[A]).obj M)).commShiftIso n).hom.app
          (L((g)^*[A]).obj K) := by
  have := NatTrans.shift_app_comm (leftDerivedUpperStarTensorComparisonFlipApp A g M) n K
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at this
  simp only [Category.assoc] at this
  exact this

/-- The tensor comparison of `Lg^*` commutes with a shift of the second factor. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_shift_right
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (n : ℤ) :
    L((g)^*[A]).map ((((-⊗ᴸ-(Y)[A]).obj K).commShiftIso n).hom.app M) ≫
        (L((g)^*[A]).commShiftIso n).hom.app _ ≫
        (((leftDerivedUpperStarTensorComparison A g).app K).app M)⟦n⟧' =
      ((leftDerivedUpperStarTensorComparison A g).app K).app (M⟦n⟧) ≫
        ((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).map ((L((g)^*[A]).commShiftIso n).hom.app M) ≫
        (((-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K)).commShiftIso n).hom.app
          (L((g)^*[A]).obj M) := by
  have := NatTrans.shift_app_comm (leftDerivedUpperStarTensorComparisonApp A g K) n M
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at this
  simp only [Category.assoc] at this
  exact this

/-- The tensor comparison of `Lg^*` is compatible with the isomorphisms
`K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧` (`AlgebraicGeometry.Etale.derivedTensorShiftIso`) and the
shift compatibility of `Lg^*`. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_derivedTensorShiftIso
    (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) (a b : ℤ) :
    L((g)^*[A]).map (derivedTensorShiftIso A K M a b).hom ≫
        (L((g)^*[A]).commShiftIso (a + b)).hom.app _ ≫
        (((leftDerivedUpperStarTensorComparison A g).app K).app M)⟦a + b⟧' =
      ((leftDerivedUpperStarTensorComparison A g).app (K⟦a⟧)).app (M⟦b⟧) ≫
        ((-⊗ᴸ-(Z)[A]).map ((L((g)^*[A]).commShiftIso a).hom.app K)).app _ ≫
        ((-⊗ᴸ-(Z)[A]).obj _).map ((L((g)^*[A]).commShiftIso b).hom.app M) ≫
        (derivedTensorShiftIso A (L((g)^*[A]).obj K) (L((g)^*[A]).obj M) a b).hom := by
  have : NatTrans.CommShift ((-⊗ᴸ-(Z)[A]).flip.map
      ((L((g)^*[A]).commShiftIso b).hom.app M)) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).flip.map
      ((L((g)^*[A]).commShiftIso b).hom.app M)) ℤ)
  have h₁ := NatTrans.shift_app_comm ((-⊗ᴸ-(Z)[A]).flip.map
    ((L((g)^*[A]).commShiftIso b).hom.app M)) a (L((g)^*[A]).obj K)
  have h₂ := (shiftFunctorAdd' (DerivedCategory (Sheaf Z.smallEtaleTopology A)) b a (a + b)
    (add_comm b a)).inv.naturality (((leftDerivedUpperStarTensorComparison A g).app K).app M)
  dsimp at h₁ h₂
  simp only [derivedTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc, Functor.map_comp,
    L((g)^*[A]).commShiftIso_add' (add_comm b a), Functor.CommShift.isoAdd'_hom_app]
  rw [← Functor.map_comp_assoc L((g)^*[A]) (((shiftFunctorAdd' _ b a (a + b) _).inv.app _)),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← h₂]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    leftDerivedUpperStarTensorComparison_shift_right]
  simp only [Functor.map_comp, Category.assoc]
  rw [leftDerivedUpperStarTensorComparison_shift_left_assoc]
  erw [reassoc_of% h₁]
  rfl

end

end Etale

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The associator of the derived tensor product and the shifts

The identifications `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧`
(`AlgebraicGeometry.Etale.derivedTensorShiftIso`) on `D(X_ét)` are compatible with the associator
of the derived tensor product: the two identifications
`(K⟦a⟧ ⊗ᴸ L⟦b⟧) ⊗ᴸ M⟦c⟧ ≅ (K ⊗ᴸ (L ⊗ᴸ M))⟦a + b + c⟧` agree. This is
`DerivedCategory.shiftTensorShiftIso_assoc` for the derived category of étale sheaves.

## Main statements

- `AlgebraicGeometry.Etale.derivedTensorShiftIso_assoc`
- `AlgebraicGeometry.Etale.derivedTensorHom_comp_eqToHom_comp_derivedTensorShiftIso_hom`,
  `AlgebraicGeometry.Etale.derivedTensorHom_id_comp_eqToHom_comp_derivedTensorShiftIso_hom`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

attribute [local instance] Sheaf.monoidalCategory in
/-- The associativity of the identifications `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧`
(`AlgebraicGeometry.Etale.derivedTensorShiftIso`):

```
(K⟦a⟧ ⊗ L⟦b⟧) ⊗ M⟦c⟧ ──────────α──────────▶ K⟦a⟧ ⊗ (L⟦b⟧ ⊗ M⟦c⟧)
        │                                            │
        ▼                                            ▼
(K ⊗ L)⟦a + b⟧ ⊗ M⟦c⟧                       K⟦a⟧ ⊗ (L ⊗ M)⟦b + c⟧
        │                                            │
        ▼                                            ▼
((K ⊗ L) ⊗ M)⟦a + b + c⟧ ──α⟦a + b + c⟧──▶ (K ⊗ (L ⊗ M))⟦a + b + c⟧
```
-/
lemma derivedTensorShiftIso_assoc (K L M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (a b c : ℤ) :
    derivedTensorHom A (derivedTensorShiftIso A K L a b).hom (𝟙 (M⟦c⟧)) ≫
      (derivedTensorShiftIso A (((derivedTensor A X).obj K).obj L) M (a + b) c).hom ≫
        (derivedTensorAssociator A X K L M).hom⟦a + b + c⟧' =
    (derivedTensorAssociator A X (K⟦a⟧) (L⟦b⟧) (M⟦c⟧)).hom ≫
      derivedTensorHom A (𝟙 (K⟦a⟧)) (derivedTensorShiftIso A L M b c).hom ≫
        (derivedTensorShiftIso A K (((derivedTensor A X).obj L).obj M) a (b + c)).hom ≫
          eqToHom (by rw [add_assoc]) := by
  have h := DerivedCategory.shiftTensorShiftIso_assoc K L M a b c
  simp only [derivedTensorHom, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.comp_id, Category.id_comp]
  exact h

/-- Moving a change of the shift of the first factor through `derivedTensorShiftIso`. -/
lemma derivedTensorHom_comp_eqToHom_comp_derivedTensorShiftIso_hom
    {Z K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) {a a' : ℤ} (h : a = a') (b : ℤ)
    (hK : K' = K) (f : Z ⟶ K'⟦a⟧) (h' : K'⟦a⟧ = K⟦a'⟧) :
    derivedTensorHom A (f ≫ eqToHom h') (𝟙 (M⟦b⟧)) ≫ (derivedTensorShiftIso A K M a' b).hom =
    derivedTensorHom A f (𝟙 (M⟦b⟧)) ≫ (derivedTensorShiftIso A K' M a b).hom ≫
      eqToHom (by rw [h, hK]) := by
  subst h hK
  simp

/-- Moving a change of the shift of the second factor through `derivedTensorShiftIso`. -/
lemma derivedTensorHom_id_comp_eqToHom_comp_derivedTensorShiftIso_hom
    {Z M' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (a : ℤ) {b b' : ℤ} (h : b = b')
    (hM : M' = M) (f : Z ⟶ M'⟦b⟧) (h' : M'⟦b⟧ = M⟦b'⟧) :
    derivedTensorHom A (𝟙 (K⟦a⟧)) (f ≫ eqToHom h') ≫ (derivedTensorShiftIso A K M a b').hom =
    derivedTensorHom A (𝟙 (K⟦a⟧)) f ≫ (derivedTensorShiftIso A K M' a b).hom ≫
      eqToHom (by rw [h, hM]) := by
  subst h hM
  simp

end Etale

end AlgebraicGeometry

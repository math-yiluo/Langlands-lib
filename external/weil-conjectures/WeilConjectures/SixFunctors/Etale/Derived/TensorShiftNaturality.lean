/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# Naturality of the shift commutation of the derived tensor product

The commutation `(R ⊗ᴸ T)⟦n⟧ ≅ R⟦n⟧ ⊗ᴸ T` of the functor `- ⊗ᴸ T` with the shifts
(`AlgebraicGeometry.Etale.commShiftDerivedTensorFlipObj`) is natural in `T`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

attribute [local instance] Sheaf.monoidalCategory in
/-- The commutation of `- ⊗ᴸ T` with the shifts is natural in `T`. -/
@[reassoc]
lemma derivedTensor_flip_commShiftIso_hom_app_naturality
    {T T' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : T ⟶ T')
    (R : DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ) :
    (((derivedTensor A X).flip.obj T).commShiftIso n).hom.app R ≫
        (((derivedTensor A X).obj R).map e)⟦n⟧' =
      ((derivedTensor A X).obj (R⟦n⟧)).map e ≫
        (((derivedTensor A X).flip.obj T').commShiftIso n).hom.app R := by
  have : NatTrans.CommShift ((derivedTensor A X).flip.map e) ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int)
      (G := curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))) e
  exact NatTrans.shift_app_comm ((derivedTensor A X).flip.map e) n R

end AlgebraicGeometry.Etale

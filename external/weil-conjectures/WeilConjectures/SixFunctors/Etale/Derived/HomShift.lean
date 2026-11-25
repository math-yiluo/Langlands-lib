/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# The derived hom out of a shifted complex

The derived tensor product commutes with shifts in its first variable, naturally in the second
one, `K⟦a⟧ ⊗ᴸ M ≅ (K ⊗ᴸ M)⟦a⟧`. Passing to right adjoints, the derived hom out of a shifted
complex is the shifted derived hom, `RHom(K⟦a⟧, M) ≅ RHom(K, M)⟦-a⟧`; in particular the Verdier
dual of a shift is the opposite shift of the Verdier dual, `𝔻(K⟦a⟧) ≅ (𝔻K)⟦-a⟧`.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensorObjShiftIso`: `K⟦a⟧ ⊗ᴸ - ≅ (K ⊗ᴸ -)⟦a⟧`.
- `AlgebraicGeometry.Etale.derivedHomShiftIso`: `RHom(K⟦a⟧, -) ≅ RHom(K, -)⟦-a⟧`.
- `AlgebraicGeometry.Etale.verdierDualShiftIso`: `𝔻(K⟦a⟧) ≅ (𝔻K)⟦-a⟧`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X : Scheme.{u}}

attribute [local instance] Sheaf.monoidalCategory in
/-- Tensoring with a shifted complex on the left shifts the tensor product,
`K⟦a⟧ ⊗ᴸ M ≅ (K ⊗ᴸ M)⟦a⟧`, naturally in `M`. The components are the commutation of `- ⊗ᴸ M`
with the shift; they are natural in `M` because the derived tensor product commutes with shifts
as a bifunctor (`DerivedCategory.commShift₂CurriedTensor`). -/
noncomputable def derivedTensorObjShiftIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (a : ℤ) :
    (derivedTensor A X).obj (K⟦a⟧) ≅ (derivedTensor A X).obj K ⋙ shiftFunctor _ a :=
  NatIso.ofComponents (fun M ↦ (((derivedTensor A X).flip.obj M).commShiftIso a).app K)
    (fun f ↦
      have : NatTrans.CommShift ((derivedTensor A X).flip.map f) ℤ :=
        Functor.CommShift₂.commShift_flip_map (h := .int)
          (G := curriedTensor (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))) f
      (NatTrans.shift_app_comm ((derivedTensor A X).flip.map f) a K).symm)

/-- The derived hom out of a shifted complex is the shifted derived hom,
`RHom(K⟦a⟧, -) ≅ RHom(K, -)⟦-a⟧`: both are right adjoint to `K⟦a⟧ ⊗ᴸ - ≅ K ⊗ᴸ (-)⟦a⟧`. -/
noncomputable def derivedHomShiftIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (a : ℤ) :
    (RHom(X)[A]).obj (op (K⟦a⟧)) ≅ (RHom(X)[A]).obj (op K) ⋙ shiftFunctor _ (-a) :=
  (derivedTensorHomAdjunction A (K⟦a⟧)).rightAdjointUniq
    (((shiftEquiv _ a).toAdjunction.comp (derivedTensorHomAdjunction A K)).ofNatIsoLeft
      (((derivedTensor A X).obj K).commShiftIso a ≪≫ (derivedTensorObjShiftIso A K a).symm))

variable {S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]

/-- The Verdier dual of a shift is the opposite shift of the Verdier dual,
`𝔻(K⟦m⟧) ≅ (𝔻K)⟦-m⟧`. -/
noncomputable def verdierDualShiftIso
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m : ℤ) :
    (verdierDual Λ a).obj (op (K⟦m⟧)) ≅ ((verdierDual Λ a).obj (op K))⟦-m⟧ :=
  (derivedHomShiftIso (ModuleCat.{u + 1} Λ) K m).app (dualizingComplex Λ a)

end AlgebraicGeometry.Etale

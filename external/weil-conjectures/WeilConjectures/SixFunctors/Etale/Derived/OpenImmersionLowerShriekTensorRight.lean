/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-!
# Extension by zero commutes with tensoring by a fixed complex

For an open immersion `j : U ⟶ X` and a fixed `M` in `D(X_ét)`, the projection formula
`j_!(K ⊗ᴸ Lj^*M) ≅ j_!K ⊗ᴸ M`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`)
as a natural isomorphism of functors of `K`
(`AlgebraicGeometry.Etale.derivedTensorRightCompOpenImmersionLowerShriekIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable [Etale.UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The projection formula `j_!(K ⊗ᴸ Lj^*M) ≅ j_!K ⊗ᴸ M` for an open immersion `j` and a fixed
`M`, as a natural isomorphism of functors of `K`. -/
noncomputable def derivedTensorRightCompOpenImmersionLowerShriekIso
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    derivedTensorRight A U (L((j)^*[A]).obj M) ⋙ D((j)_!open[A]) ≅
      D((j)_!open[A]) ⋙ derivedTensorRight A X M :=
  NatIso.ofComponents (fun K ↦ ((derivedOpenImmersionLowerShriekProjectionIso A j).app K).app M)
    fun φ ↦
      NatTrans.congr_app ((derivedOpenImmersionLowerShriekProjectionIso A j).hom.naturality φ) M

end Etale

end AlgebraicGeometry

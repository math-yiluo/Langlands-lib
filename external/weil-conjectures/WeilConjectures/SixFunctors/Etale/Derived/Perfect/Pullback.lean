/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# Internal hom out of a dualizable étale complex versus pullback

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_leftDerivedUpperStar_derivedHom`
  (`theorem-poincare-duality-frobenius--1`): the internal hom with
  a dualizable first variable commutes with pullback.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale.DerivedCategory

variable {A X}

/-- Blueprint `theorem-poincare-duality-frobenius--1`: Internal Hom versus pullback for a
site-perfect first variable. This is also blueprint `theorem-poincare-duality-frobenius--1`.

For a morphism of schemes `g : Y' ⟶ X`, a dualizable `M` and any `N` in `D(X_ét)`, the
canonical comparison

`Lg^* RHom_Λ(M, N) ⟶ RHom_Λ(Lg^* M, Lg^* N)`

is an isomorphism. Writing `M^∨` for a left dual of `M`, this is the chain
`Lg^* RHom(M, N) ≅ Lg^*(M^∨ ⊗ᴸ N) ≅ Lg^* M^∨ ⊗ᴸ Lg^* N ≅ RHom(Lg^* M, Lg^* N)`, the last step
because the monoidal functor `Lg^*` sends the duality between `M^∨` and `M` to a duality
between `Lg^* M^∨` and `Lg^* M`. -/
theorem nonempty_iso_leftDerivedUpperStar_derivedHom [Etale.UpperStarPreservesFlat A]
    {Y' : Scheme.{u}} (g : Y' ⟶ X)
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hM : IsDualizable M)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((L((g)^*[A])).obj ((RHom(X)[A].obj (op M)).obj N) ≅
      (RHom(Y')[A].obj (op ((L((g)^*[A])).obj M))).obj ((L((g)^*[A])).obj N)) := by
  obtain ⟨_⟩ := hM
  obtain ⟨_⟩ := nonempty_exactPairing_swap M Mᘁ
  obtain ⟨_⟩ := nonempty_monoidal_leftDerivedUpperStar A g
  let _ := ExactPairing.map L((g)^*[A]) Mᘁ M
  exact ⟨L((g)^*[A]).mapIso (MonoidalClosed.ihomObjIsoTensor Mᘁ M N) ≪≫
    (Functor.Monoidal.μIso L((g)^*[A]) Mᘁ N).symm ≪≫
    (MonoidalClosed.ihomObjIsoTensor _ _ _).symm⟩

end Etale.DerivedCategory

end AlgebraicGeometry

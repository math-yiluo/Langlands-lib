/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-!
# Reduction of the projection map through its first variable

Let `c` be a compactification of `f : X ⟶ Y`, `N_Y` a dualizable object of `D(Y_ét)` and
`a : Lf^*N_Y ≅ N_X`. The reduction `PF_{K, L} ⊗ᴸ N_Y` of the projection map
`PF_{K, L} : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` is an isomorphism as soon as the projection map
`PF_{K ⊗ᴸ N_X, L}` is: by
`AlgebraicGeometry.Etale.isIso_derivedTensorRight_map_projectionMapOfCompactification_iff` the
former is invertible if and only if `PF_{K, L ⊗ᴸ N_Y}` is, and by the associativity of the
projection map (`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`) at
`(K, N_Y, L)` the latter differs from `PF_{K ⊗ᴸ Lf^*N_Y, L}` by isomorphisms, `PF_{K, N_Y}`
being invertible for the dualizable `N_Y`.

For `N = (Λ/J)` constant this moves the reduction of the coefficients from the second variable
of the projection map, where it is in the blueprint (`sk-prop-sf-pf-reduction`), to the first
one, where the object becomes torsion and proper base change applies.

## Main statements

- `AlgebraicGeometry.Etale.isIso_derivedTensorRight_map_projectionMapOfCompactification_of_tensor`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The projection formula at `(K, L)` passes to objects isomorphic to `L`. -/
lemma HasProjectionFormulaOfCompactification.of_iso_right
    {K : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L L' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : L ≅ L')
    (h : HasProjectionFormulaOfCompactification A c K L) :
    HasProjectionFormulaOfCompactification A c K L' :=
  (NatTrans.isIso_app_iff_of_iso ((projectionMapOfCompactification A c).app K) e).1 h

/-- The projection formula at `(K, L)` passes to objects isomorphic to `K`. -/
lemma HasProjectionFormulaOfCompactification.of_iso_left
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {L : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : K ≅ K')
    (h : HasProjectionFormulaOfCompactification A c K L) :
    HasProjectionFormulaOfCompactification A c K' L :=
  (NatTrans.isIso_app_iff_of_iso
    (((flipFunctor _ _ _).map (projectionMapOfCompactification A c)).app L) e).1 h

/-- **Moving the reduction to the first variable of the projection map.** For a dualizable
`N_Y` and `a : Lf^*N_Y ≅ N_X`, the reduction `PF_{K, L} ⊗ᴸ N_Y` of the projection map is an
isomorphism as soon as the projection map `PF_{K ⊗ᴸ N_X, L}` is. -/
theorem isIso_derivedTensorRight_map_projectionMapOfCompactification_of_tensor
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (hN : IsDualizable NY) (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : HasProjectionFormulaOfCompactification A c (((-⊗ᴸ-(X)[A]).obj K).obj NX) L) :
    IsIso ((derivedTensorRight A Y NY).map
      (((projectionMapOfCompactification A c).app K).app L)) := by
  have hc := isIso_rightDerivedLowerShriekDerivedTensorRightMap_of_isDualizable A c a hN
  rw [isIso_derivedTensorRight_map_projectionMapOfCompactification_iff A c a K L
    (inferInstanceAs (IsIso ((rightDerivedLowerShriekDerivedTensorRightMap A c a.hom).app _)))]
  -- `PF_{K, N_Y ⊗ L}` is invertible
  have h' : HasProjectionFormulaOfCompactification A c (K ⊗ L((f)^*[A]).obj NY) L :=
    h.of_iso_left A c (whiskerLeftIso K a).symm
  have hKN : IsIso (((projectionMapOfCompactification A c).app K).app NY) :=
    hasProjectionFormulaOfCompactification_of_isDualizable A c K hN
  have hassoc := projectionMapOfCompactification_assoc A c K NY L
  have : IsIso (((projectionMapOfCompactification A c).app K).app (NY ⊗ L)) := by
    have : IsIso ((α_ ((Rf_!(c)[A]).obj K) NY L).hom ≫
        ((projectionMapOfCompactification A c).app K).app (NY ⊗ L) ≫
        Rf_!(c)[A].map (K ◁ ((leftDerivedUpperStarTensorComparison A f).app NY).app L)) := by
      rw [← hassoc]
      have : IsIso (((projectionMapOfCompactification A c).app
          (K ⊗ L((f)^*[A]).obj NY)).app L) := h'
      infer_instance
    have : IsIso (((projectionMapOfCompactification A c).app K).app (NY ⊗ L) ≫
        Rf_!(c)[A].map (K ◁ ((leftDerivedUpperStarTensorComparison A f).app NY).app L)) :=
      IsIso.of_isIso_comp_left (α_ ((Rf_!(c)[A]).obj K) NY L).hom _
    exact IsIso.of_isIso_comp_right _
      (Rf_!(c)[A].map (K ◁ ((leftDerivedUpperStarTensorComparison A f).app NY).app L))
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf Y.smallEtaleTopology A)
  exact HasProjectionFormulaOfCompactification.of_iso_right A c (β_ NY L) this

end AlgebraicGeometry.Etale

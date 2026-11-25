/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingle
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# `Ext` out of a pulled back projective sheaf detects higher direct images

Let `g : X ⟶ Y` be a morphism of schemes and `P` a projective pro-étale sheaf on `Y` (for
instance the constant sheaf `Λ` when `Y` is the spectrum of an algebraically closed field, where
global sections are exact). If `Extⁿ(g^* P, F) ≠ 0` for a pro-étale sheaf `F` on `X`, then
`Rⁿ g_* F ≠ 0` (`AlgebraicGeometry.ProEtale.not_isZero_homology_of_ext_ne_zero`): by the derived
adjunction `Lg^* ⊣ Rg_*` and `Lg^* ≅ D(g^*)`, a nonzero class gives a nonzero morphism
`P[0] ⟶ (Rg_* F)[n]`, and such morphisms vanish when `H⁰((Rg_* F)[n]) = Rⁿg_* F` vanishes, `P`
being projective (`DerivedCategory.eq_zero_of_isZero_homology_zero`).
-/

@[expose] public section

universe w u' u

open CategoryTheory Limits Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- A nonzero class in `Extⁿ(g^* P, F)`, for a projective sheaf `P` on `Y`, forces
`Rⁿ g_* F ≠ 0`. -/
theorem not_isZero_homology_of_ext_ne_zero [HasExt.{w} (Sheaf (Scheme.ProEt.topology X) A)]
    (P : Sheaf (Scheme.ProEt.topology Y) A) [Projective P]
    (F : Sheaf (Scheme.ProEt.topology X) A) (n : ℕ) (x : Ext ((g)^*[A].obj P) F n)
    (hx : x ≠ 0) :
    ¬ IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((R((g)_*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  intro hZ
  apply hx
  let adj := derivedUpperStarLowerStarAdjunction A g
  let K := (R((g)_*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  -- the transported morphism `P[0] ⟶ (Rg_* F)[n]`
  let e : (DerivedCategory.singleFunctor _ 0).obj ((g)^*[A].obj P) ≅
      L((g)^*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj P) :=
    ((((g)^*[A]).mapDerivedCategorySingleFunctor 0).app P).symm ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.app _
  let ψ : (DerivedCategory.singleFunctor _ 0).obj P ⟶ K⟦(n : ℤ)⟧ :=
    adj.homEquiv _ _ (e.inv ≫ x.hom) ≫
      ((R((g)_*[A])).commShiftIso (n : ℤ)).hom.app _
  have hψ : ψ = 0 := DerivedCategory.eq_zero_of_isZero_homology_zero P _
    (hZ.of_iso (((DerivedCategory.homologyFunctor _ 0).shiftIso (n : ℤ) 0 n (by simp)).app K))
    ψ
  have h1 : adj.homEquiv _ _ (e.inv ≫ x.hom) = 0 := by
    simpa [ψ] using hψ =≫ ((R((g)_*[A])).commShiftIso (n : ℤ)).inv.app _
  have h2 : e.inv ≫ x.hom = 0 := by
    have := adj.isLeftAdjoint
    rw [← (adj.homEquiv _ _).symm_apply_apply (e.inv ≫ x.hom), h1,
      Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  have h3 : x.hom = 0 := by simpa using e.hom ≫= h2
  exact Ext.ext (h3.trans (Ext.zero_hom (X := (g)^*[A].obj P) (Y := F) (n := n)).symm)

end AlgebraicGeometry.ProEtale

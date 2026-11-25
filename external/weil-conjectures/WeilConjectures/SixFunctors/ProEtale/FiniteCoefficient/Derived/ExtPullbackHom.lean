/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtPullback

/-!
# Nonzero `Ext` out of a pulled back sheaf gives nonzero morphisms to direct images

Let `g : X ⟶ Y` be a morphism of schemes, `P` a pro-étale sheaf on `Y` and `F` a pro-étale sheaf
on `X`. By the derived adjunction `Lg^* ⊣ Rg_*` and `Lg^* ≅ D(g^*)`, a class
`x ∈ Extⁿ(g^* P, F)` is the same as a morphism `P[0] ⟶ (Rg_* F)[n]`, which is nonzero when `x`
is (`AlgebraicGeometry.ProEtale.hom_ne_zero_of_ext_ne_zero`).

## Main statements

- `AlgebraicGeometry.ProEtale.hom_ne_zero_of_ext_ne_zero`.
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

/-- A nonzero class in `Extⁿ(g^* P, F)` gives a nonzero morphism `P[0] ⟶ (Rg_* F)[n]` in the
derived category. -/
theorem hom_ne_zero_of_ext_ne_zero [HasExt.{w} (Sheaf (Scheme.ProEt.topology X) A)]
    (P : Sheaf (Scheme.ProEt.topology Y) A) (F : Sheaf (Scheme.ProEt.topology X) A) (n : ℕ)
    (x : Ext ((g)^*[A].obj P) F n) (hx : x ≠ 0) :
    ∃ ψ : (DerivedCategory.singleFunctor _ 0).obj P ⟶
      ((R((g)_*[A])).obj ((DerivedCategory.singleFunctor _ 0).obj F))⟦(n : ℤ)⟧, ψ ≠ 0 := by
  let adj := derivedUpperStarLowerStarAdjunction A g
  let e : (DerivedCategory.singleFunctor _ 0).obj ((g)^*[A].obj P) ≅
      L((g)^*[A]).obj ((DerivedCategory.singleFunctor _ 0).obj P) :=
    ((((g)^*[A]).mapDerivedCategorySingleFunctor 0).app P).symm ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.app _
  refine ⟨adj.homEquiv _ _ (e.inv ≫ x.hom) ≫ ((R((g)_*[A])).commShiftIso (n : ℤ)).hom.app _,
    fun hψ ↦ hx ?_⟩
  have h1 : adj.homEquiv _ _ (e.inv ≫ x.hom) = 0 := by
    simpa using hψ =≫ ((R((g)_*[A])).commShiftIso (n : ℤ)).inv.app _
  have h2 : e.inv ≫ x.hom = 0 := by
    have := adj.isLeftAdjoint
    rw [← (adj.homEquiv _ _).symm_apply_apply (e.inv ≫ x.hom), h1,
      Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  have h3 : x.hom = 0 := by simpa using e.hom ≫= h2
  exact Ext.ext (h3.trans (Ext.zero_hom (X := (g)^*[A].obj P) (Y := F) (n := n)).symm)

end AlgebraicGeometry.ProEtale

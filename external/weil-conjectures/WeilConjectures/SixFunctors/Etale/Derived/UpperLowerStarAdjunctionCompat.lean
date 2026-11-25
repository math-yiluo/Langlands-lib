/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# The two derived adjunctions for the pushforward

For a morphism of schemes `g`, the derived pushforward `Rg_*` is right adjoint both to the
levelwise pullback `D(g^*)` (`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`)
and to the derived pullback `Lg^*` (`AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction`).
The first is the second transported along `Lg^* ≅ D(g^*)`
(`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction_eq`).
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The adjunction `D(g^*) ⊣ Rg_*` is the adjunction `Lg^* ⊣ Rg_*` transported along
`Lg^* ≅ D(g^*)`. -/
lemma mapDerivedUpperStarLowerStarAdjunction_eq :
    mapDerivedUpperStarLowerStarAdjunction A g =
      (derivedUpperStarLowerStarAdjunction A g).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory A g) := by
  refine ((Etale.upperStarLowerStarAdjunction A g).mapHomotopyCategory (.up ℤ)
    ).derived_eq_ofNatIsoLeft (HomotopyCategory.quasiIso _ (.up ℤ))
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ?_
  ext X
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  rw [← (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]


/-- Under the derived adjunctions `Lg^* ⊣ Rg_*`, the composition isomorphism of the derived
pullbacks has the same conjugate as the composition isomorphism `D(g₁₂^*) ≅ D(g₂^*) ⋙ D(g₁^*)`
under the adjunctions `D(g^*) ⊣ Rg_*`. -/
lemma conjugateEquiv_leftDerivedUpperStarComp_hom {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) :
    conjugateEquiv ((derivedUpperStarLowerStarAdjunction A g₂).comp
        (derivedUpperStarLowerStarAdjunction A g₁)) (derivedUpperStarLowerStarAdjunction A g₁₂)
        (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom =
      conjugateEquiv ((mapDerivedUpperStarLowerStarAdjunction A g₂).comp
          (mapDerivedUpperStarLowerStarAdjunction A g₁))
        (mapDerivedUpperStarLowerStarAdjunction A g₁₂)
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A g₁ g₂ g₁₂ hg) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).hom := by
  rw [mapDerivedUpperStarLowerStarAdjunction_eq, mapDerivedUpperStarLowerStarAdjunction_eq,
    mapDerivedUpperStarLowerStarAdjunction_eq]
  ext K
  simp [conjugateEquiv_apply_app, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]
end Etale

end AlgebraicGeometry

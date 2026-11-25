/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The exceptional inverse image along an isomorphism

For an isomorphism of schemes `e : X ≅ Y` the exceptional inverse image is the derived
pullback, `Re^! ≅ Le^*`. Both functors are right adjoint to the same functor: `Re_! ≅ Re_*`
because `e` is proper (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`),
`Re_* ≅ L(e⁻¹)^*` (`AlgebraicGeometry.Etale.rightDerivedLowerStarIsoLeftDerivedUpperStarInv`),
and `L(e⁻¹)^* ⊣ R(e⁻¹)_* ≅ Le^*`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIso`: `Re^! ≅ Le^*`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_eq`: equal morphisms have
  isomorphic exceptional inverse images, whatever the instances of `HasCompactification`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso`: the counit
  of `Rf_! ⊣ Rf^!` is an isomorphism when `f` is an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Equal morphisms have isomorphic exceptional inverse images. This transports the
exceptional inverse image along an equation of morphisms, which a rewrite cannot do since the
functor also depends on the `HasCompactification` instance. -/
theorem nonempty_iso_rightDerivedUpperShriek_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (h : f = g) :
    Nonempty (R(f)^![Λ] ≅ R(g)^![Λ]) := by
  subst h
  exact ⟨Iso.refl _⟩

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- For an isomorphism of schemes `e : X ≅ Y`, the derived lower shriek `Re_!` is a left
adjoint, for any coefficient category: `Re_! ≅ Re_* ≅ L(e⁻¹)^*`, and `L(e⁻¹)^*` is left adjoint to
`R(e⁻¹)_*`. -/
instance isLeftAdjoint_rightDerivedLowerShriek_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (R(e.hom)_![A]).IsLeftAdjoint :=
  have := (derivedUpperStarLowerStarAdjunction A e.inv).isLeftAdjoint
  Functor.isLeftAdjoint_of_iso
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A e.hom ≪≫
      rightDerivedLowerStarIsoLeftDerivedUpperStarInv A e).symm

/-- For an isomorphism of schemes `e : X ≅ Y`, the exceptional inverse image along `e` is the
derived pullback, `Re^! ≅ Le^*`: both are right adjoint to `Re_! ≅ Re_* ≅ L(e⁻¹)^*`. -/
noncomputable def rightDerivedUpperShriekIsoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    R(e.hom)^![Λ] ≅ L((e.hom)^*[ModuleCat.{u + 1} Λ]) :=
  ((rightDerivedUpperShriekAdjunction Λ e.hom).ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) e.hom ≪≫
        rightDerivedLowerStarIsoLeftDerivedUpperStarInv (ModuleCat.{u + 1} Λ) e)).rightAdjointUniq
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e.inv).ofNatIsoRight
      (rightDerivedLowerStarIsoLeftDerivedUpperStarInv (ModuleCat.{u + 1} Λ) e.symm))

/-- For an isomorphism of schemes `f : X ⟶ Y`, the counit `Rf_! Rf^! ⟶ 𝟭` of `Rf_! ⊣ Rf^!` is an
isomorphism: `Rf^! ⋙ Rf_! ≅ Lf^* ⋙ L(f⁻¹)^* ≅ L(𝟙_Y)^* ≅ 𝟭`. -/
theorem isIso_rightDerivedUpperShriekAdjunction_counit_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] [HasCompactification f] :
    IsIso (rightDerivedUpperShriekAdjunction Λ f).counit :=
  (rightDerivedUpperShriekAdjunction Λ f).isIso_counit_of_iso
    (Functor.isoWhiskerRight (rightDerivedUpperShriekIsoOfIso Λ (asIso f)) _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1}
          Λ) f ≪≫
        rightDerivedLowerStarIsoLeftDerivedUpperStarInv (ModuleCat.{u + 1} Λ) (asIso f)) ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (inv f) f (𝟙 Y) (by simp)).symm ≪≫
      leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (𝟙 Y) ≪≫
      Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} Λ) Y) ≪≫
      Functor.mapDerivedCategoryIdIso _)

end Etale

end AlgebraicGeometry

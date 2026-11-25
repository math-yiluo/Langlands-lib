/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# Coherence of the projection formula

Let `f : X ⟶ Y` admit a compactification. We record the coherence properties of the projection
transformation `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of blueprint
`proposition-composition-base-change-rf-shriek--1` (detailed node `prop-sf-pf-coherence`) as
identities between morphisms:

- naturality in `K` and `L`
  (`AlgebraicGeometry.Etale.projectionMapOfCompactification_naturality`): `PF` is a natural
  transformation of bifunctors;
- the identity case (`AlgebraicGeometry.Etale.hasProjectionFormula_id`);
- independence of the compactification: the comparison isomorphisms `Rf_!(c) ≅ Rf_!` intertwine
  the projection maps
  (`AlgebraicGeometry.Etale.projectionMapOfCompactification_rightDerivedLowerShriekIso`,
  and, along a refinement and for any coefficients,
  `AlgebraicGeometry.Etale.projectionMapOfCompactification_comparison`);
- for proper `f`, agreement with the direct-image projection formula through `Rf_! ≅ Rf_*`
  (`AlgebraicGeometry.Etale.projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar`);
- compatibility with base change
  (`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`);
- associativity with respect to the derived tensor product
  (`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`), and, as its
  special case for the constant complex `(Λ/J)_Y`, compatibility with finite reduction
  `- ⊗ᴸ (Λ/J)` (`AlgebraicGeometry.Etale.projectionMapOfCompactification_reductionModIdeal`).

## Implementation notes

Finite reduction is modelled in this repository, as in
`AlgebraicGeometry.Etale.reductionModIdeal`, by the endofunctor `K ↦ K ⊗ᴸ (Λ/J)_X` of `D(X_ét, Λ)`;
its compatibility with `Rf_!` is the projection map at `L = (Λ/J)_Y`
(`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite`), so
the reduction square of the projection map is the associativity of the projection map.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: Coherence of the projection
formula; naturality in `K` and `L`. For morphisms `x : K ⟶ K'` and `y : L ⟶ L'`, the square
```
Rf_!K ⊗ᴸ L  ──PF──▶ Rf_!(K ⊗ᴸ Lf^*L)
    │ Rf_!x ⊗ y          │ Rf_!(x ⊗ Lf^*y)
    ▼                    ▼
Rf_!K' ⊗ᴸ L' ──PF──▶ Rf_!(K' ⊗ᴸ Lf^*L')
```
commutes, for `Rf_!` computed with any compactification `c` of `f`. -/
theorem projectionMapOfCompactification_naturality (c : Compactification f)
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (x : K ⟶ K')
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (y : L ⟶ L') :
    ((-⊗ᴸ-(Y)[A]).map ((Rf_!(c)[A]).map x)).app L ≫
        ((-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K')).map y ≫
        ((projectionMapOfCompactification A c).app K').app L' =
      ((projectionMapOfCompactification A c).app K).app L ≫
        (Rf_!(c)[A]).map (((-⊗ᴸ-(X)[A]).map x).app (L((f)^*[A]).obj L) ≫
          ((-⊗ᴸ-(X)[A]).obj K').map (L((f)^*[A]).map y)) := by
  have h₁ := NatTrans.congr_app ((projectionMapOfCompactification A c).naturality x) L
  have h₂ := ((projectionMapOfCompactification A c).app K').naturality y
  rw [Functor.map_comp]
  exact (congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h₁).trans (Category.assoc _ _ _)))

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: Coherence of the projection
formula; agreement with the direct-image projection formula for proper `f`. For a proper `f`, the
identification `Rf_! ≅ Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`) intertwines the
projection map `PF` of `Rf_!` with the projection map `Rf_*K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^*L)` of the direct
image:
```
Rf_!K ⊗ᴸ L ──PF──▶ Rf_!(K ⊗ᴸ Lf^*L)
    │ ≅                  │ ≅
    ▼                    ▼
Rf_*K ⊗ᴸ L ──PF_*──▶ Rf_*(K ⊗ᴸ Lf^*L)
``` -/
theorem projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar (f : X ⟶ Y)
    [IsProper f] (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMap A f).app K).app L ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom.app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) =
      ((-⊗ᴸ-(Y)[A]).map ((rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom.app K)).app L ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app L := by
  have h : (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom =
      compactificationForgetSupports A (HasCompactification.compactification f) := by
    rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
      rightDerivedLowerShriekToLowerStarComp_comp_eq]
    rfl
  rw [h]
  exact projectionMapOfCompactification_comp_compactificationForgetSupports A _ K L

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: Coherence of the projection
formula; for proper `f`, the projection formula for `Rf_!` holds at `(K, L)` if and only if the
direct-image projection formula holds there. -/
theorem hasProjectionFormula_iff_isIso_rightDerivedLowerStarProjectionMap (f : X ⟶ Y)
    [IsProper f] (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    HasProjectionFormula A f K L ↔
      IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app L) :=
  isIso_projectionMapOfCompactification_app_app_iff_of_isProper A _ K L

end General

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

set_option hygiene false in
/-- The constant complex `(Λ/J)_Y` placed in degree zero, by which `reductionModIdeal` tensors. -/
local notation "𝐏(" Y ", " J ")" =>
  constantSingle (ModuleCat.{u + 1} Λ) Y (ModuleCat.of Λ (Λ ⧸ J))

section Reduction

-- The generic associativity `AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`
-- braids `ModuleCat Λ` through its symmetric structure and étale sheaves through
-- `Etale.sheafBraidedCategory`; use the same instances here so that the specialisation below
-- matches it syntactically rather than up to an expensive unfolding.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

/-- Blueprint `proposition-composition-base-change-rf-shriek--1` (and `sk-prop-sf-pf-reduction`):
compatibility of the projection formula with finite reduction. Writing `ρ = - ⊗ᴸ (Λ/J)` for the
reduction `AlgebraicGeometry.Etale.reductionModIdeal` and `P = (Λ/J)_Y`, the reduction of the
projection map `ρ(PF_{K, L}) = PF_{K, L} ▷ P`, followed by the reduction comparison
`ρ Rf_! ⟶ Rf_! ρ` (the projection map at `P`), is the projection map at `(K, L ⊗ᴸ P)` read through
the associativity of `⊗ᴸ` and the tensor comparison of `Lf^*`. -/
theorem projectionMapOfCompactification_reductionModIdeal (c : Compactification f)
    (J : Ideal Λ) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L ▷ 𝐏(Y, J) ≫
        ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app
          (K ⊗ L((f)^*[ModuleCat.{u + 1} Λ]).obj L)).app (𝐏(Y, J)) ≫
        (Rf_!(c)[ModuleCat.{u + 1} Λ]).map (α_ K (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)
          (L((f)^*[ModuleCat.{u + 1} Λ]).obj 𝐏(Y, J))).hom =
      (α_ ((Rf_!(c)[ModuleCat.{u + 1} Λ]).obj K) L 𝐏(Y, J)).hom ≫
        ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app (L ⊗ 𝐏(Y, J)) ≫
        (Rf_!(c)[ModuleCat.{u + 1} Λ]).map (K ◁
          ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) f).app L).app (𝐏(Y, J))) :=
  projectionMapOfCompactification_assoc _ c K L _

end Reduction

variable [Finite Λ]

/-- Blueprint `proposition-composition-base-change-rf-shriek--1`: Coherence of the projection
formula; independence of the compactification. For torsion coefficients and a quasi-compact `f`, the
comparison isomorphism `Rf_!(c) ≅ Rf_!` between the compactly supported direct images computed with
a compactification `c` and with the chosen one
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`) intertwines the projection maps:
```
Rf_!(c)K ⊗ᴸ L ──PF_c──▶ Rf_!(c)(K ⊗ᴸ Lf^*L)
     │ ≅                      │ ≅
     ▼                        ▼
 Rf_!K ⊗ᴸ L   ──PF──▶   Rf_!(K ⊗ᴸ Lf^*L)
``` -/
theorem projectionMapOfCompactification_rightDerivedLowerShriekIso [QuasiCompact f]
    [HasCompactification f] (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L ≫
        (rightDerivedLowerShriekIso Λ c).hom.app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) =
      ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map ((rightDerivedLowerShriekIso Λ c).hom.app K)).app L ≫
        ((projectionMap _ f).app K).app L :=
  projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso Λ c _ K L

end Torsion

end Etale

end AlgebraicGeometry

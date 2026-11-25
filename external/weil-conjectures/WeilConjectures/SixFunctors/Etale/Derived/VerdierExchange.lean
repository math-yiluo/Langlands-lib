/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality

/-!
# The Verdier-duality exchange as a natural isomorphism

Let `f : X ⟶ Y` and `a_Y : Y ⟶ S` admit compactifications, with `a_X = f ≫ a_Y`, and let
`ω_X = Ra_X^! Λ_S`, `ω_Y = Ra_Y^! Λ_S` be the dualizing complexes. Given a composition
isomorphism `R(a_Y ∘ f)_! ≅ Ra_{Y!} ∘ Rf_!` (`proposition-composition-base-change-rf-shriek--1`),
its mate is an isomorphism `Rf^! ω_Y ≅ ω_X`, and the tensor–Hom exchange at `N = ω_Y` then gives the
*Verdier-duality exchange*

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`,

natural in `M`. This file constructs it as a natural isomorphism of functors
`D(X_ét)ᵒᵖ ⥤ D(Y_ét)`, for every coefficient category in which the projection formula holds.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIso`
  (`lemma-internal-adjunction-two-exchange-formulas--2`, Step 1): `Rf^! ω_Y ≅ ω_X`, the mate of a
  composition isomorphism.
- `AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekIso`
(`lemma-internal-adjunction-two-exchange-formulas--2`):
  the natural isomorphism `𝔻_Y ∘ Rf_! ≅ Rf_* ∘ 𝔻_X`.
- `AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekShiftIso`
  (`lemma-internal-adjunction-two-exchange-formulas--2`, shifts):
  `𝔻_Y (Rf_!(M⟦a⟧)) ≅ (Rf_* 𝔻_X M)⟦-a⟧`.

## Main statements

- `AlgebraicGeometry.Etale.verdierDualRightDerivedLowerShriekIso_hom_app`: the exchange is the
  inverse of the tensor–Hom exchange at `N = ω_Y` followed by `Rf_* RHom(M, Rf^! ω_Y ≅ ω_X)`;
  in particular its compatibility with changes of coefficients is that of the tensor–Hom
  exchange (`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv`)
  and of the mate `Rf^! ω_Y ≅ ω_X`.

At finite coefficients the existence of the natural isomorphism is
`AlgebraicGeometry.Etale.nonempty_verdierDual_rightDerivedLowerShriek_natIso`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ S) [HasCompactification f]
  [HasCompactification aY] [HasCompactification (f ≫ aY)]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--2`, Step 1: `Rf^! ω_Y ≅ ω_X`.

For a composition isomorphism `e : R(f ≫ a_Y)_! ≅ Rf_! ⋙ Ra_{Y!}`
(`proposition-composition-base-change-rf-shriek--1`), the mate of `e` under the adjunctions
`Rf_! ⊣ Rf^!` is an isomorphism `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!`
(`proposition-composition-open-restriction-compactifications-f--1`); evaluated at the unit `Λ_S` it
reads `Rf^! ω_Y ≅ ω_X`. -/
noncomputable def rightDerivedUpperShriekDualizingComplexIso
    (e : R(f ≫ aY)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(aY)_![ModuleCat.{u + 1}
        Λ]) :
    (R(f)^![Λ]).obj (dualizingComplex Λ aY) ≅ dualizingComplex Λ (f ≫ aY) :=
  (((rightDerivedUpperShriekAdjunction Λ (f ≫ aY)).ofNatIsoLeft e).rightAdjointUniq
    ((rightDerivedUpperShriekAdjunction Λ f).comp
      (rightDerivedUpperShriekAdjunction Λ aY))).symm.app (𝟙_ _)

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--2`: Verdier-duality exchange.

Let `f : X ⟶ Y` and the structure morphism `a_Y : Y ⟶ S` admit compactifications, with
`a_X = f ≫ a_Y`, and assume the projection formula for `f` (axiom (A3) of `def-sf-datum`). For a
composition isomorphism `e : R(a_Y ∘ f)_! ≅ Ra_{Y!} ∘ Rf_!` there is an isomorphism

`𝔻_Y (Rf_! M) ≅ Rf_* 𝔻_X M`,

natural in `M ∈ D(X_ét)`. As in the blueprint it is the tensor–Hom exchange
`Rf_* RHom_X(M, Rf^! N) ≅ RHom_Y(Rf_! M, N)`
(`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso`) at `N = ω_Y`, followed by the
mate `Rf^! ω_Y ≅ ω_X` of `e` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIso`).
The blueprint takes `M ∈ Dᵇctf(X, Λ)`; no finiteness of `M` is needed. -/
noncomputable def verdierDualRightDerivedLowerShriekIso [IsIso (projectionMap (ModuleCat.{u + 1} Λ)
    f)]
    (e : R(f ≫ aY)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(aY)_![ModuleCat.{u + 1}
        Λ]) :
    (R(f)_![ModuleCat.{u + 1} Λ]).op ⋙ verdierDual Λ aY ≅ verdierDual Λ (f ≫ aY) ⋙
        R((f)_*[ModuleCat.{u + 1} Λ]) :=
  (Functor.isoWhiskerRight (derivedHomRightDerivedLowerShriekIso Λ f)
      ((CategoryTheory.evaluation _ _).obj (dualizingComplex Λ aY))).symm ≪≫
    NatIso.ofComponents (fun M ↦ (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj M).mapIso (rightDerivedUpperShriekDualizingComplexIso Λ
            f aY e)))
      (fun {M M'} g ↦ by
        dsimp [verdierDual]
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        exact (((RHom(X)[ModuleCat.{u + 1} Λ]).map g).naturality _).symm)

/-- The component of the Verdier-duality exchange: the inverse of the tensor–Hom exchange at
`N = ω_Y`, followed by `Rf_* RHom(M, -)` of `Rf^! ω_Y ≅ ω_X`. -/
lemma verdierDualRightDerivedLowerShriekIso_hom_app [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)]
    (e : R(f ≫ aY)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(aY)_![ModuleCat.{u + 1}
        Λ])
    (M : (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))ᵒᵖ) :
    (verdierDualRightDerivedLowerShriekIso Λ f aY e).hom.app M =
      ((derivedHomRightDerivedLowerShriekIso Λ f).inv.app M).app (dualizingComplex Λ aY) ≫
        (R((f)_*[ModuleCat.{u + 1} Λ])).map (((RHom(X)[ModuleCat.{u + 1} Λ]).obj M).map
          (rightDerivedUpperShriekDualizingComplexIso Λ f aY e).hom) :=
  rfl

/-- Blueprint `lemma-internal-adjunction-two-exchange-formulas--2`: Verdier-duality exchange,
compatibility with shifts.

For every `M` and `a : ℤ`, `𝔻_Y (Rf_!(M⟦a⟧)) ≅ (Rf_* 𝔻_X M)⟦-a⟧`: the Verdier dual of the
commutation `Rf_!(M⟦a⟧) ≅ (Rf_! M)⟦a⟧`, then `RHom(N⟦a⟧, ω_Y) ≅ RHom(N, ω_Y)⟦-a⟧`
(`AlgebraicGeometry.Etale.derivedHomShiftIso`), then the shift of the exchange for `M`. -/
noncomputable def verdierDualRightDerivedLowerShriekShiftIso [IsIso (projectionMap (ModuleCat.{u +
    1} Λ) f)]
    (e : R(f ≫ aY)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(aY)_![ModuleCat.{u + 1}
        Λ])
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ) :
    (verdierDual Λ aY).obj (op ((R(f)_![ModuleCat.{u + 1} Λ]).obj (M⟦a⟧))) ≅
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ (f ≫ aY)).obj (op M)))⟦-a⟧ :=
  ((verdierDual Λ aY).mapIso (((R(f)_![ModuleCat.{u + 1} Λ]).commShiftIso a).app M).op).symm ≪≫
    (derivedHomShiftIso (ModuleCat.{u + 1} Λ) _ a).app (dualizingComplex Λ aY) ≪≫
      (shiftFunctor _ (-a)).mapIso ((verdierDualRightDerivedLowerShriekIso Λ f aY e).app (op M))

end General

end Etale

end AlgebraicGeometry

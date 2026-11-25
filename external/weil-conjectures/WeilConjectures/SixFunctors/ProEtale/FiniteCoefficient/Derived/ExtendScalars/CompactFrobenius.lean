/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactWeilDatum
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.WeilDatum

/-!
# Derived scalar extension and the compact Frobenius

Let `S` be an algebra over a noetherian commutative ring `R` and write `Ψ = - ⊗ᴸ_R S` for the
derived extension of scalars of pro-étale sheaves. For a compactification `c` of `f : X ⟶ Y`
and endomorphisms `g : X ⟶ X`, `gZ : c.Z ⟶ c.Z` compatible with `c` over the identity of `Y`,
the comparison map `ξ : Ψ (Rf_!(c) K) ⟶ Rf_!(c) (Ψ K)`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationExtendScalarsMap`)
intertwines the scalar extension of the compact Frobenius of a Weil datum `φ : Lg^* K ⟶ K` with
the compact Frobenius of its scalar extension `φ_S : Lg^* Ψ K ≅ Ψ Lg^* K --Ψ φ--> Ψ K`
(`AlgebraicGeometry.ProEtale.extendScalarsWeilDatum`). This is the compatibility of compact
cohomology with the change of coefficients and the Frobenius maps of blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`.

## Main results

- `AlgebraicGeometry.ProEtale.lowerShriekWeilDatum_extendScalarsWeilDatum`: `ξ` is a morphism of
  Weil data.
- `AlgebraicGeometry.ProEtale.compactFrobenius_extendScalarsWeilDatum`: `ξ` intertwines the
  compact Frobenii.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) {g : X ⟶ X} {h : Y ⟶ Y}
  {gZ : c.Z ⟶ c.Z} {K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))}

/-- **Derived scalar extension commutes with the Weil data on `Rf_!(c)`**: the comparison map
`ξ : Ψ (Rf_!(c) K) ⟶ Rf_!(c) (Ψ K)` is a morphism from the scalar extension of the Weil datum
induced by `φ` on `Rf_!(c) K` to the Weil datum induced by `φ_S` on `Rf_!(c) (Ψ K)`, through
the commutation `Lh^* Ψ ≅ Ψ Lh^*`. -/
theorem lowerShriekWeilDatum_extendScalarsWeilDatum (hi : IsPullback g c.i c.i gZ)
    (hg : CommSq gZ c.g c.g h) (φ : L((g)^*[ModuleCat.{u + 1} R]).obj K ⟶ K) :
    (leftDerivedUpperStarExtendScalarsIso R S h).hom.app (Rf_!(c)[ModuleCat.{u + 1} R].obj K) ≫
        L(sheafExtendScalars (algebraMap R S) Y).map
          (lowerShriekWeilDatum (ModuleCat.{u + 1} R) c hi hg φ) ≫
        (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app K =
      L((h)^*[ModuleCat.{u + 1} S]).map
          ((rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app K) ≫
        lowerShriekWeilDatum (ModuleCat.{u + 1} S) c hi hg (extendScalarsWeilDatum (S := S) φ) := by
  have hξ : L(sheafExtendScalars (algebraMap R S) Y).map (Rf_!(c)[ModuleCat.{u + 1} R].map φ) ≫
      (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app K =
      (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app _ ≫
        Rf_!(c)[ModuleCat.{u + 1} S].map (L(sheafExtendScalars (algebraMap R S) X).map φ) :=
    (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).naturality φ
  have hEx := rightDerivedLowerShriekOfCompactificationBaseChange_extendScalars_app R S c c hi hg K
  simp only [lowerShriekWeilDatum, extendScalarsWeilDatum, Functor.map_comp, Category.assoc]
  rw [hξ]
  exact (reassoc_of% hEx) _

/-- **Derived scalar extension commutes with the compact Frobenius** (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`): the comparison map
`ξ : Ψ (Rf_!(c) K) ⟶ Rf_!(c) (Ψ K)` carries the scalar extension of the compact Frobenius of `φ` to
the compact Frobenius of its scalar extension `φ_S`, `Ψ (F_c(φ)) ≫ ξ = ξ ≫ F_c(φ_S)`. -/
theorem compactFrobenius_extendScalarsWeilDatum (hi : IsPullback g c.i c.i gZ)
    (hg : CommSq gZ c.g c.g (𝟙 Y)) (φ : L((g)^*[ModuleCat.{u + 1} R]).obj K ⟶ K) :
    L(sheafExtendScalars (algebraMap R S) Y).map
        (compactFrobenius (ModuleCat.{u + 1} R) c hi hg φ) ≫
        (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app K =
      (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app K ≫
        compactFrobenius (ModuleCat.{u + 1} S) c hi hg (extendScalarsWeilDatum (S := S) φ) := by
  have hW := lowerShriekWeilDatum_extendScalarsWeilDatum R S c hi hg φ
  have hι := leftDerivedUpperStarExtendScalarsIso_hom_app_id R S
    (Rf_!(c)[ModuleCat.{u + 1} R].obj K)
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).inv.naturality
    ((rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app K)
  dsimp at hn
  -- `ι_S⁻¹ ≫ α_𝟙 = Ψ ι_R⁻¹`
  have hι' : (leftDerivedUpperStarId (ModuleCat.{u + 1} S) Y).inv.app
        (L(sheafExtendScalars (algebraMap R S) Y).obj (Rf_!(c)[ModuleCat.{u + 1} R].obj K)) ≫
      (leftDerivedUpperStarExtendScalarsIso R S (𝟙 Y)).hom.app
        (Rf_!(c)[ModuleCat.{u + 1} R].obj K) =
      L(sheafExtendScalars (algebraMap R S) Y).map
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).inv.app
          (Rf_!(c)[ModuleCat.{u + 1} R].obj K)) := by
    rw [← cancel_mono (L(sheafExtendScalars (algebraMap R S) Y).map
      ((leftDerivedUpperStarId (ModuleCat.{u + 1} R) Y).hom.app
        (Rf_!(c)[ModuleCat.{u + 1} R].obj K))), Category.assoc, hι, ← Functor.map_comp,
      Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    exact (CategoryTheory.Functor.map_id L(sheafExtendScalars (algebraMap R S) Y) _).symm
  rw [compactFrobenius, compactFrobenius, Functor.map_comp, Category.assoc, reassoc_of% hn,
    ← hW]
  exact ((reassoc_of% hι') _).symm

end AlgebraicGeometry.ProEtale

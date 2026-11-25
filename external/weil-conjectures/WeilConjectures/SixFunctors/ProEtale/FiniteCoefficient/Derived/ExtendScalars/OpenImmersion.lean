/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.RestrictScalarsMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate

/-!
# Derived scalar extension commutes with extension by zero

Let `S` be an algebra over a noetherian commutative ring `R` and `j : U ⟶ X` an open immersion.
Derived scalar extension `Ψ = - ⊗ᴸ_R S` commutes with the exact extension by zero `j_!`:
`Ψ (j_! K) ≅ j_! (Ψ K)` (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`). The
isomorphism is the conjugate, along the adjunctions `Ψ ⊣ Res` and `j_! ⊣ Lj^*`, of the commutation
`Lj^* (Res K) ≅ Res (Lj^* K)` of restriction of scalars with the derived pullback; equivalently,
its mate along `j_! ⊣ Lj^*` is the commutation `Lj^* Ψ ≅ Ψ Lj^*` of `Ψ` with the derived pullback
(`AlgebraicGeometry.ProEtale.mateEquiv_openImmersionLowerShriekExtendScalarsIso_inv`).

## Main definitions

- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekExtendScalarsIso`: `Ψ (j_! K) ≅ j_! (Ψ K)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Derived scalar extension commutes with the extension by zero along an open immersion `j`:
`Ψ (j_! K) ≅ j_! (Ψ K)`, the conjugate along `Ψ ⊣ Res` and `j_! ⊣ Lj^*` of the commutation
`Lj^* (Res K) ≅ Res (Lj^* K)` (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso`)
of restriction of scalars with the derived pullback. -/
noncomputable def openImmersionLowerShriekExtendScalarsIso :
    D((j)_!open[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) X) ≅
      L(sheafExtendScalars (algebraMap R S) U) ⋙ D((j)_!open[ModuleCat.{u + 1} S]) :=
  (conjugateIsoEquiv
    ((leftDerivedSheafExtendScalarsAdjunction R S U).comp
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} S) j))
    ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} R) j).comp
      (leftDerivedSheafExtendScalarsAdjunction R S X))).symm
    (leftDerivedUpperStarRestrictScalarsIso (algebraMap R S) j).symm

/-- The mate of `Ψ (j_! K) ≅ j_! (Ψ K)` along the adjunctions `j_! ⊣ Lj^*` is the commutation
`Lj^* Ψ ≅ Ψ Lj^*` of derived scalar extension with the derived pullback
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`). -/
theorem mateEquiv_openImmersionLowerShriekExtendScalarsIso_inv :
    mateEquiv (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
        (ModuleCat.{u + 1} R) j)
      (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} S) j)
      (openImmersionLowerShriekExtendScalarsIso R S j).inv =
    (leftDerivedUpperStarExtendScalarsIso R S j).inv := by
  apply (mateEquiv (leftDerivedSheafExtendScalarsAdjunction R S X)
    (leftDerivedSheafExtendScalarsAdjunction R S U)).injective
  have h := iterated_mateEquiv_conjugateEquiv
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} R) j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} S) j)
    (leftDerivedSheafExtendScalarsAdjunction R S U) (leftDerivedSheafExtendScalarsAdjunction R S X)
    (openImmersionLowerShriekExtendScalarsIso R S j).inv
  rw [openImmersionLowerShriekExtendScalarsIso, conjugateIsoEquiv_symm_apply_inv,
    Equiv.apply_symm_apply] at h
  exact h.trans (mateEquiv_leftDerivedUpperStarExtendScalarsIso_inv R S j).symm

end OpenImmersion

end AlgebraicGeometry.ProEtale

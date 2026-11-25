/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekCompactificationBaseChange

/-!
# Derived scalar extension and compact-support base change

Let `S` be an algebra over a noetherian commutative ring `R` and write `Ψ = - ⊗ᴸ_R S` for the
derived extension of scalars of pro-étale sheaves. The compact-support exchange maps
`Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` along compatible compactifications
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChange`) with
coefficients `R` and `S` are compatible with `Ψ`, the commutations `Lg^* Ψ ≅ Ψ Lg^*` of `Ψ` with
the derived pullbacks and the comparison maps `Ψ Rf_!(c) ⟶ Rf_!(c) Ψ`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationExtendScalarsMap`). This
is an input for the compatibility of compact cohomology with the change of coefficients and the
Frobenius maps (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).

## Main results

- `leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_extendScalars_app`:
  the compatibility for the extension by zero along a cartesian square of open immersions.
- `rightDerivedLowerShriekOfCompactificationBaseChange_extendScalars_app`:
  the compatibility for the compact-support exchange maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]

section OpenImmersion

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

/-- **Derived scalar extension commutes with the base change of the extension by zero.** For a
cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions and `K` in
`D(U_proét, R)`, the two composites `L(g'')^* Ψ (j_! K) ⟶ j'_! Ψ (Lg'^* K)`
```
L(g'')^* Ψ j_! K ──ω_j──▶ L(g'')^* j_! Ψ K ──BC──▶ j'_! Lg'^* Ψ K ──α_{g'}──▶ j'_! Ψ Lg'^* K
L(g'')^* Ψ j_! K ──α_{g''}──▶ Ψ L(g'')^* j_! K ──Ψ(BC)──▶ Ψ j'_! Lg'^* K ──ω_{j'}──▶ j'_! Ψ Lg'^* K
```
agree, where `BC` is the base change isomorphism of the extension by zero
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso`), `ω`
the commutation of `Ψ` with the extension by zero
(`AlgebraicGeometry.ProEtale.openImmersionLowerShriekExtendScalarsIso`) and `α` the commutation
of `Ψ` with the derived pullbacks. This is an input for blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`. -/
theorem leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_extendScalars_app
    (hsq : IsPullback g' j' j g'')
    (K : DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))) :
    L((g'')^*[ModuleCat.{u + 1} S]).map
        ((openImmersionLowerShriekExtendScalarsIso R S j).hom.app K) ≫
      (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} S) hsq).hom.app
          (L(sheafExtendScalars (algebraMap R S) U).obj K) ≫
      D((j')_!open[ModuleCat.{u + 1} S]).map
        ((leftDerivedUpperStarExtendScalarsIso R S g').hom.app K) =
    (leftDerivedUpperStarExtendScalarsIso R S g'').hom.app
        (D((j)_!open[ModuleCat.{u + 1} R]).obj K) ≫
      L(sheafExtendScalars (algebraMap R S) Z').map
        ((leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} R)
          hsq).hom.app K) ≫
      (openImmersionLowerShriekExtendScalarsIso R S j').hom.app
        (L((g')^*[ModuleCat.{u + 1} R]).obj K) := by
  have hc := mateEquiv_app_cube_converse
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} R) j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} R) j')
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} S) j)
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat.{u + 1} S) j')
    (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} R) hsq).inv
    (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} S) hsq).inv
    (openImmersionLowerShriekExtendScalarsIso R S j).inv
    (openImmersionLowerShriekExtendScalarsIso R S j').inv
    (leftDerivedUpperStarExtendScalarsIso R S g').hom
    (leftDerivedUpperStarExtendScalarsIso R S g'').hom (fun M ↦ by
      rw [mateEquiv_leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_inv,
        mateEquiv_leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_inv,
        mateEquiv_openImmersionLowerShriekExtendScalarsIso_inv,
        mateEquiv_openImmersionLowerShriekExtendScalarsIso_inv]
      have h := leftDerivedUpperStarExtendScalarsIso_hom_app_square R S hsq.toCommSq M
      rw [← cancel_epi (L((g')^*[ModuleCat.{u + 1} S]).map
        ((leftDerivedUpperStarExtendScalarsIso R S j).hom.app M)),
        ← cancel_epi ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} S) hsq.toCommSq).hom.app
          (L(sheafExtendScalars (algebraMap R S) Z).obj M))]
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
        Category.id_comp, Iso.hom_inv_id_app_assoc]
      rw [reassoc_of% h.symm]
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
      exact Category.comp_id _) K
  rw [← cancel_mono ((openImmersionLowerShriekExtendScalarsIso R S j').inv.app _),
    ← cancel_mono (L(sheafExtendScalars (algebraMap R S) Z').map
      ((leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} R)
        hsq).inv.app K))]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  rw [hc]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp [← Functor.map_comp]

end OpenImmersion

section Compactification

variable {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} (c : Compactification f)
  (c' : Compactification f') {g : Y' ⟶ Y} {g' : X' ⟶ X} {gZ : c'.Z ⟶ c.Z}

/-- **Derived scalar extension commutes with the compact-support exchange maps.** For
compactifications `c` of `f` and `c'` of `f'` compatible with `g : Y' ⟶ Y`, `g' : X' ⟶ X` and
`gZ : c'.Z ⟶ c.Z` (the square `g' ≫ c.i = c'.i ≫ gZ` being cartesian and
`gZ ≫ c.g = c'.g ≫ g`), and `K` in `D(X_proét, R)`, the two composites
`Lg^* Ψ (Rf_!(c) K) ⟶ Rf'_!(c') Ψ (Lg'^* K)`
```
Lg^* Ψ Rf_!(c) K ──α_g──▶ Ψ Lg^* Rf_!(c) K ──Ψ(Ex_!)──▶ Ψ Rf'_!(c') Lg'^* K
  ──▶ Rf'_!(c') Ψ Lg'^* K
Lg^* Ψ Rf_!(c) K ──▶ Lg^* Rf_!(c) Ψ K ──Ex_!──▶ Rf'_!(c') Lg'^* Ψ K
  ──Rf'_!(c') α_{g'}──▶ Rf'_!(c') Ψ Lg'^* K
```
agree, where `Ex_!` is the compact-support exchange map
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChange`), the
unlabelled arrows are the comparison maps
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationExtendScalarsMap` and `α` is
the commutation of `Ψ` with the derived pullbacks. This is the input for the compatibility of
compact cohomology with the change of coefficients and the Frobenius maps (blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`). -/
theorem rightDerivedLowerShriekOfCompactificationBaseChange_extendScalars_app
    (hi : IsPullback g' c'.i c.i gZ) (hg : CommSq gZ c'.g c.g g)
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    (leftDerivedUpperStarExtendScalarsIso R S g).hom.app (Rf_!(c)[ModuleCat.{u + 1} R].obj K) ≫
        L(sheafExtendScalars (algebraMap R S) Y').map
          ((rightDerivedLowerShriekOfCompactificationBaseChange (ModuleCat.{u + 1} R) c c' hi
            hg).app K) ≫
        (rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c').app
          (L((g')^*[ModuleCat.{u + 1} R]).obj K) =
      L((g)^*[ModuleCat.{u + 1} S]).map
          ((rightDerivedLowerShriekOfCompactificationExtendScalarsMap R S c).app K) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChange (ModuleCat.{u + 1} S) c c' hi
          hg).app (L(sheafExtendScalars (algebraMap R S) X).obj K) ≫
        Rf_!(c')[ModuleCat.{u + 1} S].map
          ((leftDerivedUpperStarExtendScalarsIso R S g').hom.app K) := by
  have h₁ := derivedBaseChangeMap_extendScalars_app R S hg
    (D((c.i)_!open[ModuleCat.{u + 1} R]).obj K)
  have h₂ := congrArg R((c'.g)_*[ModuleCat.{u + 1} S]).map
    (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_extendScalars_app R S hi K)
  have h₃ := (rightDerivedLowerStarExtendScalarsMap R S c'.g).naturality
    ((leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} R) hi).hom.app
      K)
  have h₄ := (derivedBaseChangeMap (ModuleCat.{u + 1} S) hg).naturality
    ((openImmersionLowerShriekExtendScalarsIso R S c.i).hom.app K)
  simp only [Functor.map_comp] at h₂
  dsimp at h₃ h₄
  rw [rightDerivedLowerShriekOfCompactificationBaseChange_app,
    rightDerivedLowerShriekOfCompactificationBaseChange_app,
    rightDerivedLowerShriekOfCompactificationExtendScalarsMap_app,
    rightDerivedLowerShriekOfCompactificationExtendScalarsMap_app]
  simp only [rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₃, reassoc_of% h₁, reassoc_of% h₄]
  rw [h₂]

end Compactification

end AlgebraicGeometry.ProEtale

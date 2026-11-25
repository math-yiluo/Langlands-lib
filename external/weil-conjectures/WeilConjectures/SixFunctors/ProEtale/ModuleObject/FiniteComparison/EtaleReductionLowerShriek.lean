/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionClosedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar

/-!

# Reduction modulo `ℓⁿ` read on the étale site commutes with `Rd_!` for closed immersions

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`, `n : ℕ`, and write
`red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small étale
site (`AlgebraicGeometry.ProEtale.CondensedRing.etaleReduction`). This file constructs, for a
closed immersion `d : Z ⟶ Y` of separated `k`-schemes of finite type, an isomorphism
```
Rd_! ⋙ red_Y ≅ red_Z ⋙ Rd_!
```
by chaining the following isomorphisms, with `Rd_! ≅ Rd_*` on both sides (`d` is proper):

* `Rd_! ≅ Rd_*` on bounded constructible `𝒪_E`-complexes
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`);
* reduction modulo `ℓⁿ` commutes with `Rd_*` for a closed immersion
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarIntegersModPowReductionIso`);
* the inclusion of bounded constructible complexes commutes with `Rd_*`
  (`ProEtale.CondensedRing.IntegersModPowRingObj.boundedConstructibleLowerStarCompatibility`);
* the finite-coefficient comparison commutes with `Rd_*`
  (`ProEtale.finiteCoefficientDerivedLowerStarIso`);
* `Rν_*` commutes with `Rd_*` (`ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso`);
* étale `Rd_! ≅ Rd_*` (`Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`).

## Main definitions

* `ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`:
  `Rf_! ≅ Rf_*` on bounded constructible `𝒪_E`-complexes for a proper `f`.
* `ProEtale.CondensedRing.etaleReductionLowerStarIsoOfIsClosedImmersion`:
  `Rd_* ⋙ red_Y ≅ red_Z ⋙ Rd_*` for a closed immersion `d`.
* `ProEtale.CondensedRing.etaleReductionLowerShriekIsoOfIsClosedImmersion`:
  `Rd_! ⋙ red_Y ≅ red_Z ⋙ Rd_!` for a closed immersion `d`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The isomorphism `Rf_! ≅ Rf_*` on bounded constructible `𝒪_E`-sheaves for a proper `f`: by
independence of the compactification, `Rf_!` is `Rf_!^c` for the trivial compactification
`c = (X ⟶[𝟙] X ⟶[f] Y)`, which is `Rf_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekIsoLowerStar_padicIntegers (f : Z ⟶ Y)
    [IsProper f.left] :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ≅
      PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E f :=
  boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E
      (compactificationOverField f) (.ofIsProper f.left) ≪≫
    (Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso
      (Profinite.padicIntegersRingObj ℓ E) ℓ f) _ ≪≫ Functor.leftUnitor _)

/-- **Reduction modulo `ℓⁿ`, read on the étale site, commutes with `Rd_*` for a closed
immersion `d`**: `Rd_* ⋙ red_Y ≅ red_Z ⋙ Rd_*`, where `red = etaleReduction`. It chains the
commutation of `Rd_*` with the condensed reduction
(`boundedConstructibleLowerStarIntegersModPowReductionIso`), with the inclusion of bounded
constructible complexes, with the finite-coefficient comparison
(`ProEtale.finiteCoefficientDerivedLowerStarIso`) and with `Rν_*`
(`ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso`). -/
@[no_expose]
noncomputable def etaleReductionLowerStarIsoOfIsClosedImmersion (d : Z ⟶ Y)
    [IsClosedImmersion d.left] :
    PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E d ⋙
        etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n Z ⋙
        R(Etale.lowerStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) d.left) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleLowerStarIntegersModPowReductionIso ℓ E n d) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (IntegersModPowRingObj.boundedConstructibleLowerStarCompatibility ℓ E n d) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              (finiteCoefficientDerivedLowerStarIso (PadicAlgCl.integersModPow ℓ E n)
                d.left).symm _ ≪≫
            Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _
              (rightDerivedLowerStarCompComparisonLowerStarIso
                (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) d.left) ≪≫
            (Functor.associator _ _ _).symm) ≪≫
        (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- **Reduction modulo `ℓⁿ`, read on the étale site, commutes with `Rd_!` for a closed
immersion `d`**: `Rd_! ⋙ red_Y ≅ red_Z ⋙ Rd_!`, where `red = etaleReduction`. Both lower
shrieks are identified with `Rd_*` (`d` is proper:
`boundedConstructibleLowerShriekIsoLowerStar_padicIntegers` and
`Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), and
`etaleReductionLowerStarIsoOfIsClosedImmersion` identifies `Rd_* ⋙ red_Y` with `red_Z ⋙ Rd_*`. -/
@[no_expose]
noncomputable def etaleReductionLowerShriekIsoOfIsClosedImmersion (d : Z ⟶ Y)
    [IsClosedImmersion d.left] :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E d ⋙
        etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n Z ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          d.left :=
  Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E d) _ ≪≫
    etaleReductionLowerStarIsoOfIsClosedImmersion ℓ E n d ≪≫
    Functor.isoWhiskerLeft _
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) d.left).symm

end AlgebraicGeometry.ProEtale.CondensedRing

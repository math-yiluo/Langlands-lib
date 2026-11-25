/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizingUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriekCanonical

/-!
# The reduction of the integral dualizing complex

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). This file proves that `red_X` carries the
integral dualizing complex `ω_{X, 𝒪_E} = Ra_X^! 𝒪_E` to the étale dualizing complex
`ω_X = Ra_X^! (𝒪_E ⧸ ℓⁿ)` (blueprint `theorem-verdier-biduality`, proof of (ii), from the
coefficient comparison for `f^!` of blueprint
`lemma-change-coefficients-exceptional-inverse-image`).

The reduction commutes canonically with `Ra_X^!` (`etaleReductionUpperShriekIso`, assembled from
a compactification of `a_X` as an open immersion followed by a proper morphism), and it sends
the unit `𝒪_E` to the unit (`etaleReductionUnitIso`).

## Main definitions

- `ProEtale.CondensedRing.etaleReductionDualizingComplexIso`:
  `red_X ω_{X, 𝒪_E} ≅ ω_X`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- Reduction modulo `ℓⁿ` commutes with the exceptional inverse image along a proper `p`, in the
form `Rp^! = (Rp_*)^ʳ` (the chosen right adjoint of the pushforward, which enters
`PadicIntegersRingObj.boundedConstructibleUpperShriekOfCompactification`): it is the
right adjoint of `Rp_! ≅ Rp_*` (`boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`), and
the transpose of the canonical comparison `etaleReductionLowerShriekIso` is invertible
(`isIso_mateEquiv_etaleReductionLowerShriekIso`). -/
noncomputable def etaleReductionProperUpperShriekIso {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    haveI := HasCompactification.of_over p
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p).rightAdjoint ⋙
        etaleReduction ℓ E n Z ≅
      etaleReduction ℓ E n Y ⋙
        Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) p.left :=
  haveI := HasCompactification.of_over p
  haveI := isIso_mateEquiv_etaleReductionLowerShriekIso ℓ E n p
  Functor.isoWhiskerRight ((Adjunction.ofIsLeftAdjoint _).rightAdjointUniq
    ((PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E p).ofNatIsoLeft
      (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p))) _ ≪≫
    asIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E p)
      (Etale.rightDerivedUpperShriekAdjunction _ p.left)
      (TwoSquare.mk _ _ _ _ (etaleReductionLowerShriekIso ℓ E n p).inv))

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **The reduction of the integral dualizing complex is the étale dualizing complex**:
`red_X (Ra_X^! 𝒪_E) ≅ Ra_X^! (𝒪_E ⧸ ℓⁿ)` (blueprint
`lemma-change-coefficients-exceptional-inverse-image` for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site,
at the unit): the canonical commutation of the reduction with `Ra_X^!`
(`etaleReductionUpperShriekIso`) at the unit, followed by `Ra_X^!` of the reduction of the unit
(`etaleReductionUnitIso`). -/
noncomputable def etaleReductionDualizingComplexIso :
    (etaleReduction ℓ E n X).obj (PadicIntegersRingObj.dualizingComplex ℓ E X) ≅
      Etale.dualizingComplex (integersModPowCoeff.{u} ℓ E n) X.hom :=
  haveI := HasCompactification.of_over (Over.mkIdTerminal.from X)
  (etaleReductionUpperShriekIso ℓ E n (Over.mkIdTerminal.from X)).app (𝟙_ _) ≪≫
    (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n)
      (Over.mkIdTerminal.from X).left).mapIso (etaleReductionUnitIso ℓ E n _) ≪≫
    eqToIso (by
      rw [Etale.dualizingComplex]
      congr 2
      exact Over.mkIdTerminal_from_left X)

end AlgebraicGeometry.ProEtale.CondensedRing

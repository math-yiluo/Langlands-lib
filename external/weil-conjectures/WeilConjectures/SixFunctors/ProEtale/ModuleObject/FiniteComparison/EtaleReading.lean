/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateOfNatIsoLeft
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar

/-!
# The étale reading of `𝒪_E ⧸ ℓⁿ`-coefficients

Write `ρ_X : Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)`, `M ↦ Rν_* Φ(M)`, for the *étale reading* of
bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes
(`ProEtale.CondensedRing.finiteEtaleReading`), and, for a proper `p`, the finite-coefficient
comparison for `p^!` (`ProEtale.CondensedRing.HasEtaleReadingUpperShriekComparison`): `Rp_*` on
`Dᵇc(-)⟦𝒪_E ⧸ ℓⁿ⟧` has a right adjoint read by `ρ` as the étale `Rp^!`.

No integral coefficients are involved, so this file does not depend on the exceptional inverse
image with `𝒪_E`-coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- The finite coefficient ring `𝒪_E ⧸ ℓⁿ`, lifted to the universe of étale sheaves of
modules. -/
abbrev integersModPowCoeff : Type (u + 1) :=
  ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n)

/-- **The étale reading of bounded constructible `𝒪_E ⧸ ℓⁿ`-complexes**: `M ↦ Rν_* Φ(M)`, from
bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes on `X_proét` to the derived category of
étale sheaves of `𝒪_E ⧸ ℓⁿ`-modules on `X`. The étale reduction `etaleReduction` is the
condensed reduction followed by it. -/
noncomputable def finiteEtaleReading (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤
      DerivedCategory (Sheaf Y.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :=
  (boundedConstructible _).ι ⋙
    (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
      R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The finite-coefficient comparison for `p^!`** (proper `p`): the pushforward `Rp_*` on
bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes has a right adjoint `H'`, and there is an
isomorphism `Rp_* ⋙ ρ_Y ≅ ρ_X ⋙ Rp_!` (`ρ = finiteEtaleReading`, `Rp_!` étale) whose transpose
`H' ⋙ ρ_X ⟶ ρ_Y ⋙ Rp^!` under `Rp_* ⊣ H'` and the étale `Rp_! ⊣ Rp^!` is an isomorphism. -/
def HasEtaleReadingUpperShriekComparison (p : X ⟶ Y) : Prop :=
  have := HasCompactification.of_over p
  ∃ (H' : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤
      Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧)
    (adjH' : IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p ⊣ H')
    (γ : IntegersModPowRingObj.boundedConstructibleLowerStar ℓ E n p ⋙
        finiteEtaleReading ℓ E n Y ≅
      finiteEtaleReading ℓ E n X ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left),
    IsIso (mateEquiv adjH' (Etale.rightDerivedUpperShriekAdjunction _ p.left)
      (TwoSquare.mk _ _ _ _ γ.inv))

end AlgebraicGeometry.ProEtale.CondensedRing

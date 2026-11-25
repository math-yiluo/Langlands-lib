/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction

/-!
# The pullback comparison of the étale reduction factors through the étale reading

The étale reduction `etaleReduction = R ⋙ ρ` is the condensed reduction modulo `ℓⁿ`
(`ProEtale.boundedConstructibleIntegersModPowReduction`) followed by the étale reading
`ρ = ProEtale.CondensedRing.finiteEtaleReading`. Its canonical pullback comparison
`ProEtale.CondensedRing.etaleReductionUpperStarIso` is the condensed comparison
(`ProEtale.CondensedRing.boundedConstructibleUpperStarIntegersModPowReductionIso`) read by `ρ`,
followed by the pullback comparison of `ρ`
(`ProEtale.CondensedRing.finiteEtaleReadingUpperStarIso`)
(`ProEtale.CondensedRing.etaleReductionUpperStarIso_eq`).
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

section EtaleReduction

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The pullback comparison of the étale reduction factors through the étale reading**: on
`K`, the canonical isomorphism `etaleReductionUpperStarIso` is `ρ_Z` of the condensed comparison
`(f^* K)_{𝒪_E ⧸ ℓⁿ} ≅ f^* (K_{𝒪_E ⧸ ℓⁿ})` followed by the pullback comparison of `ρ` at
`K_{𝒪_E ⧸ ℓⁿ}`. -/
lemma etaleReductionUpperStarIso_hom_app (f : Z ⟶ Y)
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (etaleReductionUpperStarIso ℓ E n f).hom.app K =
      (finiteEtaleReading ℓ E n Z).map
          ((boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f).hom.app K) ≫
        (finiteEtaleReadingUpperStarIso ℓ E n f).hom.app
          ((boundedConstructibleIntegersModPowReduction Y.left ℓ E n).obj K) := by
  simp [etaleReductionUpperStarIso, finiteEtaleReadingUpperStarIso, finiteEtaleReading]

/-- **The pullback comparison of the étale reduction factors through the étale reading**:
`etaleReductionUpperStarIso` is the condensed comparison
`boundedConstructibleUpperStarIntegersModPowReductionIso`, read by `ρ_Z`, followed by the pullback
comparison `finiteEtaleReadingUpperStarIso` of `ρ`. -/
theorem etaleReductionUpperStarIso_eq (f : Z ⟶ Y) :
    etaleReductionUpperStarIso ℓ E n f =
      Functor.isoWhiskerRight (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E n f)
          (finiteEtaleReading ℓ E n Z) ≪≫
        Functor.isoWhiskerLeft (boundedConstructibleIntegersModPowReduction Y.left ℓ E n)
          (finiteEtaleReadingUpperStarIso ℓ E n f) := by
  ext K
  exact etaleReductionUpperStarIso_hom_app ℓ E n f K

end EtaleReduction

end AlgebraicGeometry.ProEtale.CondensedRing

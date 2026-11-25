/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterion

/-!
# The integral constructibility criterion with condensed residue coefficients

A variant of blueprint `proposition-integral-constructibility-criterion`, (2) ⇒ (1)
(`ProEtale.boundedConstructible_of_derivedCompleteIntegers`), with the hypothesis on the
reduction stated for the condensed coefficient ring `𝔽_{E,X}`: on a noetherian scheme `X`, a
derived complete complex `K` of `𝒪_{E,X}`-modules whose derived extension of scalars
`𝔽_{E,X} ⊗ᴸ K` is a bounded constructible complex of `𝔽_{E,X}`-modules is bounded constructible
(`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_residueField`). This is the form
in which the reduction of nearby cycles is controlled by the finiteness theorem with
finite coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

private lemma lt_or_lt_of_lt_sub_toNat_or_lt' {i a b : ℤ}
    (h : i < b - (b - a).toNat ∨ b < i) : i < a ∨ b < i := by
  omega

/-- **The integral criterion with condensed residue coefficients** (blueprint
`proposition-integral-constructibility-criterion`, (2) ⇒ (1); Bhatt–Scholze, Proposition 6.8.11): on
a noetherian scheme `X`, a derived complete complex `K` of `𝒪_{E,X}`-modules whose derived extension
of scalars `𝔽_{E,X} ⊗ᴸ K` is bounded constructible is bounded constructible. -/
theorem boundedConstructible_of_derivedCompleteIntegers_of_residueField {X : Scheme.{u}}
    [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : derivedCompleteIntegers ℓ E X K)
    (h₁ : boundedConstructible (residueFieldRingObj X ℓ E)
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K)) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K := by
  have h₁' := boundedConstructible_comap_padicIntegersToResidueField h₁
  obtain ⟨⟨a, b, hab⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 h₁'
  exact boundedConstructible_of_derivedCompleteIntegers_of_amplitude (b - a).toNat K b hK h₁'
    fun i hi ↦ hab i (lt_or_lt_of_lt_sub_toNat_or_lt' hi)

end AlgebraicGeometry.ProEtale

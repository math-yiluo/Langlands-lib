/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdicCompleteHomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleDerivedAdicComplete
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CountableProducts

/-!

# Bounded constructible integral complexes are derived complete

On a noetherian scheme `X`, a bounded constructible complex of `𝒪_{E,X}`-modules is derived
`ℓ`-adically complete (`ProEtale.isDerivedAdicComplete_of_boundedConstructible`): the derived
limit of the tower `⋯ --ℓ--> K --ℓ--> K` vanishes (`CategoryTheory.IsDerivedAdicComplete`). This
is the completeness half of the implication (1) ⇒ (2) of blueprint
`proposition-integral-constructibility-criterion` (section `chap-The-pro-etale-site`); the other
half, that the first derived reduction is bounded constructible, is
`ProEtale.boundedConstructible_derivedReduction_obj`.

A complex is derived complete if and only if its cohomology objects are
(`DerivedCategory.isDerivedAdicComplete_iff_homology`, countable products of module objects being
exact), and constructible module objects are derived complete
(`ProEtale.isDerivedAdicComplete_of_isConstructibleModuleObject`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- **Bounded constructible integral complexes are derived complete** (blueprint
`proposition-integral-constructibility-criterion`, section `chap-The-pro-etale-site`, implication
(1) ⇒ (2), the completeness of `K`): on a noetherian scheme `X`, a bounded constructible complex `K`
of `𝒪_{E,X}`-modules is derived complete. Completeness is stated here for `ℓ ∈ 𝔪_E`, as the
vanishing of `R lim (⋯ --ℓ--> K --ℓ--> K)` (`CategoryTheory.IsDerivedAdicComplete`); since
`𝔪_E^e ⊆ (ℓ) ⊆ 𝔪_E`, this is equivalent to completeness for `𝔪_E` (Stacks, Tags 091N, 091Q). -/
theorem isDerivedAdicComplete_of_boundedConstructible [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    IsDerivedAdicComplete (ℓ : ℤ) K :=
  (DerivedCategory.isDerivedAdicComplete_iff_homology K).2 fun p ↦
    isDerivedAdicComplete_of_isConstructibleModuleObject ℓ E _ (hK.2 p)

end AlgebraicGeometry.ProEtale

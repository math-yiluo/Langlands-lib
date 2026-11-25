/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators

/-! Constructibility of a single integral locally closed extension in the topological
Noetherian setting. Source: Bhatt--Scholze, Lemma 6.8.13, and step 1 of the plan of
lem-sfb-topological-integral-generators
(blueprint: lem-sfb-topological-integral-extension-constructibility).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.SixFunctors

/-- The integral extension by zero `i_* j_! L₀` of a locally finite free `O_E`-module is
constant-model constructible on a topologically Noetherian scheme.

Source: step 1 of the plan of lem-sfb-topological-integral-generators; definition
definition-constructible-sheaves (blueprint:
lem-sfb-topological-integral-extension-constructibility).

Proof:
1. `X` is topologically Noetherian, so it is quasi-compact and quasi-separated and every
   open (in particular `X ∖ Z` and `Z ∖ T`) is quasi-compact
   (lem-sfb-noetherian-space-compact-subsets); the constructibility condition is the
   finite-stratification one.
2. Stratify `X` by `T`, `Z ∖ T` and `X ∖ Z`. By lem-sfb-topological-locally-closed-extension
   the restrictions of `i_* j_! L₀` to these strata are `L₀`, `0` and `0`.
3. `L₀` is pro-étale locally `O_E^r`, the pullback of the finitely presented condensed
   module `O_E^r` on the point, and `0` is the pullback of `0`; so every stratum has finite
   constant local models (definition-constructible-sheaves--1), and `i_* j_! L₀` is
   constructible. -/
theorem topological_integral_extension_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (T Z : Scheme.{u}) (j : T ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (L₀ : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (integralCoefficientObject T ℓ E))
    (hL₀ : CondensedRing.LocallyFree (integralCoefficientObject T ℓ E) L₀) :
    IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
      (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) j i L₀) := by
  sorry

end WeilConjectures.SixFunctors

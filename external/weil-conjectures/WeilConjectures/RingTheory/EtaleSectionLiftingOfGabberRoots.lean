/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.RingTheory.GabberIntegralSectionFactor
import WeilConjectures.RingTheory.ZariskiPairFlatIntegralIsomorphism

/-!
# Étale section lifting from Gabber's root condition

Source: Stacks Project, More on Algebra, Lemma Tag 09XI, implication (5) ⇒ (2)
(blueprint: lem-weil-pbc-gabber-root-criterion-etale-section-lifting).
-/

@[expose] public section

universe u v

open Polynomial
open scoped BigOperators

namespace Algebra

/-- Gabber's root condition for an ideal in the Jacobson radical implies that every
section of an étale algebra modulo that ideal lifts to an algebra section.
Source: Stacks Project, More on Algebra, Lemma Tag 09XI, implication (5) ⇒ (2)
(blueprint: lem-weil-pbc-gabber-root-criterion-etale-section-lifting).

Proof (the nine steps of the DAG node):
1. The section factors through `B/IB`. By `lem-weil-pbc-etale-ring-base-change` and
`lem-weil-pbc-etale-section-idempotent-splitting`, its associated idempotent `ε` gives
`B/IB ≅ A/I × C`, with the section the first projection.
2. Let `B'` be the integral closure of `A` in `B`. Finite presentation follows from
`lem-weil-pbc-etale-algebra-finite-presentation-localization`. Apply
`lem-weil-pbc-integral-closure-finite-fibre-part-localization` to obtain an idempotent
`ε'` modulo `IB'` mapping to `ε` and a lift `b` with `B'_b ≅ B_b`.
3. Choose a finite subalgebra `B''` containing `b`, the numerators of generators of `B'_b`,
and the finitely many elements expressing `b²-b` in `IB'`. Finiteness follows from
`lem-weil-pbc-finite-of-integral-generators`. Then `B''_b ≅ B'_b`, the image of `b` is
idempotent modulo `IB''`, and its first factor is `A/I`.
4. Apply `lem-weil-pbc-zariski-pair-finite-gabber-polynomial` to find `n ≥ 1` and a
polynomial `f = X^n(X-1) + ∑ aⱼ X^j`, with all `aⱼ ∈ I`, annihilating `b`.
5. The root hypothesis supplies `α` with `α-1 ∈ I`. The Jacobson condition makes `α`
a unit. Write `f = (X-α)g`; reduction gives `g mod I = X^n`, so `g(α)` is a unit.
The polynomial `E = g(α)⁻¹ g` satisfies `E²-E ∈ (f)` and `(X-α)E ∈ (f)`.
Thus `e = E(b)` is idempotent in `B'` and `be = αe`.
6. Modulo `I`, `E = X^n`, so `e` maps to `ε'^n = ε'`, since `n ≥ 1`.
Consequently its image in `B/IB` is `ε`.
7. On the `e` factor, `b = α` is invertible. Therefore `B'_e ≅ B_e` follows from
`B'_b ≅ B_b`. Since localization at an idempotent is a quotient, `B'_e`, and hence
`B_e`, is integral over `A`.
8. The map `A → B_e` is étale by
`lem-weil-pbc-etale-algebra-finite-presentation-localization`, flat by
`lem-weil-pbc-etale-algebra-flat`, and integral by step 7. Its reduction modulo `I`
is the identity of `A/I`. By `lem-weil-pbc-zariski-pair-flat-integral-isomorphism`,
it is an isomorphism.
9. Compose `B → B_e` with the inverse of this isomorphism. Its reduction agrees
with the original section, since both maps agree on the image of `A → B_e`,
which is surjective. This yields the required `τ`. -/
theorem exists_etale_section_lift_of_gabber_roots
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (hroots : ∀ (n : ℕ), 1 ≤ n → ∀ (a : Fin (n + 1) → A),
      (∀ j, a j ∈ I) → ∀ (f : A[X]), f.Monic →
        f = X ^ n * (X - 1) + ∑ j : Fin (n + 1), C (a j) * X ^ (j : ℕ) →
          ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α)
    (B : Type v) [CommRing B] [Algebra A B] [Etale A B] (σ : B →ₐ[A] A ⧸ I) :
    ∃ τ : B →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ := by
  classical
  obtain ⟨e, _he, hint, hquot, ρ, hρ⟩ :=
    exists_gabber_integral_section_factor A I hI hroots B σ
  have hbij : Function.Bijective (algebraMap A (Localization.Away e)) :=
    RingHom.zariskiPair_flat_integral_finitePresentation_isIso
      (algebraMap A (Localization.Away e)) I (by simpa only [Ideal.jacobson_bot] using hI)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hint
      (RingHom.finitePresentation_algebraMap.mpr inferInstance) hquot
  let Φ : A ≃ₐ[A] Localization.Away e := AlgEquiv.ofBijective (Algebra.ofId A _) hbij
  let τ : B →ₐ[A] A := Φ.symm.toAlgHom.comp (IsScalarTower.toAlgHom A B _)
  refine ⟨τ, ?_⟩
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.mkₐ A I (Φ.symm (algebraMap B (Localization.Away e) x)) = σ x
  rw [← hρ x]
  calc
    _ = ρ (algebraMap A (Localization.Away e)
        (Φ.symm (algebraMap B (Localization.Away e) x))) := (ρ.commutes _).symm
    _ = ρ (algebraMap B (Localization.Away e) x) :=
      congrArg ρ (Φ.apply_symm_apply _)

end Algebra

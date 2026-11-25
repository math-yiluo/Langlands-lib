/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Sections of algebras cut out by idempotents

Let `S` be an `R`-algebra with an `R`-algebra section `s : S →ₐ[R] R`.

- `AlgHom.exists_awayAlgEquiv_of_isIdempotentElem`: if `e ∈ S` is an idempotent with
  `ker s = (1 - e)`, then `S[1/e] ≅ R` as `R`-algebras, by `x / 1 ↦ s x`.
-/

@[expose] public section

namespace AlgHom

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Let `s : S →ₐ[R] R` be a section of an `R`-algebra `S` and `e ∈ S` an idempotent with
`ker s = (1 - e)` (which forces `s e = 1`). Then `s` induces an `R`-algebra isomorphism
`S[1/e] ≅ R` sending `x / 1` to `s x`.
(blueprint: `lem-weil-pbc-etale-section-localization`) -/
theorem exists_awayAlgEquiv_of_isIdempotentElem (s : S →ₐ[R] R) {e : S}
    (he : IsIdempotentElem e) (hker : RingHom.ker s = Ideal.span {1 - e}) :
    ∃ φ : Localization.Away e ≃ₐ[R] R, ∀ x : S, φ (algebraMap S _ x) = s x := by
  let : Algebra S R := s.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap S R) := fun r ↦
    ⟨algebraMap R S r, s.commutes r⟩
  have : IsLocalization.Away e R :=
    IsLocalization.away_of_isIdempotentElem he hker hsurj
  let ψ : Localization.Away e ≃+* R :=
    (IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e) R).toRingEquiv
  have hψ : ∀ x : S, ψ (algebraMap S _ x) = s x := fun x ↦
    (IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e) R).commutes x
  refine ⟨{ ψ with commutes' := fun r ↦ ?_ }, hψ⟩
  change ψ (algebraMap R (Localization.Away e) r) = algebraMap R R r
  rw [IsScalarTower.algebraMap_apply R S (Localization.Away e), hψ, s.commutes]

end AlgHom

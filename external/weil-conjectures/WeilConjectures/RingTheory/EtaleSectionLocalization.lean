/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localization of an idempotent section

Source: Stacks Project, Tag 00EH (blueprint: lem-weil-pbc-etale-section-localization).
-/

@[expose] public section

universe u v

namespace Algebra.Etale

/-- Localization identification induced by a section and an idempotent kernel.
Source: Stacks Project, Tag 00U8 and Tag 00EH.
(blueprint: lem-weil-pbc-etale-section-localization)

Proof: Give R its S-algebra structure through s. Since s(e)=1, each r is the
image of e*algebraMap R S r, so this algebra map is surjective. Its kernel is
(1-e), and e is idempotent. The Mathlib criterion
IsLocalization.away_of_isIdempotentElem therefore makes R a localization of S
away from e. Uniqueness of localization gives an S-algebra equivalence from
Localization.Away e to R, which sends the image of x to s(x). Its underlying
ring equivalence is an R-algebra equivalence: on an R-scalar r, the scalar-tower
formula expresses its image as the image of algebraMap R S r, and s sends that
element to r. This proves both the equivalence and the required extension formula.
-/
theorem exists_localization_equiv_of_idempotent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (s : S →ₐ[R] R) (e : S) (he : IsIdempotentElem e) (hse : s e = 1)
    (hker : RingHom.ker s.toRingHom = Ideal.span {1 - e}) :
    ∃ ψ : Localization.Away e ≃ₐ[R] R,
      ∀ x : S, ψ (algebraMap S (Localization.Away e) x) = s x := by
  let : Algebra S R := s.toRingHom.toAlgebra
  have hs : Function.Surjective (algebraMap S R) :=
    fun r ↦ ⟨e * algebraMap R S r, by
      change s (e * algebraMap R S r) = r
      simp [hse]⟩
  let : IsLocalization.Away e R := IsLocalization.away_of_isIdempotentElem he hker hs
  let φ := IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e) R
  have hφ (x : S) : φ (algebraMap S (Localization.Away e) x) = s x :=
    φ.commutes x
  let ψ : Localization.Away e ≃ₐ[R] R := AlgEquiv.ofRingEquiv (f := φ.toRingEquiv)
    (fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R S (Localization.Away e)]
      exact (hφ (algebraMap R S r)).trans (s.commutes r))
  exact ⟨ψ, hφ⟩

end Algebra.Etale

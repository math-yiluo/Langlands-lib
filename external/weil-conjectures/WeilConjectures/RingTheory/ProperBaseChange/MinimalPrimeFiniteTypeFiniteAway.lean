/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import WeilConjectures.RingTheory.ProperBaseChange.MinimalPrimeFiniteTypeFiniteAwayAux

/-!
# Finiteness near a minimal prime

Source: Stacks Project, Algebra, Tag 02ML, `lemma-generically-finite`
(blueprint: lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A finite-type ring map with only finitely many primes over a minimal prime becomes
finite after inverting one element outside that prime.

Source: Stacks Project, Algebra, Tag 02ML, `lemma-generically-finite`
(blueprint: lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away).

Proof:
1. Choose algebra generators x₁, ..., xₙ of S over R. The fibre-prime bijection
   (lem-weil-pbc-fibre-ring-primes-bijection) makes the spectrum of the fibre algebra
   A = κ(p) ⊗[R] S finite. The images of the xᵢ generate A over κ(p), by expanding pure
   tensors as polynomials. The finite-spectrum lemma
   (pqf-lem-finite-type-algebra-finite-spectrum) makes A finite-dimensional, even if A = 0.
2. Identify A with Sₚ/pSₚ using lem-weil-pbc-fibre-ring-localization-quotient and
   def-weil-pbc-localization-at-prime. Linear dependence of powers of each generator
   gives a monic annihilating polynomial over κ(p), of positive degree. For A = 0 use X.
   Lift its nonleading coefficients to Rₚ, preserving leading coefficient 1, to get Pᵢ
   with Pᵢ(xᵢ) ∈ pSₚ.
3. Minimality of p makes pRₚ locally nilpotent
   (lem-weil-pbc-minimal-prime-reduced-localization-field), without assuming R reduced.
   Its extension pSₚ is locally nilpotent by lem-weil-pbc-locally-nilpotent-extension.
   Hence Pᵢ(xᵢ)^eᵢ = 0 for some eᵢ ≥ 1.
4. Take g₁ to be the product of the finitely many denominators of the coefficients
   of the Pᵢ. It lies outside p and makes all these coefficients elements of R[g₁⁻¹].
   The localization fraction equality criterion supplies uᵢ outside p annihilating
   each resulting Pᵢ(xᵢ)^eᵢ in S[φ(g₁)⁻¹].
5. Put g₂ = ∏ᵢ uᵢ and g = g₁g₂. Primality gives g ∉ p. Every factor of g is invertible
   in R[g⁻¹], and its image is invertible in S[φ(g)⁻¹]. Thus Qᵢ = Pᵢ^eᵢ is monic of
   positive degree Dᵢ and annihilates xᵢ in S[φ(g)⁻¹].
6. The xᵢ still generate the localized algebra. Repeated reduction by the Qᵢ expresses
   every monomial in their R[g⁻¹]-span with exponents 0 ≤ aᵢ < Dᵢ. These finitely many
   monomials span S[φ(g)⁻¹] as a module. For n = 0 use the empty monomial 1; empty
   denominator products are 1. All localizations use def-weil-ring-localization-away.
-/
theorem exists_finite_awayMap_of_finite_fiber_minimalPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.FiniteType) (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (hfinite : {q : PrimeSpectrum S | Ideal.comap φ q.asIdeal = p}.Finite) :
    ∃ g : R, g ∉ p ∧ (Localization.awayMap φ g).Finite := by
  obtain ⟨g, hg, n, b, hb⟩ :=
    exists_finite_span_awayMap_of_finite_fiber_minimalPrime φ hφ p hp hfinite
  refine ⟨g, hg, ?_⟩
  let _ : Algebra (Localization.Away g) (Localization.Away (φ g)) :=
    (Localization.awayMap φ g).toAlgebra
  change Module.Finite (Localization.Away g) (Localization.Away (φ g))
  exact ⟨Submodule.fg_iff_exists_fin_generating_family.mpr ⟨n, b, hb⟩⟩

end RingHom

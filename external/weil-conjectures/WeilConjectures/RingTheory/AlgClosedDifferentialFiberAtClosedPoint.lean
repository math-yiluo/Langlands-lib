/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import WeilConjectures.RingTheory.AlgClosedPrimeOver
import WeilConjectures.RingTheory.AlgClosedDifferentialFiberFinrank

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

set_option linter.unusedVariables false in
/-- A prime has a closed point above it after an algebraically closed scalar extension,
with the same differential-fibre dimension. No smoothness or dimension bound is assumed.
Source: Stacks Project, Algebra, proof of Tag 00TT, the construction of the maximal ideal
and the differential base change of Tag 00RV.
(blueprint: new-algclosed-differential-fiber-at-closed-point).

Proof: Set κ = κ(q) and let K be its algebraic closure, regarded as a k-algebra through
k → S → κ → K. The tensor-product universal property gives the K-algebra map
φ : K ⊗[k] S → K with φ(λ ⊗ s) = λ ψ(s̄), where ψ : κ → K is the field embedding.
It is surjective, since φ(λ ⊗ 1) = λ, so its kernel is maximal. Injectivity of ψ and
ker(S → κ) = q show that this kernel contracts to q. Its residue field is K as a
K-algebra: the quotient is K and localizing this field changes nothing. Differential
base change identifies Ω[(K ⊗[k] S)/K] with (K ⊗[k] S) ⊗[S] Ω[S/k]. Tensoring this
isomorphism with the residue field gives K ⊗[S] Ω[S/k]. Tensor associativity identifies
this with K ⊗[κ] (κ ⊗[S] Ω[S/k]). A basis of the latter κ-vector space extends to a
basis over K, so its finrank is unchanged. These identifications prove the equality.
The witness K lives in Type (max u v), since κ does. -/
theorem exists_algClosed_prime_over_finrank_differentials_eq
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S] [FiniteType k S]
    (q : PrimeSpectrum S) :
    ∃ (K : Type (max u v)) (hK : Field K) (hAk : Algebra k K) (hCK : IsAlgClosed K)
      (qK : PrimeSpectrum (K ⊗[k] S)),
      qK.asIdeal.IsMaximal ∧
        PrimeSpectrum.comap
          (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK = q ∧
        Module.finrank qK.asIdeal.ResidueField
          (qK.asIdeal.ResidueField ⊗[K ⊗[k] S] KaehlerDifferential K (K ⊗[k] S)) =
          Module.finrank q.asIdeal.ResidueField
            (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) := by
  obtain ⟨K, _hK, _hAk, _hCK, qK, hmax, hq⟩ := exists_algClosed_prime_over (k := k) q
  exact ⟨K, _hK, _hAk, _hCK, qK, hmax, hq,
    algClosed_prime_over_finrank_differentials_eq (k := k) (S := S) q K _hK _hAk _hCK qK
      hmax hq⟩

end Algebra

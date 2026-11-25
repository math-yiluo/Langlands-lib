/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.FiniteAfterCompletion
import WeilConjectures.RingTheory.CompletionFiniteExtensionDecomposition
import WeilConjectures.RingTheory.CompletionFiniteExtensionTensor
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Completion of a finite algebra over a prime

Source: Stacks Project, Algebra, Lemma 10.97.8 (Tag 07N9)
(blueprint: lem-weil-pbc-completion-finite-extension).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace AdicCompletion

/-- Completion of a finite algebra decomposes over the primes above a prime of the base.
Source: Stacks Project, Algebra, Lemma 10.97.8 (Tag 07N9)
(blueprint: lem-weil-pbc-completion-finite-extension).

The factors are indexed by all primes lying over `p`, with finiteness a conclusion.
The maps `g q` are specified modulo every power of the maximal ideals, so they are
exactly the completion maps induced by `Localization.localRingHom`. The equation on
`a ⊗ₜ 1` expresses compatibility with the completed-base algebra structures.

Proof:
1. Localize at `p`: put `A = R_p`, `B = A ⊗ S`. Localization-base-change and
   localization-prime-residue-field-iso identify the primes over the maximal ideal of
   `A` with the primes over `p`, and their localizations with `S_q`. The localization
   is Noetherian by localization-noetherian; finite-type-algebra-noetherian applies to `S`.
2. For each positive `n`, finite-over-zero-dim-local-discrete-spectrum shows that
   `B / p^n B` has exactly these finitely many maximal ideals and nil Jacobson radical.
   Product-of-localizations-at-maximal decomposes this quotient, including the zero ring
   when there are no primes over `p`.
3. Localization-at-prime-of-quotient identifies each factor with `S_q / p^n S_q`.
   These identifications commute with reduction. Taking compatible sequences componentwise
   gives the product decomposition of the `p B`-adic completion of `B`.
4. Finite-after-completion identifies the `p`-adic and maximal-ideal-adic completions of
   each `S_q`, compatibly with both `S` and the completion of `A`.
5. Completion-finite-module-tensor gives `A^ ⊗_A B ≃ B^` and
   tensor-cancel-base-change identifies the source with `A^ ⊗_R S`.
6. Compose these isomorphisms. They are `S`-linear and compatible with the completed
   base; both sides are isomorphic to `B^`. An empty product is the zero ring. -/
theorem completion_finite_extension
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    Finite Q ∧
      ∃ (e : (C ⊗[R] S) ≃ₐ[S] (∀ q : Q, D q))
        (g : ∀ q : Q, C →+* D q),
        (∀ (q : Q) (n : ℕ) (a : C) (r : A),
          AdicCompletion.evalₐ m n a = Ideal.Quotient.mk (m ^ n) r →
          AdicCompletion.evalₐ
              (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n (g q a) =
            Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
              (Localization.localRingHom p q.1 (algebraMap R S)
                (Ideal.LiesOver.over (P := q.1) (p := p)) r)) ∧
        (∀ (a : C) (q : Q), e (a ⊗ₜ[R] (1 : S)) q = g q a) ∧
        Nonempty ((C ⊗[R] S) ≃ₐ[S] AdicCompletion J B) := by
  have hd := completion_finite_extension_decomposition R S p
  have ht := completion_finite_extension_tensor R S p
  rcases hd with ⟨hfin, ⟨e, g, hlevel, hcompat⟩⟩
  exact ⟨hfin, ⟨e, g, hlevel, hcompat, ht⟩⟩

end AdicCompletion

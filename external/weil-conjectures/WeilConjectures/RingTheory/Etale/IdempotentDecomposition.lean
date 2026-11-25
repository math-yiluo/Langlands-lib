/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Idempotent decomposition of a finite algebra after an étale neighbourhood

Let `S` be a finite `R`-algebra and `p` a prime of `R`. After base change to an étale
neighbourhood `(R', P)` of `p` with trivial residue field extension, the algebra `R' ⊗[R] S`
splits by complete orthogonal idempotents into factors with at most one prime over `P`
(Stacks 00UK/00UL, finite case). This is Mathlib's
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`.
-/

@[expose] public section

universe u v

open TensorProduct

/-- **Idempotent decomposition of a finite algebra after an étale neighbourhood** (finite case
of Stacks 00UK/00UL). If `S` is a finite `R`-algebra and `p` is a prime of `R`, there are an
étale `R`-algebra `R'`, a prime `P` of `R'` over `p` with `κ(p) ≅ κ(P)`, complete orthogonal
idempotents `e₁, …, eₙ, e_∞` of `R' ⊗[R] S` and primes `Q₁, …, Qₙ` of `R' ⊗[R] S` over `P`
such that `eᵢ ∉ Qᵢ`, and every prime `Q` over `P` contains `e_∞` and equals `Qᵢ` whenever
`eᵢ ∉ Q`.

(blueprint: `lem-weil-pbc-finite-algebra-etale-idempotent-decomposition`) -/
theorem Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_of_finite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ i, e i.castSucc ∉ P' i) ∧
      ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
        e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i :=
  Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq p

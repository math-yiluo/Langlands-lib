/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.NormalLocusOpen
import WeilConjectures.RingTheory.FiniteNormalCover
import WeilConjectures.RingTheory.FiniteNormalSup

@[expose] public section

universe u v

/-- Patch finite intermediate algebras normal above individual maximal ideals.
Source: Stacks Project, Algebra, Tag 0333, first and third paragraphs of the reverse
implication, stopping before the identification with the integral closure.
(blueprint: lem-weil-pbc-patch-local-normal-intermediate-algebras)

Proof: Fix the nonzero f. The principal localization A_f is an integrally closed
domain: its prime localizations are normal, so use the local criterion for normality.
For any finite intermediate algebra C in the integral closure, C_f = A_f, since
C_f is integral over the integrally closed A_f inside their common fraction field K.
Such a C is Noetherian and has an open normal locus by Tag 0332. The image Z_C of
its closed non-normal locus in Spec A is closed, since C is integral over A.
For every maximal m choose a C normal at all primes over m, using hLocal. Thus
m avoids Z_C. Every prime p lies in a maximal m; if p belonged to this closed Z_C,
its specialization m would too. Hence the complements of the Z_C cover Spec A.
Quasi-compactness supplies finitely many C_i whose complements still cover.
Let B be their supremum as A-subalgebras of K. Finite suprema of finite algebras
are finite, and B remains contained in the integral closure.
For any prime q of B, its contraction p to A avoids some Z_C_i. The contraction
q_i to C_i therefore has normal localization (C_i)_q_i. Localizing B at
C_i \ q_i gives an integral subring of K over this normal domain, with the same
fraction field, so it equals (C_i)_q_i. The ring B_q is a further localization
of that ring and is integrally closed. This gives a finite B normal at all primes;
the final identification B = integralClosure A K is deliberately not part of this lemma. -/
theorem exists_finite_locally_normal_intermediate_algebra (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hAway : ∃ f : A, f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hLocal : ∀ (m : Ideal A) [m.IsMaximal],
      ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
        ∀ (q : Ideal B) [q.IsPrime], Ideal.comap (algebraMap A B) q = m →
          IsIntegrallyClosed (Localization.AtPrime q)) :
    ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
      ∀ (q : Ideal B) [q.IsPrime], IsIntegrallyClosed (Localization.AtPrime q) := by
  obtain ⟨s, S, hS, hs, hn⟩ := exists_finite_normal_cover A K hAway hLocal
  exact finite_normal_sup A K s S hS hs hn

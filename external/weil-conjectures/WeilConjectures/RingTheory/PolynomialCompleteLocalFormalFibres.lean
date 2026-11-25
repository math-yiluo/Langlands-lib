/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.PolynomialCompleteLocalFibreReduction
import WeilConjectures.RingTheory.PolynomialCompleteLocalGenericFibre
import WeilConjectures.RingTheory.PolynomialCompleteLocalNonzeroFibreCharZero
import WeilConjectures.RingTheory.PolynomialFormalFiber

@[expose] public section

universe u

namespace Polynomial

/-- The completion map at a maximal ideal over the maximal ideal of a complete local
Noetherian ring is regular. Source: Stacks Project, More on Algebra, proof of
Proposition 07PV, paragraphs 2--5
(blueprint: lem-weil-pbc-polynomial-complete-local-formal-fibres).
Proof (the seven steps of the node), with T = S[x]_Q and C its completion:
1. S[x] and T are Noetherian, so T → C is flat (lem-weil-pbc-noetherian-completion-flat)
with Noetherian fibres (lem-weil-pbc-fibre-ring-noetherian); the primes of T are the rT,
r ⊆ Q, and it remains to show C ⊗_{S[x]} κ(r) geometrically regular over κ(r).
2. With p = r ∩ S and A = S/p (lem-weil-pbc-complete-local-quotient), pass to the
complete local domain A, the images of Q and r (r ∩ A = 0), using
lem-weil-pbc-localization-at-prime-of-quotient and lem-weil-pbc-local-completion-quotient.
3. Choose a regular complete local subring A₀ ⊆ A with A finite over A₀
(lem-weil-pbc-complete-local-domain-finite-over-regular); Q₀ = Q ∩ A₀[x] is maximal,
A₀[x] → A[x] is quasi-finite at Q, and lem-weil-pbc-formal-fibre-quasi-finite-ascent
reduces to the formal fibre of A₀[x] at Q₀ over r₀ = r ∩ A₀[x].
4. A₀[x] is regular (lem-weil-pbc-regular-ring-smooth-ascent), so C₀ = (A₀[x]_{Q₀})^∧ is
regular (lem-weil-pbc-completion-regular-local), and so are its localizations.
5. Characteristic 0, r₀ = 0: the fibre is a localization of C₀, hence regular, and
geometrically regular as there are no nontrivial purely inseparable extensions.
6. Characteristic 0, r₀ ≠ 0: r₀K₀[x] = (f), the fibre is R/fR with R a localization of
C₀; d/dx extends (theorem-finite-etale-covers-proper-henselian--2) with D(f) = f' a unit mod f, so
R/fR is regular (lem-weil-pbc-hypersurface-derivation-regular).
7. Characteristic p: A₀ ≅ k[[X₁, …, X_d]]; r₀ = 0 by lem-weil-pbc-helper-g-ring-char-p,
r₀ ≠ 0 by lem-weil-pbc-another-helper-g-ring. Steps 3, 2, 1 conclude. -/
theorem isRegular_algebraMap_adicCompletion_localization
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]
    (Q : Ideal (Polynomial S)) [Q.IsMaximal]
    (hQ : Q.comap (Polynomial.C : S →+* Polynomial S) = IsLocalRing.maximalIdeal S) :
    RingHom.IsRegular
      (algebraMap (Localization.AtPrime Q)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (Localization.AtPrime Q))) := by
  classical
  rw [RingHom.IsRegular, toAlgebra_algebraMap]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, ?_⟩
  intro s hs
  obtain ⟨A, hA, hdom, hnoeth, hlocal, hcomplete, q, r, hqmax, hrprime,
    hq, hrq, hrA, htransfer⟩ := exists_completeLocalDomain_fibre_reduction S Q hQ s
  let := hA
  let := hdom
  let := hnoeth
  let := hlocal
  let := hcomplete
  let := hqmax
  let := hrprime
  apply htransfer
  by_cases hr : r = ⊥
  · subst r
    exact completeLocalGenericFibre A q hq
  · rcases CharP.exists' (Localization.AtPrime (⊥ : Ideal A)) with hzero | ⟨p, hp, hchar⟩
    · let := hzero
      exact completeLocalNonzeroFibreCharZero A q hq r hrq hr hrA
    · let := hchar
      exact (formalFiber_isGeometricallyRegular A p hp.out q hq r hrq hr hrA).2

end Polynomial

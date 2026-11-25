/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.IsSMulRegular
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.IsSMulRegularOfGoodSequence
import WeilConjectures.RingTheory.CmModuleGoodElementSetup

/-!
# A dimension-cutting element on a Cohen–Macaulay module

Source: Stacks Project, Algebra, Lemma 10.103.3 (Tag 00N5), and Definition 10.103.1
(Tag 00N3) (blueprint: lem-weil-pbc-cm-module-good-element-nonzerodivisor).
-/

@[expose] public section

universe u v

namespace Module

/-- Source: Stacks Project, Algebra, Tag 00N5
(blueprint: lem-weil-pbc-cm-module-good-element-nonzerodivisor).
A dimension-cutting element is a nonzerodivisor (`IsSMulRegular`: multiplication by it
is injective) on a nonzero finite Cohen–Macaulay module;
its quotient is Cohen–Macaulay and has depth one less. Cohen–Macaulayness is written
as the equality of depth and support dimension, as in Tag 00N3. Dimension drops are
written as successor equalities to avoid truncated subtraction at zero.

Proof (the nine steps of the node, following Tag 00N5):
1. The maximal ideal belongs to the support: localization there is an isomorphism,
since every denominator is a unit (def-weil-pbc-module-localization). Thus the
support dimension d is nonnegative and finite by
lem-weil-pbc-noetherian-local-finite-krull-dimension and
 def-weil-pbc-krull-dimension-ring. The dimension-drop hypothesis rules out d = 0.
By def-weil-pbc-depth and def-weil-pbc-regular-sequence, choose a regular sequence
f₁, ..., f_d of length d in the maximal ideal.
2. Induct on the positive integer d, proving both conclusions simultaneously.
3. If g is good for this sequence, use
lem-weil-pbc-cm-module-good-sequence-element-nonzerodivisor. This proves d = 1.
4. Set M_i = M/(f₁, ..., f_i)M. By
lem-weil-pbc-support-quotient-ideal-module its support is Supp(M) intersected with
V(f₁, ..., f_i). Regularity and
lem-weil-pbc-support-dimension-quotient-element-equality give dimension d - i.
The support of M/gM likewise has dimension d - 1.
5. The finitely many minimal primes of these supports for i < d, together with
those of M/gM, do not include the maximal ideal, since these supports have positive
dimension. Use lem-weil-pbc-finite-module-support-annihilator,
lem-weil-pbc-noetherian-finitely-many-minimal-primes,
def-weil-pbc-noetherian-ring and lem-weil-pbc-prime-avoidance to choose h in the
maximal ideal avoiding all these primes.
6. By lem-weil-pbc-support-dimension-quotient-element-equality and
lem-weil-pbc-support-quotient-ideal-module, h is good for the chosen sequence and
Supp(M) intersected with V(h,g) has dimension d - 2.
7. The good-sequence lemma makes h regular and M/hM Cohen–Macaulay of dimension
d - 1. Apply induction to g on M/hM, using the support-quotient lemma: g is regular
there, and M/(h,g)M is Cohen–Macaulay of depth d - 2.
8. By def-weil-pbc-regular-sequence, (h,g) is regular. Use
lem-weil-pbc-regular-sequence-permutation-noetherian-local to swap it: g is regular
on M and h is regular on M/gM.
9. Prepend h to a regular sequence of length d - 2 on M/(g,h)M, obtaining depth
at least d - 1 on M/gM (def-weil-pbc-depth, def-weil-pbc-regular-sequence).
The reverse bound is lem-weil-pbc-depth-le-support-dimension. Hence its depth and
support dimension both equal d - 1, proving the two assertions. -/
theorem cm_module_good_element_nonzerodivisor
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hCM : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) = supportDim R M)
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdim : Order.krullDim (support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R) :
      Set (PrimeSpectrum R)) + 1 =
      supportDim R M) :
    IsSMulRegular M g ∧
      (IsLocalRing.depth (R := R) (QuotSMulTop g M) : WithBot ℕ∞) =
        supportDim R (QuotSMulTop g M) ∧
      IsLocalRing.depth (R := R) (QuotSMulTop g M) + 1 = IsLocalRing.depth (R := R) M :=
  by
    exact (exists_good_sequence_for_cm_element M hCM g hg hdim).elim (fun d hd =>
    hd.2.2.elim (fun fs hfs =>
      let T := isSMulRegular_of_good_sequence M d hd.1 hCM hd.2.1 fs hfs.1 hfs.2.1
        hfs.2.2.1 g hg hfs.2.2.2
      have hdepthM : IsLocalRing.depth (R := R) M = d := by
        simpa only [WithBot.coe_eq_coe] using hCM.trans hd.2.1
      ⟨T.1, T.2.1, by
        rw [T.2.2.1, hdepthM]
        simpa [Nat.cast_sub hd.1] using
          (tsub_add_cancel_of_le
            (Nat.cast_le.mpr hd.1 : (1 : ℕ∞) ≤ d))⟩))

end Module

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.GRingPairsForward
import WeilConjectures.RingTheory.GRingPairsBackward

/-!
# The G-ring criterion using pairs of prime ideals

Source: Stacks Project, More on Algebra, Lemma 07PN and Definition 07GH
(blueprint: lem-weil-pbc-g-ring-check-pairs-of-primes).
-/

@[expose] public section

universe u

/-- A Noetherian ring is a G-ring exactly when the generic formal fibres of all its
prime quotients, localized at primes containing the quotient ideal, are Noetherian and
geometrically regular. Source: Stacks Project, More on Algebra, Lemma 07PN
(blueprint: lem-weil-pbc-g-ring-check-pairs-of-primes).

Here `p.map (Ideal.Quotient.mk q)` is p/q in B = R/q. The residue field q.ResidueField
has its canonical B-algebra structure and is the fraction field of B. We use the
residue-field-first tensor order, canonically isomorphic to the order in the source.

Proof plan, following the seven steps of the node:
1. Localization-noetherian and adic-completion-noetherian show that R_p and its
   completion are Noetherian. Fibre-ring-noetherian gives Noetherianity of every
   E = κ(q) ⊗[R] completion(R_p).
2. Localization-at-prime-of-quotient gives a surjection R_p → (R/q)_(p/q), with
   kernel qR_p. Local-completion-quotient identifies the completion of the target
   with completion(R_p)/q completion(R_p), compatibly with the maps from B.
3. Tensor-quotient-base-change identifies this quotient with completion(R_p) ⊗[R] B.
   Localization-at-prime-of-quotient also identifies κ(q) with the fraction field of B.
   Tensor-cancel-base-change and tensor symmetry then identify the fibre F in the
   conclusion with E, as κ(q)-algebras.
4. If q is not contained in p, an element of q outside p becomes both zero and a unit
   in E. Thus E is zero. Every finite purely inseparable base change is also zero,
   hence Noetherian and regular (there are no primes).
5. Localization-regular and regular-composition show that regularity of the local
   completion map implies regularity of R → completion(R_p). Conversely use
   regular-through-localization. The fibre Noetherianity needed here is step 1.
6. Localization-flat, noetherian-completion-flat and flat-ring-map-comp show that
   R → completion(R_p) is flat. By the definition of a regular map and step 4, it
   is regular exactly when E is Noetherian and geometrically regular for all q ≤ p.
7. Noetherianity and regularity are invariant under ring isomorphisms; tensoring a
   κ(q)-algebra isomorphism with every finite purely inseparable field extension
   proves invariance of geometric regularity. Apply step 3, then steps 5 and 6 to
   the definition of IsGRing, which quantifies over all primes p. -/
theorem isGRing_iff_pairsOfPrimes (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔ ∀ (q p : Ideal R) [q.IsPrime] [p.IsPrime] (hqp : q ≤ p),
      let pbar := p.map (Ideal.Quotient.mk q)
      letI : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
      let L := Localization.AtPrime pbar
      let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
      let F := TensorProduct (R ⧸ q) q.ResidueField C
      IsNoetherianRing F ∧ Algebra.IsGeometricallyRegular q.ResidueField F := by
  exact ⟨isGRing_pairsOfPrimes_forward R, isGRing_pairsOfPrimes_backward R⟩

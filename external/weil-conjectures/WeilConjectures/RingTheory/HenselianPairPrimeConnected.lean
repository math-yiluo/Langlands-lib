/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.RingTheory.IntegralOverHenselianPair
import WeilConjectures.RingTheory.HenselianPairDomainConnected

/-!
# Connected zero loci over a henselian pair

Source: Stacks Project, More on Algebra, Lemma 15.11.16 (Tag 09Y6)
(blueprint: lem-weil-pbc-henselian-pair-prime-connected).
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- For a henselian pair `(A, I)` and a prime ideal `p`, the closed subset `V(p + I)`
is connected in its subspace topology, including nonemptiness.
Source: Stacks Project, More on Algebra, Lemma 15.11.16 (Tag 09Y6)
(blueprint: lem-weil-pbc-henselian-pair-prime-connected).

Proof:
1. Apply `henselianRing_of_isIntegral` to the integral quotient A → A/p.
   The quotient is a nonzero domain because p is prime.
2. Apply `connectedSpace_zeroLocus_of_henselian_domain` to the image of I in A/p.
   That theorem lifts roots of X(X - 1), making every quotient idempotent zero or one,
   and uses the clopen-idempotent criterion for connectedness, including nonemptiness.
3. Take the continuous image under the quotient-spectrum map. Mathlib's
   `image_comap_zeroLocus_eq_zeroLocus_comap` and the ideal comap-map identity
   identify this image with V(p ⊔ I). -/
theorem connectedSpace_zeroLocus_sup_of_henselian {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] (p : Ideal A) [p.IsPrime] :
    ConnectedSpace (zeroLocus ((p ⊔ I : Ideal A) : Set A)) := by
  have : HenselianRing (A ⧸ p) (I.map (algebraMap A (A ⧸ p))) :=
    henselianRing_of_isIntegral A I (A ⧸ p)
  have hconn := isConnected_iff_connectedSpace.mpr
    (connectedSpace_zeroLocus_of_henselian_domain (I.map (algebraMap A (A ⧸ p))))
  have himage := hconn.image (comap (Ideal.Quotient.mk p))
    (continuous_comap _).continuousOn
  apply isConnected_iff_connectedSpace.mp
  simpa [Ideal.Quotient.algebraMap_eq,
    image_comap_zeroLocus_eq_zeroLocus_comap (A ⧸ p) (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm] using himage

end PrimeSpectrum

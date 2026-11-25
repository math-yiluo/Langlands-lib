/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.MvPolynomial.Basic
import WeilConjectures.RingTheory.RelativeCompleteIntersectionClosedFiberRegularSequence
import WeilConjectures.RingTheory.RegularSequenceFlatClosedFiber

/-! # The Noetherian case of local complete-intersection regularity

Source: Stacks Project, Algebra, Tag 00SV, first paragraph of the proof.
-/

@[expose] public section

universe u

namespace Algebra

/-- Over a Noetherian base the specified equations are regular at every polynomial prime
containing their ideal.
Source: Stacks Project, Algebra, Tag 00SV, first paragraph of the proof.
(blueprint: lem-weil-pbc-relative-ci-noetherian-local-regular-sequence).

Proof: Put `P = R[x]`, `p = Q ∩ R`, and `B = P_Q`. The polynomial ring is free over `R`
and Noetherian, so the canonical map `R_p → B` is flat and local between Noetherian local
rings. Polynomial scalar extension identifies the polynomial fibre with `κ(p)[x]`.
The fibre-prime correspondence gives a prime over `Q`; since `Q` contains the equations,
the induced quotient fibre is nonzero. Base change (00SS) preserves the specified relative
complete-intersection presentation, hence its dimension is `n-c`, with `c ≤ n`.
Apply the field-case local regular-sequence lemma (00SC) at this fibre prime. The natural
fibre-local-ring isomorphism identifies its localized polynomial ring with the closed
fibre of `R_p → B`, and sends each displayed equation to its closed-fibre image.
Transport regularity through this isomorphism and apply the flat closed-fibre lifting
lemma (00MG). Its regularity conclusion is the assertion here. For `c=0`, all lists are
empty and `B` is nonzero because `Q` is prime. The zero quotient has no such prime `Q`.
-/
theorem isRegular_localization_of_relativeCompleteIntersection_of_noetherian
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (Q : Ideal (MvPolynomial (Fin n) R)) [Q.IsPrime]
    (hQ : Ideal.span (Set.range f) ≤ Q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime Q)
      ((List.ofFn f).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime Q))) := by
  let P := MvPolynomial (Fin n) R
  let p := Q.comap (algebraMap R P)
  let φ := Localization.localRingHom p Q (algebraMap R P) rfl
  have hflat : φ.Flat := RingHom.Flat.localRingHom
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R P)) Q p rfl
  exact (RingTheory.Sequence.isRegular_and_flat_quotient_of_closedFiber φ hflat
    ((List.ofFn f).map (algebraMap P (Localization.AtPrime Q)))
      (isRegular_closedFiber_of_relativeCompleteIntersection f h Q hQ)).1

end Algebra

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Colon
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.FlatAssociatedPrimeDVR
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# DVR localizations of the completion at associated primes

Source: Stacks Project, Algebra, Lemma Tag 032Z
(blueprint: lem-weil-pbc-codimension-one-analytically-unramified).
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- (blueprint: lem-weil-pbc-codimension-one-analytically-unramified)
Stacks Project, Algebra, Lemma Tag 032Z. If `R` is Noetherian local, `R_p` is a DVR,
and `p` is analytically unramified, then the completion localized at any associated
prime of its quotient by the extended ideal `p` is a DVR. The colon of the zero
submodule by `{z}` is exactly the annihilator of `z` (without taking a radical).

Proof, following the seven steps of the node:
1. The completion is Noetherian and flat over `R`
   (`lem-weil-pbc-adic-completion-noetherian`, `lem-weil-pbc-noetherian-completion-flat`).
   Its localization `C` at `q` is Noetherian local
   (`lem-weil-pbc-localization-noetherian`).
2. The quotient `B` of the completion by the extended `p` is the completion of `R/p`
   (`lem-weil-pbc-local-completion-quotient`), hence reduced by analytic unramifiedness.
3. Write `q = Ann(z)` for nonzero `z` in `B` and lift `z` to the completion.
   The lift is outside `q`, since otherwise `z^2 = 0` contradicts reducedness.
   For `a` in `q`, the product `az` belongs to the extended `p`; invert the lift
   in `C` to obtain `qC = pC`.
4. Multiplication by any `s` outside `p` is injective on `R/p`. Flatness preserves
   injectivity on `B`, so `s` cannot annihilate `z`; thus its image is outside `q`.
5. Choose `x` in `p` generating `pR_p` with nonzero image. Clear denominators on
   finitely many generators of `p` to find `s` outside `p` with `sp` contained in `xR`.
   Inverting `s` in `C` gives `qC = pC = xC`.
6. The finitely generated ideal `Ann_R(x)` vanishes at `p`, so some `t` outside `p`
   kills it. Flatness identifies `Ann(x)` in the completion with its extension.
   Inverting `t` shows that `x` is a nonzerodivisor in `C`.
7. Krull intersection (`lem-weil-pbc-krull-intersection-jacobson`) gives
   intersection of all `x^n C` equal to zero. Every nonzero element is a power of
   `x` times a unit; products of nonzero elements are nonzero. Hence `C` is a domain
   with nonzero principal maximal ideal, and therefore a DVR.
-/
theorem isDiscreteValuationRing_atPrime_of_isAnalyticallyUnramified
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime p)] (hp : p.IsAnalyticallyUnramified)
    (q : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) [q.IsPrime]
    (hq : ∃ z : AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
        p.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)),
      q = (⊥ : Submodule (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
          p.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))).colon {z}) :
    ∃ (_ : IsDomain (Localization.AtPrime q)),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have : IsNoetherianRing A := AdicCompletion.isNoetherianRing _
  obtain ⟨_, _, _, _, _, _, e, _⟩ :=
    exists_local_completion_quotient R (R ⧸ p) (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective
  have : IsReduced
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk p))
        (R ⧸ p)) := hp.2
  have : IsReduced (A ⧸ p.map (algebraMap R A)) := by
    have h := isReduced_of_injective e e.injective
    rw [Ideal.mk_ker] at h
    exact h
  exact isDiscreteValuationRing_atPrime_of_flat_reduced_quotient R A p q hq

end AdicCompletion

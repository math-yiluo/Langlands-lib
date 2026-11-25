/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

/-!
# Étale algebras over reduced rings are reduced

Since an étale algebra is Zariski locally standard étale
(`Algebra.IsEtaleAt.exists_isStandardEtale`), and a standard étale algebra over a reduced ring
is reduced (`StandardEtalePair.isReduced_ring`), an étale algebra over a reduced ring is
reduced.

## Main statements

- `Algebra.Etale.isReduced`: an étale algebra over a reduced ring is reduced.
-/

@[expose] public section

namespace Algebra.Etale

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- An étale algebra `A` over a reduced ring `R` is reduced. The annihilator of a nilpotent
`x ∈ A` is the unit ideal: every prime `Q` of `A` has a basic open neighbourhood `D(f)` with
`A[1/f]` standard étale over `R`, hence reduced, so `x` vanishes in `A[1/f]` and some `fⁿ ∉ Q`
kills `x`. This is a special case of [Stacks 033B]. -/
theorem isReduced [IsReduced R] [Etale R A] : IsReduced A := by
  refine ⟨fun x hx ↦ ?_⟩
  suffices h : LinearMap.ker (LinearMap.mulRight A x) = ⊤ by
    simpa using (h ▸ Submodule.mem_top : (1 : A) ∈ LinearMap.ker (LinearMap.mulRight A x))
  by_contra hne
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hfQ, hf⟩ := IsEtaleAt.exists_isStandardEtale (R := R) Q
  have : IsReduced (Localization.Away f) := by
    let P := hf.nonempty_standardEtalePresentation.some
    exact isReduced_of_injective P.equivRing.toRingHom P.equivRing.injective
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f)
    (Localization.Away f) x).1 (hx.map _).eq_zero
  exact hfQ (hQ.isPrime.mem_of_pow_mem n (hle (by simpa using hn)))

end Algebra.Etale

/-- **Étale algebras are Zariski locally standard étale.** Let `B` be an étale `S`-algebra and
`q` a prime of `B`. Then there are `g ∉ q`, a standard étale pair `P = (f, h)` over `S` and an
isomorphism of `S`-algebras `B[1/g] ≃ P.Ring = S[t][Y] ⧸ (f, Yh - 1)`. This is mathlib's
`Algebra.IsEtaleAt.exists_isStandardEtale`.
(blueprint: `lem-weil-pbc-etale-locally-standard`) -/
@[stacks 00UE]
theorem Algebra.Etale.exists_algEquiv_standardEtalePair_ring (S B : Type*) [CommRing S]
    [CommRing B] [Algebra S B] [Algebra.Etale S B] (q : Ideal B) [q.IsPrime] :
    ∃ g ∉ q, ∃ P : StandardEtalePair S, Nonempty (Localization.Away g ≃ₐ[S] P.Ring) := by
  obtain ⟨g, hg, h⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) q
  obtain ⟨P⟩ := h.nonempty_standardEtalePresentation
  exact ⟨g, hg, P.P, ⟨P.equivRing⟩⟩

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.CohenRing
import WeilConjectures.RingTheory.CohenRingModPowFormallySmoothCore
import Mathlib.Algebra.Algebra.ZMod

@[expose] public section
universe u v
namespace IsDiscreteValuationRing
/-- The explicit square-zero lifting clause for a Cohen ring modulo a prime power.
Source: Stacks Project, Algebra, Lemma Tag 0329.
(blueprint: lem-weil-pbc-cohen-ring-mod-pn-formally-smooth-explicit)

Choose the canonical ZMod (p^n)-algebra structures on Λ/(p^n) and D using
that their characteristics divide p^n. The core theorem supplies formal smoothness
of Λ/(p^n). Every ring homomorphism between these algebras commutes with scalars,
since each element of ZMod (p^n) is an integer cast. Apply
`Algebra.FormallySmooth.exists_lift` to the square-zero ideal J (nilpotence exponent 2),
then forget the algebra structure of the lift. This works in any target universe and
also when D is the zero ring. -/
theorem cohenRing_mod_pow_formallySmooth_explicit
    (p : ℕ) (Λ : Type u) [CommRing Λ] (hΛ : IsCohenRing p Λ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ (D : Type v) [CommRing D], (p : D) ^ n = 0 →
      ∀ (J : Ideal D), J ^ 2 = ⊥ →
        ∀ (g : (Λ ⧸ Ideal.span {(p : Λ) ^ n}) →+* D ⧸ J),
          ∃ f : (Λ ⧸ Ideal.span {(p : Λ) ^ n}) →+* D,
            (Ideal.Quotient.mk J).comp f = g := by
  let Q := Λ ⧸ Ideal.span {(p : Λ) ^ n}
  have hQ : ((p ^ n : ℕ) : Q) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _) (p ^ n), Nat.cast_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  let : Algebra (ZMod (p ^ n)) Q := ZMod.algebra' Q (ringChar Q) (ringChar.dvd hQ)
  let : Algebra.FormallySmooth (ZMod (p ^ n)) Q :=
    cohenRing_mod_pow_formallySmooth_core p Λ hΛ n hn
  intro D _ hD J hJ g
  let : Algebra (ZMod (p ^ n)) D :=
    ZMod.algebra' D (ringChar D) (ringChar.dvd (by simpa using hD))
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩
    ({ toRingHom := g, commutes' := by
        intro r
        obtain ⟨k, rfl⟩ := ZMod.intCast_surjective r
        simp } : Q →ₐ[ZMod (p ^ n)] D ⧸ J)
  exact ⟨f.toRingHom, congrArg AlgHom.toRingHom hf⟩
end IsDiscreteValuationRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.RingTheory.CohenRing
import WeilConjectures.RingTheory.CohenRingModPowFormallySmoothCore
import WeilConjectures.RingTheory.CohenRingModPowFormallySmoothExplicit

/-!
# Formal smoothness of a Cohen ring modulo a prime power

Source: Stacks Project, Algebra, Lemma Tag 0329 and Definition Tag 0327
(blueprint: lem-weil-pbc-cohen-ring-mod-pn-formally-smooth).
-/

@[expose] public section

universe u v

namespace IsDiscreteValuationRing

/-- A Cohen ring modulo `p ^ n` is formally smooth over `ZMod (p ^ n)` for `n ≥ 1`.
The Cohen-ring hypothesis is `IsCohenRing p Λ` (prime `p`, DVR, maximal ideal `pΛ`,
`pΛ`-adically complete). The first clause is formal smoothness of `ℤ/p^n → Λ/p^nΛ`
(`Algebra.FormallySmooth`, the case `𝔫 = 0` of the adic notion); the second spells out
the same property for ring homomorphisms in an arbitrary target universe.
The `ZMod (p ^ n)`-algebra structure on the quotient exists and is unique, so the first
clause quantifies over it without adding a hypothesis or choosing auxiliary data.
Source: Stacks Project, Algebra, Lemma Tag 0329, Definition Tag 0327.
(blueprint: lem-weil-pbc-cohen-ring-mod-pn-formally-smooth)

Proof route from the blueprint:
1. Define P(m) to be the displayed square-zero lifting property. A ring with `p ^ m = 0`
is uniquely a `ZMod (p ^ m)`-algebra, and every ring map between such rings is linear.
By `Algebra.FormallySmooth.iff_comp_surjective`, formal smoothness is this lifting property.
2. The Cohen-ring hypotheses give a residue field of characteristic p. They also imply
that Λ is torsion-free over ℤ: integers prime to p are units, while p is nonzero in the
DVR, hence no nonzero integer kills a nonzero element of Λ.
3. P(1) follows from `lem-weil-pbc-field-char-p-nilpotent-lifting` for the residue field
and nilpotence exponent 2 (Stacks Tag 0322).
4. By `lem-weil-pbc-pid-torsion-free-module-flat`, Λ is flat over ℤ; then
`lem-weil-pbc-flat-module-quotient-flat` makes Λ/p^mΛ flat over ℤ/p^mℤ.
5. Assuming P(n), apply `lem-weil-pbc-lift-formal-smoothness-flat-square-zero`
(Stacks Tag 031L) to ℤ/p^(n+1)ℤ → Λ/p^(n+1)Λ and I = (p^n). The ideal I is square-zero
since 2n ≥ n+1, flatness is step 4, and reduction modulo I is the map for exponent n.
Thus P(n+1) holds.
6. Induction from step 3 proves P(n) for every n ≥ 1, and step 1 identifies the first
clause with this explicit lifting condition. Completeness is retained as part of the
Cohen-ring hypothesis, although this proof uses only its DVR and uniformizer clauses. -/
theorem cohenRing_mod_pow_formallySmooth
    (p : ℕ) (Λ : Type u) [CommRing Λ] (hΛ : IsCohenRing p Λ)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ [Algebra (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})],
      Algebra.FormallySmooth (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})) ∧
    (∀ (D : Type v) [CommRing D], (p : D) ^ n = 0 →
      ∀ (J : Ideal D), J ^ 2 = ⊥ →
        ∀ (g : (Λ ⧸ Ideal.span {(p : Λ) ^ n}) →+* D ⧸ J),
          ∃ f : (Λ ⧸ Ideal.span {(p : Λ) ^ n}) →+* D,
            (Ideal.Quotient.mk J).comp f = g) := by
  exact ⟨cohenRing_mod_pow_formallySmooth_core p Λ hΛ n hn,
    cohenRing_mod_pow_formallySmooth_explicit p Λ hΛ n hn⟩

end IsDiscreteValuationRing

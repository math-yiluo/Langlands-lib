/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The Artin–Schreier kernel in a local ring

Source: blueprint sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md, proof, first sentence;
Stacks Project, Étale Cohomology, Section 59.63 (Tag 0A3J).
(blueprint: lem-sc-local-ring-artin-schreier-kernel)
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- In a local commutative ring with `p = 0`, the roots of `X ^ p - X` are exactly the
unique images of elements of `ZMod p` under the canonical cast.
Source: blueprint lemma-p-torsion-affine-curve-characteristic--3, proof, first sentence; Stacks
Project, Tag 0A3J. (blueprint: lem-sc-local-ring-artin-schreier-kernel)

Proof:
1. Reduce a root `a` modulo the unique maximal ideal to the residue field. By
   `lem-sc-field-artin-schreier-kernel`, its image is the image of a unique `c : ZMod p`.
2. Set `b = a - ZMod.cast c`. Then `b` belongs to the maximal ideal and `b ^ p = b`,
   by the characteristic-`p` binomial theorem and the field root calculation. Since
   `p ≥ 2`, also `b ^ (p - 1)` is in the maximal ideal. Hence `1 - b ^ (p - 1)` is a unit
   by `lem-weil-pbc-local-ring-unit-criterion` (Stacks Tag 00E9). The equality
   `b * (1 - b ^ (p - 1)) = 0` gives `b = 0`, so `a = ZMod.cast c`.
3. Conversely, every `c : ZMod p` satisfies `c ^ p = c` by the field root calculation;
   the canonical ring map preserves this equation. If two constants have equal images
   in the local ring, reduction to the residue field and injectivity of its prime-field
   map give equality of the constants. This proves the asserted unique correspondence,
   equivalently the bijection from `ZMod p` to the root set. -/
theorem pow_eq_self_iff_existsUnique_zmod {R : Type u} [CommRing R] [IsLocalRing R]
    (p : ℕ) (hp : p.Prime) (hchar : (p : R) = 0) (a : R) :
    a ^ p = a ↔ ∃! c : ZMod p, (ZMod.cast c : R) = a := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr hchar
  have : CharP (ResidueField R) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    simpa only [map_natCast, map_zero] using congrArg (residue R) hchar)
  have hcast (c : ZMod p) : (ZMod.cast c : R) ^ p = ZMod.cast c := by
    rw [← ZMod.cast_pow dvd_rfl, ZMod.pow_card]
  constructor
  · intro ha
    have hres : residue R a ∈ (⊥ : Subfield (ResidueField R)) :=
      (Subfield.mem_bot_iff_pow_eq_self (F := ResidueField R) p).mpr (by
        simpa only [map_pow] using congrArg (residue R) ha)
    rw [← ZMod.fieldRange_castHom_eq_bot p] at hres
    obtain ⟨c, hc⟩ := hres
    have hmap (d : ZMod p) :
        residue R (ZMod.cast d : R) = (ZMod.cast d : ResidueField R) := by
      simp only [ZMod.cast_eq_val, map_natCast]
    have hz : residue R (a - (ZMod.cast c : R)) = 0 := by
      rw [map_sub, hmap, ← hc]
      simp only [ZMod.castHom_apply, sub_self]
    have hpow : (a - (ZMod.cast c : R)) ^ p = a - (ZMod.cast c : R) := by
      rw [sub_pow_char, ha, hcast]
    have hu : IsUnit (1 - (a - (ZMod.cast c : R)) ^ (p - 1)) :=
      (residue_ne_zero_iff_isUnit _).mp (by
        rw [map_sub, map_one, map_pow, hz, zero_pow (by have := hp.two_le; omega), sub_zero]
        exact one_ne_zero)
    have heq : a - (ZMod.cast c : R) = 0 := hu.mul_right_cancel (by
      rw [zero_mul, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hp.one_le, hpow,
        sub_self])
    refine ⟨c, (sub_eq_zero.mp heq).symm, ?_⟩
    intro d hd
    apply ZMod.castHom_injective R
    change (ZMod.cast d : R) = ZMod.cast c
    exact hd.trans (sub_eq_zero.mp heq)
  · rintro ⟨c, hc, _⟩
    rw [← hc]
    exact hcast c

end IsLocalRing

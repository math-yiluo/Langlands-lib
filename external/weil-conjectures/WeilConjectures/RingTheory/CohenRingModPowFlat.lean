/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.RingTheory.CohenRing
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing

/-! # Flatness of the prime-power quotients of a Cohen ring -/

@[expose] public section

universe u

namespace IsDiscreteValuationRing

/-- Flatness used in the induction of Stacks Project, Algebra, Tag 0329.
(blueprint: lem-weil-pbc-cohen-ring-mod-pow-flat)

Proof: The domain underlying a Cohen ring has characteristic zero. Indeed p is
nonzero because its principal ideal is the nonzero maximal ideal of the DVR.
If another prime q vanished, Bezout for p and q would make p a unit, contradicting
membership in the maximal ideal. Thus the integer action is torsion-free. A
torsion-free module over the PID ℤ is flat (Tag 0AUW). Base change along
ℤ → ℤ/p^n gives flatness of Λ/(p^n) over ℤ/p^n (Tag 00HI), using the tensor
quotient isomorphism. Identify ℤ/p^n with ZMod (p^n). Every algebra structure
has this same integer-cast map, so flatness holds for the displayed structure. -/
theorem cohenRing_mod_pow_flat
    (p : ℕ) (Λ : Type u) [CommRing Λ] (hΛ : IsCohenRing p Λ) (n : ℕ)
    [Algebra (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n})] :
    Module.Flat (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n}) := by
  obtain ⟨hp, hdomain, hdvr, hm, hcomplete⟩ := hΛ
  have := hdomain
  have hchar : CharZero Λ := by
    apply (CharZero.charZero_iff_forall_prime_ne_zero Λ).mpr
    intro q hq hzero
    by_cases heq : q = p
    · subst q
      have hbot : IsLocalRing.maximalIdeal Λ = ⊥ := by
        rw [hm, hzero, Ideal.span_singleton_eq_bot]
      exact IsDiscreteValuationRing.not_isField Λ
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
    · have hcop : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr
        (fun h ↦ heq ((hq.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one).symm)
      have hunit : IsUnit (p : Λ) := by
        have h : IsCoprime (p : Λ) (q : Λ) := by
          simpa only [map_natCast] using hcop.isCoprime.map (Int.castRingHom Λ)
        simpa only [hzero, isCoprime_zero_right] using h
      have hmem : (p : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
        rw [hm]
        exact Ideal.mem_span_singleton_self _
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit
  let _ : CharZero Λ := hchar
  have : Module.Flat ℤ Λ := inferInstance
  let I : Ideal ℤ := Ideal.span {((p ^ n : ℕ) : ℤ)}
  let J : Ideal Λ := I.map (algebraMap ℤ Λ)
  have hJ : J = Ideal.span {(p : Λ) ^ n} := by
    simp [J, I, Ideal.map_span, Set.image_singleton]
  have : Module.Flat (ℤ ⧸ I) (Λ ⧸ J) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Λ I).toLinearEquiv
  let e := Int.quotientSpanNatEquivZMod (p ^ n)
  let eS := Ideal.quotEquivOfEq hJ
  let g : (ℤ ⧸ I) →+* (Λ ⧸ J) := algebraMap (ℤ ⧸ I) (Λ ⧸ J)
  have hg : g.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hf := ((RingHom.Flat.of_bijective (f := e.symm.toRingHom) e.symm.bijective).comp hg).comp
    (RingHom.Flat.of_bijective (f := eS.toRingHom) eS.bijective)
  have heq : eS.toRingHom.comp (g.comp e.symm.toRingHom) =
      algebraMap (ZMod (p ^ n)) (Λ ⧸ Ideal.span {(p : Λ) ^ n}) := by
    apply RingHom.ext
    intro x
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    simp
  rw [heq] at hf
  exact RingHom.flat_algebraMap_iff.mp hf

end IsDiscreteValuationRing

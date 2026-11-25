/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import WeilConjectures.RingTheory.KollarFiniteExtensionFromStableIdeal
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Kollár's alternatives after a regular element

Source: Stacks Project, Algebra, Tag 0BHZ, the two subcases following the choice of y.
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- Source: Stacks Project, Algebra, Lemma Tag 0BHZ, fourth and fifth proof paragraphs.
(blueprint: lem-weil-pbc-kollar-regular-element-alternatives).

Proof: The associated-prime hypothesis supplies a nonzero class of y modulo xR whose
annihilator is the maximal ideal. Thus y is outside xR and y m is contained in xR.
If y m is contained in x m, construct the subalgebra of R localized at x that
preserves the image of m. Multiplication by x injects this subalgebra into the
finite image of m, proving its finiteness over R. It contains y/x, so R does not
surject onto it, while regularity of x makes the map injective. The image of m
is already an ideal of the subalgebra, giving the cokernel condition with n = 1.
The image of x acts injectively, so m cannot be the annihilator of an element.
Lift this explicitly constructed subalgebra to Type (max u v).
Otherwise choose t in m with yt = xu for a unit u, and replace t by u inverse times t.
Then yt = x. Regularity of x implies regularity of y. For every t' in m, write yt' = xs;
cancelling y gives t' = ts, hence m = (t). The dimension is at most one by the height
theorem. Quotienting by the regular element x drops the dimension by one; since
R/(x) is nonzero, its dimension is nonnegative, so R has dimension at least one.
Thus the dimension is one, and the one generator of m proves that R is regular local. -/
theorem kollar_regular_element_alternatives (R : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hr : IsSMulRegular R x)
    (hquot : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x R)) :
    let extension : Prop := ∃ (S : Type (max u v)) (sRing : CommRing S),
      letI := sRing
      ∃ φ : R →+* S,
        letI := φ.toAlgebra
        Nontrivial S ∧ Module.Finite R S ∧ ¬ Function.Bijective φ ∧
          (∃ n : ℕ, 1 ≤ n ∧ (maximalIdeal R) ^ n * RingHom.ker φ = ⊥ ∧
            ∀ z ∈ Ideal.map φ ((maximalIdeal R) ^ n), z ∈ φ.range) ∧
          ¬ ∃ z : S, ∀ a : R, φ a * z = 0 ↔ a ∈ maximalIdeal R
    (IsRegularLocalRing R ∧ ringKrullDim R = 1) ∨ extension := by
  classical
  dsimp only
  have hw : ∃ y : R, y ∉ Ideal.span ({x} : Set R) ∧
      ∀ a ∈ maximalIdeal R, a * y ∈ Ideal.span ({x} : Set R) := by
    obtain ⟨_, q, hq⟩ := isAssociatedPrime_iff.mp hquot
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hzero : (Submodule.Quotient.mk y : QuotSMulTop x R) ≠ 0 := by
      intro hz
      apply (inferInstance : (maximalIdeal R).IsMaximal).ne_top
      rw [hq]
      ext a
      simp only [Submodule.mem_colon_singleton, hz, smul_zero, Submodule.mem_bot,
        Submodule.mem_top]
    refine ⟨y, ?_, ?_⟩
    · intro hy
      apply hzero
      apply Submodule.Quotient.mk_eq_zero _ |>.mpr
      simpa [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton, dvd_def,
        mul_comm, eq_comm] using hy
    · intro a ha
      rw [hq, Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
      change (Submodule.Quotient.mk (a * y) : QuotSMulTop x R) = 0 at ha
      have := (Submodule.Quotient.mk_eq_zero _).mp ha
      simpa [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton, dvd_def,
        mul_comm, eq_comm] using this
  obtain ⟨y, hy, hym⟩ := hw
  by_cases hstable : ∀ a ∈ maximalIdeal R, ∃ b ∈ maximalIdeal R, x * b = a * y
  · exact Or.inr (kollar_finite_extension_of_stable_ideal R x hx hr y hy hstable)
  · left
    push Not at hstable
    obtain ⟨a, ha, hbad⟩ := hstable
    obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton.mp (hym a ha))
    have hcunit : IsUnit c := by
      by_contra hn
      exact hbad c hn hc.symm
    obtain ⟨u, rfl⟩ := hcunit
    let t : R := ↑u⁻¹ * a
    have ht : t ∈ maximalIdeal R := (maximalIdeal R).mul_mem_left _ ha
    have hyt : y * t = x := by
      dsimp [t]
      calc
        y * (↑u⁻¹ * a) = ↑u⁻¹ * (a * y) := by ring
        _ = ↑u⁻¹ * (x * ↑u) := by rw [hc]
        _ = x := by simp [mul_comm, mul_assoc]
    have hry : IsSMulRegular R y := by
      intro b c hbc
      apply hr
      change x * b = x * c
      change y * b = y * c at hbc
      rw [← hyt]
      simpa [mul_assoc, mul_left_comm] using congrArg (t * ·) hbc
    have hm : maximalIdeal R = Ideal.span ({t} : Set R) := by
      apply le_antisymm
      · intro b hb
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hym b hb)
        apply Ideal.mem_span_singleton.mpr
        refine ⟨c, ?_⟩
        apply hry
        change y * b = y * (t * c)
        calc
          y * b = x * c := by simpa [mul_comm] using hc
          _ = y * (t * c) := by rw [← hyt, mul_assoc]
      · exact Ideal.span_le.mpr (by simpa using ht)
    have hx0 : x ≠ 0 := by
      intro hx0
      have h := hr (a₁ := (1 : R)) (a₂ := 0) (by simp [hx0])
      exact one_ne_zero h
    have ht0 : t ≠ 0 := by
      intro ht0
      exact hx0 (by simpa [ht0] using hyt.symm)
    have hdimle : ringKrullDim R ≤ 1 := by
      simpa [hm, Submodule.spanFinrank_singleton ht0] using
        ringKrullDim_le_spanFinrank_maximalIdeal R
    have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
          (Ideal.span_le.mpr (by simpa using hx)))
    have hdimge : 1 ≤ ringKrullDim R := by
      rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hr hx]
      simpa only [zero_add, add_comm] using add_le_add_right
        (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Ideal.span ({x} : Set R))) 1
    have hdim : ringKrullDim R = 1 := le_antisymm hdimle hdimge
    refine ⟨(isRegularLocalRing_iff R).mpr ?_, hdim⟩
    simp [hm, Submodule.spanFinrank_singleton ht0, hdim]

end IsLocalRing

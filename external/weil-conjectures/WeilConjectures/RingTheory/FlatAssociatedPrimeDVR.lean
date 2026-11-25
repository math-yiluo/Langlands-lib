/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Associated-prime localizations of a flat algebra with reduced quotient

Source: Stacks Project, Algebra, Tag 032Z, the algebraic argument after reducedness.
(blueprint: lem-weil-pbc-flat-associated-prime-dvr)
-/

@[expose] public section

universe u v

namespace AdicCompletion

private theorem quotient_annihilator_le {A : Type*} [CommRing A] (I : Ideal A)
    (z : A ⧸ I) : I ≤ (⊥ : Submodule A (A ⧸ I)).colon {z} := by
  intro a ha
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change Ideal.Quotient.mk I a * z = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]

private theorem associated_quotient_map_eq {A : Type*} [CommRing A] (I : Ideal A)
    [IsReduced (A ⧸ I)] (q : Ideal A) [q.IsPrime]
    (hq : ∃ z : A ⧸ I, q = (⊥ : Submodule A (A ⧸ I)).colon {z}) :
    q.map (algebraMap A (Localization.AtPrime q)) =
      I.map (algebraMap A (Localization.AtPrime q)) := by
  obtain ⟨z, hz⟩ := hq
  have hz0 : z ≠ 0 := by
    intro h
    have : q = ⊤ := by simp [hz, h, Submodule.colon_singleton_zero]
    exact (inferInstance : q.IsPrime).ne_top this
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
  have haq : a ∉ q := by
    intro h
    rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot] at h
    have hzz : z * z = 0 := by
      change Ideal.Quotient.mk I a * z = 0 at h
      rwa [ha] at h
    exact hz0 (IsNilpotent.eq_zero ⟨2, by simpa [pow_two] using hzz⟩)
  have hu : IsUnit (algebraMap A (Localization.AtPrime q) a) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ q a).mpr haq
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    have hba : b * a ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_mul, ha]
      rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot] at hb
      exact hb
    change algebraMap A (Localization.AtPrime q) b ∈
      I.map (algebraMap A (Localization.AtPrime q))
    apply (Ideal.mul_unit_mem_iff_mem _ hu).mp
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ hba
  · exact Ideal.map_mono (hz ▸ quotient_annihilator_le I z)

private theorem associated_quotient_comap {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (p : Ideal R) [p.IsPrime]
    (q : Ideal A) [q.IsPrime]
    (hq : ∃ z : A ⧸ p.map (algebraMap R A),
      q = (⊥ : Submodule A (A ⧸ p.map (algebraMap R A))).colon {z}) :
    q.comap (algebraMap R A) = p := by
  obtain ⟨z, hz⟩ := hq
  have hz0 : z ≠ 0 := by
    intro h
    have : q = ⊤ := by simp [hz, h, Submodule.colon_singleton_zero]
    exact (inferInstance : q.IsPrime).ne_top this
  have hpq : p.map (algebraMap R A) ≤ q := hz ▸ quotient_annihilator_le _ z
  apply le_antisymm
  · intro r hr
    by_contra hrp
    have hr0 : Ideal.Quotient.mk p r ≠ 0 := by
      simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hrp
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A p
    have hreg := Module.Flat.isSMulRegular_of_isRegular
      (M := TensorProduct R (R ⧸ p) A) (IsRegular.of_ne_zero hr0)
    have hzero : Ideal.Quotient.mk p r • z = 0 := by
      rw [Ideal.mem_comap, hz, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
      simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R (R ⧸ p)
        (A ⧸ p.map (algebraMap R A)), Ideal.Quotient.algebraMap_eq] using hr
    have hezero : e z = 0 := hreg (by simpa using congrArg e hzero)
    exact hz0 (e.injective (by simpa using hezero))
  · intro r hr
    exact hpq (Ideal.mem_map_of_mem _ hr)

private theorem factor_of_bound {C : Type*} [CommRing C] [IsLocalRing C]
    (x : C) (hm : IsLocalRing.maximalIdeal C = Ideal.span {x}) (N : ℕ) :
    ∀ b : C, b ∉ IsLocalRing.maximalIdeal C ^ N →
      ∃ n : ℕ, ∃ u : C, IsUnit u ∧ b = x ^ n * u := by
  induction N with
  | zero => simp
  | succ N ih =>
    intro b hb
    by_cases hu : IsUnit b
    · exact ⟨0, b, hu, by simp⟩
    have hbmem : b ∈ IsLocalRing.maximalIdeal C := by
      simpa [IsLocalRing.mem_maximalIdeal] using hu
    rw [hm, Ideal.mem_span_singleton] at hbmem
    obtain ⟨c, hc⟩ := hbmem
    have hcnot : c ∉ IsLocalRing.maximalIdeal C ^ N := by
      intro hcN
      apply hb
      rw [hc, pow_succ']
      exact Ideal.mul_mem_mul (by rw [hm]; exact Ideal.subset_span (by simp)) hcN
    obtain ⟨n, u, hu, hcu⟩ := ih c hcnot
    refine ⟨n + 1, u, hu, ?_⟩
    rw [hc, hcu, pow_succ']
    ring

private theorem factor_nonzero {C : Type*} [CommRing C] [IsLocalRing C]
    [IsNoetherianRing C] (x : C)
    (hm : IsLocalRing.maximalIdeal C = Ideal.span {x}) (b : C) (hb : b ≠ 0) :
    ∃ n : ℕ, ∃ u : C, IsUnit u ∧ b = x ^ n * u := by
  have hex : ∃ N : ℕ, b ∉ IsLocalRing.maximalIdeal C ^ N := by
    by_contra! h
    apply hb
    have hmem : b ∈ ⨅ N : ℕ, IsLocalRing.maximalIdeal C ^ N :=
      by simpa only [Submodule.mem_iInf] using h
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal C)
      (Ideal.IsMaximal.ne_top inferInstance), Submodule.mem_bot] at hmem
  obtain ⟨N, hN⟩ := hex
  exact factor_of_bound x hm N b hN

private theorem dvr_of_regular_maximal_generator {C : Type*} [CommRing C]
    [IsLocalRing C] [IsNoetherianRing C] (x : C) (hreg : IsLeftRegular x)
    (hm : IsLocalRing.maximalIdeal C = Ideal.span {x}) :
    ∃ (_ : IsDomain C), IsDiscreteValuationRing C := by
  have : NoZeroDivisors C := by
    constructor
    intro b c hbc
    by_cases hb : b = 0
    · exact Or.inl hb
    obtain ⟨n, u, hu, hbu⟩ := factor_nonzero x hm b hb
    right
    have hzero : x ^ n * (u * c) = x ^ n * 0 := by
      rw [← mul_assoc, ← hbu, hbc, mul_zero]
    exact hu.mul_right_eq_zero.mp ((hreg.pow n) hzero)
  let : IsDomain C := (isDomain_iff_noZeroDivisors_and_nontrivial C).mpr
    ⟨inferInstance, inferInstance⟩
  refine ⟨inferInstance, ?_⟩
  have hx : x ≠ 0 := by
    intro h
    have : (1 : C) = 0 := hreg (by simp [h])
    exact one_ne_zero this
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨x, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal x hx hm, ?_⟩
  intro b hb
  obtain ⟨n, u, hu, hbu⟩ := factor_nonzero x hm b hb
  obtain ⟨v, hv⟩ := hu
  exact ⟨n, v, by simpa [hv, mul_comm] using hbu.symm⟩

/-- The algebraic part of Stacks Project, Algebra, Tag 032Z, after establishing
Noetherianity, flatness, and reducedness of the quotient. No completion or analytic
unramifiedness is used in this part.
(blueprint: lem-weil-pbc-flat-associated-prime-dvr)

Proof: Put B = A/pA and C = A_q. Write q = Ann(z). Properness forces z nonzero.
Lift z to a in A. Reducedness implies a is outside q, since a in q would give z^2 = 0.
The ideal pA annihilates B, so pA <= q. For b in q, ba is in pA. The image of a is
invertible in C; cancelling it gives qC = pC.

For r outside p, its image in the domain R/p is nonzero and hence regular. Flat base
change makes (R/p) tensor_R A flat over R/p, so multiplication by r on this tensor
product is injective. The canonical tensor-quotient equivalence identifies it with B.
Thus r cannot kill z, and q contracts to p.

The induced algebra R_p -> C is flat, by localization and composition of flat maps.
Transporting the equality qC = pC along the scalar towers identifies the maximal
ideal of C with the extension of the maximal ideal of R_p. Choose a uniformizer x
of the DVR R_p. Its image y in C generates the maximal ideal, and flatness preserves
its regularity.

The ring C is Noetherian and local. Krull intersection says its maximal-ideal powers
have zero intersection. For a nonzero b, choose N with b outside the Nth power. By
induction on N, either b is a unit, or b = y*c and c is outside the preceding power.
This gives b = y^n*u with u a unit. Regularity of y then shows that a product of two
nonzero elements is nonzero, giving IsDomain C. The element y is nonzero by
regularity and nontriviality. Since it generates the maximal ideal, it is irreducible.
The unit-times-power factorization criterion supplies the DVR structure. -/
theorem isDiscreteValuationRing_atPrime_of_flat_reduced_quotient
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Module.Flat R A]
    (p : Ideal R) [p.IsPrime] [IsDomain (Localization.AtPrime p)]
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [IsReduced (A ⧸ p.map (algebraMap R A))]
    (q : Ideal A) [q.IsPrime]
    (hq : ∃ z : A ⧸ p.map (algebraMap R A),
      q = (⊥ : Submodule A (A ⧸ p.map (algebraMap R A))).colon {z}) :
    ∃ (_ : IsDomain (Localization.AtPrime q)),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  let C := Localization.AtPrime q
  let D := Localization.AtPrime p
  have hcontract := associated_quotient_comap p q hq
  have : q.LiesOver p := ⟨hcontract.symm⟩
  let : Algebra D C := Localization.AtPrime.algebraOfLiesOver p q
  have hmap := associated_quotient_map_eq (p.map (algebraMap R A)) q hq
  have hm : IsLocalRing.maximalIdeal C =
      (IsLocalRing.maximalIdeal D).map (algebraMap D C) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, hmap,
      ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R A C, ← IsScalarTower.algebraMap_eq R D C]
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hgen : IsLocalRing.maximalIdeal C = Ideal.span {algebraMap D C x} := by
    rw [hm, hx.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  have hreg : IsLeftRegular (algebraMap D C x) := by
    have h := Module.Flat.isSMulRegular_of_isRegular (M := C)
      (IsRegular.of_ne_zero hx.ne_zero)
    simpa [IsSMulRegular, IsLeftRegular, Algebra.smul_def] using h
  exact dvr_of_regular_maximal_generator (algebraMap D C x) hreg hgen

end AdicCompletion

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Local ideal generator counts from conormal generators

Source: Stacks Project, Tag 00SC, first proof paragraph, and Tag 00DV.
(blueprint: lem-weil-pbc-localized-ideal-conormal-generator-bound).
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace Ideal

/-- Localized conormal generators bound the number of generators of a finite ideal.
Source: Stacks Project, Tag 00SC, first proof paragraph; Tag 00DV.
(blueprint: lem-weil-pbc-localized-ideal-conormal-generator-bound).

Proof: Write P for the ring, I for the finite ideal, q for the prime of P/I,
Q for its inverse image in P, and A=P_Q. Represent each conormal generator as
z_i/s_i with z_i in I/I² and s_i outside q. Lift z_i to f_i in I.
Multiplying each generator by the unit s_i preserves its span. Hence the classes
of the f_i span the localized conormal module. For every z in I, express its
localized class in these generators and clear the finitely many denominators.
The localization equality criterion supplies a further denominator outside q;
lifting it to P gives t outside Q with tz in J+I², where J=(f_i).
Therefore IA is contained in JA+(IA)². Since I is contained in Q, IA is
contained in the maximal ideal of A. Nakayama applied to the finite A-module IA
and its submodule JA gives IA=JA. Thus IA has a generating family of size c,
and its spanFinrank is at most c. If c=0 the span condition says the conormal
localization is zero; the same Nakayama argument yields IA=0. No Noetherian
hypothesis on P is needed beyond finite generation of the specified ideal. -/
theorem spanFinrank_localized_ideal_le_of_conormal_generators
    {P : Type u} [CommRing P] (I : Ideal P) (hI : I.FG)
    (q : PrimeSpectrum (P ⧸ I)) (c : ℕ)
    (g : Fin c → LocalizedModule q.asIdeal.primeCompl I.Cotangent)
    (hspan : Submodule.span (Localization.AtPrime q.asIdeal) (Set.range g) = ⊤) :
    (I.map (algebraMap P
      (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk I))))).spanFinrank ≤ c := by
  classical
  let S := P ⧸ I
  let π := Ideal.Quotient.mk I
  let Q := q.asIdeal.comap π
  let A := Localization.AtPrime Q
  let B := Localization.AtPrime q.asIdeal
  let F := LocalizedModule.mkLinearMap q.asIdeal.primeCompl I.Cotangent
  have hlift (i : Fin c) : ∃ (f : I) (s : q.asIdeal.primeCompl),
      IsLocalizedModule.mk' F (I.toCotangent f) s = g i := by
    obtain ⟨⟨z, s⟩, hz⟩ := IsLocalizedModule.mk'_surjective q.asIdeal.primeCompl F (g i)
    obtain ⟨f, rfl⟩ := I.toCotangent_surjective z
    exact ⟨f, s, hz⟩
  choose f s hfs using hlift
  let v : Fin c → I.Cotangent := fun i ↦ I.toCotangent (f i)
  let N : Submodule S I.Cotangent := Submodule.span S (Set.range v)
  let J : Ideal P := Ideal.span (Set.range (fun i ↦ (f i : P)))
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (f i).property
  have hrep (z : I.Cotangent) (hz : z ∈ N) :
      ∃ a : I, (a : P) ∈ J ∧ I.toCotangent a = z := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨f i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
    | zero => exact ⟨0, J.zero_mem, map_zero _⟩
    | add z w hz hw ihz ihw =>
      obtain ⟨a, ha, rfl⟩ := ihz
      obtain ⟨b, hb, rfl⟩ := ihw
      exact ⟨a + b, J.add_mem ha hb, map_add _ _ _⟩
    | smul r z hz ih =>
      obtain ⟨a, ha, rfl⟩ := ih
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨r • a, J.mul_mem_left r ha, ?_⟩
      rw [map_smul]
      exact (algebraMap_smul S r _).symm
  let N' := N.localized' B q.asIdeal.primeCompl F
  have hN' : N' = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, Submodule.subset_span ⟨i, rfl⟩, s i, hfs i⟩
  have hclear (z : I) : ∃ t : Q.primeCompl, (t : P) * (z : P) ∈ J ⊔ I ^ 2 := by
    have hz : F (I.toCotangent z) ∈ N' := by rw [hN']; trivial
    obtain ⟨w, hw, s, hs⟩ := hz
    have heq : F ((s : S) • I.toCotangent z) = F w := by
      rw [map_smul, ← hs]
      exact IsLocalizedModule.mk'_cancel' F w s
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_iff_exists q.asIdeal.primeCompl F).mp heq
    have hw' : (s' : S) • (s : S) • I.toCotangent z ∈ N :=
      hs' ▸ N.smul_mem (s' : S) hw
    obtain ⟨a, ha, hza⟩ := hrep _ hw'
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((s' * s : q.asIdeal.primeCompl) : S)
    have htQ : t ∈ Q.primeCompl := by
      change π t ∉ q.asIdeal
      rw [ht]
      exact (s' * s).property
    have hclass : I.toCotangent (t • z) = I.toCotangent a := by
      rw [map_smul, ← algebraMap_smul S]
      change π t • I.toCotangent z = _
      rw [ht, Submonoid.coe_mul, mul_smul]
      exact hza.symm
    have hdiff : t * (z : P) - (a : P) ∈ I ^ 2 := I.toCotangent_eq.mp hclass
    refine ⟨⟨t, htQ⟩, ?_⟩
    have h := (J ⊔ I ^ 2).add_mem
      ((show J ≤ J ⊔ I ^ 2 from le_sup_left) ha)
      ((show I ^ 2 ≤ J ⊔ I ^ 2 from le_sup_right) hdiff)
    convert h using 1
    abel
  let IA := I.map (algebraMap P A)
  let JA := J.map (algebraMap P A)
  have hsmall : IA ≤ JA ⊔ IA ^ 2 := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro z hz
    obtain ⟨t, ht⟩ := hclear ⟨z, hz⟩
    have hh := Ideal.mem_map_of_mem (algebraMap P A) ht
    rw [Ideal.map_sup, Ideal.map_pow, map_mul] at hh
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units A t)).mp hh
  have hmax : IA ≤ IsLocalRing.maximalIdeal A := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro z hz
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff A Q z).mpr
    change π z ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
    exact q.asIdeal.zero_mem
  have hle : IA ≤ JA := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (hI.map (algebraMap P A))
      (hmax.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)
    simpa only [pow_two, Ideal.smul_eq_mul] using hsmall
  have hEq : IA = JA := le_antisymm hle (Ideal.map_mono hJI)
  change IA.spanFinrank ≤ c
  rw [hEq]
  change (J.map (algebraMap P A)).spanFinrank ≤ c
  dsimp only [J]
  rw [Ideal.map_span, ← Set.range_comp]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
  have hh := Set.ncard_image_le (s := (Set.univ : Set (Fin c)))
    (f := fun i ↦ algebraMap P A (f i : P)) (Set.finite_univ)
  simpa [Function.comp_def] using hh

end Ideal

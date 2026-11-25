/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Clearing a finite family of local ideal generators

Source: Stacks Project, Algebra, Lemma 00SC (lemma-lci), proof of (2) implies (1).
-/
@[expose] public section
universe u
namespace Ideal
/-- (blueprint: lem-weil-pbc-local-generators-clearing)
Source: Stacks Project, Algebra, Lemma 00SC, proof of (2) implies (1).
Write each local generator as a fraction with numerator in I. The numerators still
span the localized ideal, since their denominators are units. For each member of a
finite generating set of I, membership in that localized span gives a denominator
multiplying it into the numerator span. The product A of these denominators is outside
p, and multiplies every generator, hence all of I, into the numerator span. An empty
finite generating set of I gives the empty product, which is one. When e=0, the
numerator span is zero and the same argument gives A I=0; A need not be one. -/
theorem exists_clearing_of_local_generators
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I p : Ideal R) [p.IsPrime] (e : ℕ) (h : Fin e → Localization.AtPrime p)
    (hgen : Ideal.map (algebraMap R (Localization.AtPrime p)) I =
      Ideal.span (Set.range h)) :
    ∃ (F : Fin e → R) (A : R), A ∉ p ∧ (∀ i, F i ∈ I) ∧
      ∀ x ∈ I, A * x ∈ Ideal.span (Set.range F) := by
  classical
  let L := Localization.AtPrime p
  have hm (i : Fin e) : h i ∈ Ideal.map (algebraMap R L) I := by
    rw [hgen]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose y hy using fun i ↦
    (IsLocalization.mem_map_algebraMap_iff p.primeCompl L).mp (hm i)
  let F : Fin e → R := fun i ↦ (y i).1
  let J := Ideal.span (Set.range F)
  have hFI (i : Fin e) : F i ∈ I := (y i).1.property
  have hIJ : Ideal.map (algebraMap R L) I ≤ Ideal.map (algebraMap R L) J := by
    rw [hgen]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hF : algebraMap R L (F i) ∈ Ideal.map (algebraMap R L) J :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    rw [← hy i] at hF
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units L (y i).2)).mp
      (by simpa only [mul_comm] using hF)
  have hx (x : R) (hx : x ∈ I) : ∃ v : p.primeCompl, v.val * x ∈ J := by
    have hx' := hIJ (Ideal.mem_map_of_mem (algebraMap R L) hx)
    obtain ⟨v, hv, hvx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl L J x).mp hx'
    exact ⟨⟨v, hv⟩, hvx⟩
  obtain ⟨t, ht⟩ := (isNoetherianRing_iff_ideal_fg R).mp inferInstance I
  choose v hv using fun x : t ↦ hx x.val (by rw [← ht]; exact Ideal.subset_span x.property)
  let A : R := ∏ x : t, (v x).val
  have hA : A ∉ p := p.primeCompl.prod_mem fun x _ ↦ (v x).property
  refine ⟨F, A, hA, hFI, ?_⟩
  have hgenA : ∀ x ∈ t, A * x ∈ J := by
    intro x hxt
    have hd : (v ⟨x, hxt⟩).val ∣ A :=
      Finset.dvd_prod_of_mem (fun x : t ↦ (v x).val) (Finset.mem_univ (⟨x, hxt⟩ : t))
    obtain ⟨c, hc⟩ := hd
    rw [hc, mul_assoc, mul_left_comm]
    exact J.mul_mem_left c (hv ⟨x, hxt⟩)
  intro x hxI
  rw [← ht] at hxI
  induction hxI using Submodule.span_induction with
  | mem x hx => exact hgenA x hx
  | zero => simp
  | add x y hx hy hx' hy' => simpa [mul_add] using J.add_mem hx' hy'
  | smul a x hx hx' => simpa [mul_left_comm A a] using J.mul_mem_left a hx'
end Ideal

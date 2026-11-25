/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SyntomicPresentationLocalKernel

@[expose] public section
universe u v
namespace Algebra

private theorem exists_multiplier_of_localized_le
    {A : Type*} [CommRing A] (M : Submonoid A) (L : Type*)
    [CommRing L] [Algebra A L] [IsLocalization M L]
    (I J : Ideal A) (hfg : I.FG)
    (hle : I.map (algebraMap A L) ≤ J.map (algebraMap A L)) :
    ∃ s ∈ M, ∀ x ∈ I, s * x ∈ J := by
  classical
  have hkill : ∀ x ∈ I, ∃ s ∈ M, s * x ∈ J := by
    intro x hx
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff M L J x).mp
      (hle (Ideal.mem_map_of_mem _ hx))
  have hfinite : ∀ t : Finset A, (∀ x ∈ t, x ∈ I) →
      ∃ s ∈ M, ∀ x ∈ t, s * x ∈ J := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨1, M.one_mem, by simp⟩
    | @insert x t hxt ih =>
      intro ht
      obtain ⟨s, hs, hst⟩ := ih (fun y hy ↦ ht y (Finset.mem_insert_of_mem hy))
      obtain ⟨r, hr, hrx⟩ := hkill x (ht x (Finset.mem_insert_self _ _))
      refine ⟨s * r, M.mul_mem hs hr, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa only [mul_assoc] using J.mul_mem_left s hrx
      · simpa only [mul_assoc, mul_left_comm s r y] using J.mul_mem_left r (hst y hy)
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨s, hs, hst⟩ := hfinite t (fun x hx ↦ by
    rw [← ht]
    exact Submodule.subset_span hx)
  refine ⟨s, hs, ?_⟩
  intro x hx
  rw [← ht] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hst y hy
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [mul_add] using J.add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [smul_eq_mul, mul_left_comm s a x] using J.mul_mem_left a ih

/-- Core presentation and localization comparison underlying the syntomic equation-count theorem.
Source: Stacks Project, Algebra, Tag 00SY, proof of (3) ⇒ (2),
presentation, Nakayama and flatness steps.
(blueprint: lem-weil-pbc-syntomic-equation-count-comparison-core).
The proof constructs a finite polynomial presentation, chooses the conormal generators, and uses
flatness plus Nakayama to obtain an isomorphism after inverting an element outside the prime. -/
theorem exists_equationCount_comparison_core
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (hfp : FinitePresentation R S)
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      let T := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)
      ∃ (π : T →ₐ[R] S) (u : T),
        Function.Surjective π ∧ π u ∉ q.asIdeal ∧
        Function.Bijective
          (IsLocalization.Away.mapₐ (Localization.Away u) (Localization.Away (π u)) π u) ∧
        c ≤ n := by
  obtain ⟨n, φ, hφ, hfg⟩ := hfp.out
  obtain ⟨c, f, hcn, hJ, hlocal⟩ :=
    exists_bounded_local_kernel_generators q n φ hφ hfg hflat hci
  let P := MvPolynomial (Fin n) R
  let I : Ideal P := RingHom.ker φ.toRingHom
  let J : Ideal P := Ideal.span (Set.range f)
  let p : Ideal P := q.asIdeal.comap φ.toRingHom
  obtain ⟨s, hs, hkill⟩ := exists_multiplier_of_localized_le p.primeCompl
    (Localization.AtPrime p) I J hfg (le_of_eq hlocal.symm)
  let T := P ⧸ J
  let π : T →ₐ[R] S := Ideal.Quotient.liftₐ J φ (fun x hx ↦ hJ hx)
  let u : T := Ideal.Quotient.mk J s
  have hπ : ∀ x : P, π (Ideal.Quotient.mk J x) = φ x := by
    intro x
    rfl
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨Ideal.Quotient.mk J x, hπ x⟩
  refine ⟨n, c, f, π, u, hsurj, ?_, ?_, hcn⟩
  · exact hs
  · constructor
    · change Function.Injective (IsLocalization.Away.map
        (Localization.Away u) (Localization.Away (π u)) π.toRingHom u)
      apply (IsLocalization.Away.map_injective_iff
        (Localization.Away (π u)) π.toRingHom u).mpr
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨1, ?_⟩
      rw [pow_one]
      change Ideal.Quotient.mk J s * Ideal.Quotient.mk J a = 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hkill a hx
    · exact IsLocalization.Away.mapₐ_surjective_of_surjective u hsurj
end Algebra

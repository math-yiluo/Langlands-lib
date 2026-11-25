/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.AlgebraicGeometry.NormalLocusOpen

@[expose] public section

universe u v

/-- A birational integral algebra has the same normal principal open as its base.
Source: Stacks Project, Algebra, Tag 0333, reverse implication, first paragraph. -/
private theorem normal_away_intermediate (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (f : A) (hf : f ≠ 0) [IsIntegrallyClosed (Localization.Away f)]
    (C : Subalgebra A K) (hC : C ≤ integralClosure A K) :
    IsIntegrallyClosed (Localization.Away (algebraMap A C f)) := by
  let M := Submonoid.powers f
  have hM : M ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  let T := Localization.subalgebra K M hM
  let : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  let eA : Localization.Away f ≃ₐ[A] T :=
    IsLocalization.algEquiv M (Localization.Away f) T
  have : IsIntegrallyClosed T := IsIntegrallyClosed.of_equiv eA.toRingEquiv
  have hCT : C ≤ T := by
    intro x hx
    have hi : IsIntegral A x := hC hx
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (R := T) (K := K) hi.tower_top
    exact ht ▸ t.property
  let : Algebra C T := (Subalgebra.inclusion hCT).toRingHom.toAlgebra
  let : IsScalarTower A C T := IsScalarTower.of_algebraMap_eq' (by ext r; rfl)
  let g : C := algebraMap A C f
  let : IsLocalization.Away g T := by
    refine IsLocalization.Away.mk g ?_ ?_ ?_
    · change IsUnit (algebraMap A T f)
      exact IsLocalization.Away.algebraMap_isUnit f
    · intro t
      obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj f t
      exact ⟨n, algebraMap A C r, hr⟩
    · intro c d h
      have hcd : c = d := Subtype.ext (congrArg (fun z : T ↦ (z : K)) h)
      exact ⟨0, by simp [hcd]⟩
  let eC : T ≃ₐ[C] Localization.Away g :=
    IsLocalization.algEquiv (Submonoid.powers g) T (Localization.Away g)
  exact IsIntegrallyClosed.of_equiv eC.toRingEquiv

/-- A finite family whose normal fibers cover every prime of the base.
Source: Stacks Project, Algebra, Tag 0333, reverse implication, paragraphs defining
`Z_C` and extracting a finite collection; Tag 0332 for openness of the normal locus.
(blueprint: lem-weil-pbc-finite-normal-cover-family)

Proof: Choose the nonzero f of hAway. The local criterion for normality makes A_f
normal. For each finite intermediate C contained in the integral closure, C_f is
integral over A_f inside their common fraction field K, hence C_f = A_f. The ring C
is a Noetherian domain and its normal locus is open by Tag 0332. Since C is integral
over A, Spec C -> Spec A is closed, so the image Z_C of the non-normal locus is closed.
For each maximal m, hLocal supplies a C for which m is outside Z_C. Each prime p is
contained in a maximal m. If p belonged to that Z_C, specialization-closedness would
put m in Z_C too. Therefore the opens Spec A \ Z_C cover Spec A. Quasi-compactness
extracts finitely many C, forming s. Every member satisfies the original finiteness
and containment conditions. For any prime p, membership in one of these opens says
exactly that every prime of the corresponding C contracting to p has normal
localization, which is the final clause below. -/
theorem exists_finite_normal_cover_family (A : Type u) (K : Type v)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hAway : ∃ f : A, f ≠ 0 ∧
      ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hLocal : ∀ (m : Ideal A) [m.IsMaximal],
      ∃ B : Subalgebra A K, B ≤ integralClosure A K ∧ Module.Finite A B ∧
        ∀ (q : Ideal B) [q.IsPrime], Ideal.comap (algebraMap A B) q = m →
          IsIntegrallyClosed (Localization.AtPrime q)) :
    ∃ s : Finset (Subalgebra A K),
      (∀ C ∈ s, C ≤ integralClosure A K ∧ Module.Finite A C) ∧
      ∀ (p : Ideal A) [p.IsPrime], ∃ C ∈ s,
        ∀ (q : Ideal C) [q.IsPrime], Ideal.comap (algebraMap A C) q = p →
          IsIntegrallyClosed (Localization.AtPrime q) := by
  classical
  obtain ⟨f, hf, hn⟩ := hAway
  have : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  have : IsIntegrallyClosed (Localization.Away f) :=
    IsIntegrallyClosed.of_localization_maximal (fun p _ _ ↦ (hn p).2)
  let I := {C : Subalgebra A K // C ≤ integralClosure A K ∧ Module.Finite A C}
  let N (C : I) : Set (PrimeSpectrum C.1) :=
    {q | IsDomain (Localization.AtPrime q.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime q.asIdeal)}
  let Z (C : I) : Set (PrimeSpectrum A) :=
    PrimeSpectrum.comap (algebraMap A C.1) '' (N C)ᶜ
  have hZ (C : I) : IsClosed (Z C) := by
    have : Module.Finite A C.1 := C.2.2
    have : IsNoetherianRing C.1 := IsNoetherianRing.of_finite A C.1
    have hg : algebraMap A C.1 f ≠ 0 := by
      intro h
      apply hf
      apply IsFractionRing.injective A K
      have := congrArg (fun z : C.1 ↦ (z : K)) h
      simpa only [Subalgebra.coe_algebraMap, ZeroMemClass.coe_zero, map_zero] using this
    have hnC := normal_away_intermediate A K f hf C.1 C.2.1
    have hopen := AlgebraicGeometry.normal_locus_isOpen (algebraMap A C.1 f) hg
      ⟨IsLocalization.Away.isDomain _ hg, hnC⟩
    exact PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap A C.1)
      (Algebra.IsIntegral.isIntegral (R := A)) _ hopen.isClosed_compl
  have hcover : Set.univ ⊆ ⋃ C : I, (Z C)ᶜ := by
    intro p _
    obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
    have : m.IsMaximal := hm
    obtain ⟨C, hC, hfin, hnormal⟩ := hLocal m
    let i : I := ⟨C, hC, hfin⟩
    have hmZ : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∉ Z i := by
      rintro ⟨q, hq, hqm⟩
      apply hq
      refine ⟨inferInstance, hnormal q.asIdeal ?_⟩
      exact congrArg PrimeSpectrum.asIdeal hqm
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    intro hpZ
    apply hmZ
    exact (hZ i).stableUnderSpecialization
      ((PrimeSpectrum.le_iff_specializes p ⟨m, hm.isPrime⟩).mp hpm) hpZ
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun C : I ↦ (Z C)ᶜ) (fun C ↦ (hZ C).isOpen_compl) hcover
  refine ⟨s.image (fun C ↦ C.1), ?_, ?_⟩
  · intro C hC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    exact i.2
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ (⟨p, hp⟩ : PrimeSpectrum A)))
    obtain ⟨his, hip⟩ := Set.mem_iUnion.mp hi
    refine ⟨i.1, Finset.mem_image.mpr ⟨i, his, rfl⟩, ?_⟩
    intro q hq hqp
    by_contra hnormal
    apply hip
    refine ⟨⟨q, hq⟩, ?_, ?_⟩
    · exact fun h ↦ hnormal h.2
    · exact PrimeSpectrum.ext hqp


/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.Tactic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The Bertini–Noether theorem

Let `A` be a domain and `P` a multivariate polynomial over `A` which is absolutely irreducible
over the fraction field of `A`. Then there is a nonzero `a ∈ A` such that for every ring map
`φ : A → k` to a field with `φ a ≠ 0`, the polynomial `φ(P)` is irreducible of the same total
degree. This is the core of the generic geometric irreducibility of fibres (Stacks `0557`,
`0559`).

The proof is by Chevalley's theorem: the locus of primes over which `P` factors with factors of
smaller total degree is the image of the spectrum of the finitely presented algebra of
coefficients of such factorizations, hence constructible, and it misses the generic point by the
Nullstellensatz and absolute irreducibility.

## Main statements

- `MvPolynomial.bertini_noether`: the Bertini–Noether theorem.

## References

- Stacks Project, Tag `0557`, <https://stacks.math.columbia.edu/tag/0557>
-/

@[expose] public section

open MvPolynomial Topology

namespace BertiniNoether

variable {n d : ℕ}

/-- The monomial with exponent vector `e`. -/
private noncomputable def mono (e : Fin n → Fin d) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (e i : ℕ)

private lemma mono_injective : Function.Injective (mono (n := n) (d := d)) := by
  intro e e' h
  funext i
  have := congrArg (fun m : Fin n →₀ ℕ ↦ m i) h
  simpa [mono, Fin.ext_iff] using this

/-- Indices of monomials of total degree `< d`. -/
private noncomputable def lowMonos (n d : ℕ) : Finset (Fin n → Fin d) :=
  Finset.univ.filter fun e ↦ (mono e).sum (fun _ k ↦ k) < d

variable (A : Type*) [CommRing A]

/-- The generic polynomial of total degree `< d` with coefficients the variables `X (b, e)`. -/
private noncomputable def generic (n d : ℕ) (b : Bool) :
    MvPolynomial (Fin n) (MvPolynomial (Bool × (Fin n → Fin d)) A) :=
  ∑ e ∈ lowMonos n d, monomial (mono e) (X (b, e))

/-- The ideal of the "coefficient scheme" of factorizations `P = F * G`. -/
private noncomputable def factorIdeal (P : MvPolynomial (Fin n) A) (d : ℕ) :
    Ideal (MvPolynomial (Bool × (Fin n → Fin d)) A) :=
  Ideal.span ((generic A n d false * generic A n d true - map C P).coeffs : Set _)

variable {A}

private lemma coeff_generic (b : Bool) (m : Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (generic A n d b) m =
      if h : ∃ e ∈ lowMonos n d, mono e = m then X (b, h.choose) else 0 := by
  classical
  simp only [generic, coeff_sum, coeff_monomial]
  split_ifs with h
  · obtain ⟨he, hm⟩ := h.choose_spec
    rw [Finset.sum_eq_single h.choose]
    · simp [hm]
    · intro e _ hne
      rw [ite_eq_right]
      intro h'
      exact hne (mono_injective (h'.trans hm.symm))
    · intro hn
      exact absurd he hn
  · push Not at h
    exact Finset.sum_eq_zero fun e he ↦ by simp [h e he]


private lemma totalDegree_generic_lt (hd : 0 < d) (b : Bool) :
    totalDegree (generic A n d b) < d := by
  rw [totalDegree, Finset.sup_lt_iff (by simpa using hd)]
  intro m hm
  rw [mem_support_iff, coeff_generic] at hm
  split_ifs at hm with h
  · obtain ⟨he, hme⟩ := h.choose_spec
    rw [← hme]
    exact (Finset.mem_filter.mp he).2
  · exact absurd rfl hm

variable {E : Type*} [CommRing E]

/-- A point of the coefficient scheme gives a factorization. -/
private lemma map_generic_mul_eq (P : MvPolynomial (Fin n) A)
    (ψ : MvPolynomial (Bool × (Fin n → Fin d)) A →+* E) (hψ : factorIdeal A P d ≤ RingHom.ker ψ) :
    map ψ (generic A n d false) * map ψ (generic A n d true) = map (ψ.comp C) P := by
  have h : map ψ (generic A n d false * generic A n d true - map C P) = 0 := by
    ext m
    rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_cases hm :
        AddMonoidAlgebra.coeff (generic A n d false * generic A n d true - map C P) m = 0
    · rw [hm, map_zero]
    · exact hψ (Ideal.subset_span (coeff_mem_coeffs m hm))
  rwa [RingHom.map_sub, RingHom.map_mul, map_map, sub_eq_zero] at h

/-- A factorization gives a point of the coefficient scheme. -/
private lemma exists_hom_of_mul_eq (P : MvPolynomial (Fin n) A) (φ : A →+* E)
    (F G : MvPolynomial (Fin n) E) (hF : totalDegree F < d) (hG : totalDegree G < d)
    (hFG : F * G = map φ P) :
    ∃ ψ : MvPolynomial (Bool × (Fin n → Fin d)) A →+* E,
      ψ.comp C = φ ∧ factorIdeal A P d ≤ RingHom.ker ψ := by
  classical
  set ψ : MvPolynomial (Bool × (Fin n → Fin d)) A →+* E :=
    eval₂Hom φ fun x ↦ AddMonoidAlgebra.coeff (if x.1 then G else F) (mono x.2) with hψdef
  have key (b : Bool) (H : MvPolynomial (Fin n) E) (hH : totalDegree H < d)
      (hb : H = if b then G else F) : map ψ (generic A n d b) = H := by
    ext m
    rw [coeff_map, coeff_generic]
    split_ifs with h
    · obtain ⟨-, hme⟩ := h.choose_spec
      simp [ψ, hme, hb]
    · rw [map_zero, eq_comm]
      by_contra hm
      have hdeg : m.sum (fun _ k ↦ k) < d :=
        lt_of_le_of_lt (le_totalDegree (mem_support_iff.mpr hm)) hH
      refine h ⟨fun i ↦ ⟨m i, lt_of_le_of_lt (Finsupp.le_degree i m) hdeg⟩, ?_, ?_⟩
      · simp only [lowMonos, Finset.mem_filter, Finset.mem_univ, true_and]
        convert hdeg
        ext i
        simp [mono]
      · ext i
        simp [mono]
  refine ⟨ψ, by ext; simp [ψ], ?_⟩
  rw [factorIdeal, Ideal.span_le]
  intro c hc
  obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
  rw [SetLike.mem_coe, RingHom.mem_ker, ← coeff_map, RingHom.map_sub, RingHom.map_mul,
    key false F hF (by simp), key true G hG (by simp), map_map]
  have : ψ.comp C = φ := by ext; simp [ψ]
  rw [this, hFG, sub_self, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]


/-- A constructible subset of `Spec R` (`R` a domain) not containing the generic point is
contained in `V(a)` for some `a ≠ 0`. -/
lemma exists_ne_zero_forall_mem_of_isConstructible {R : Type*} [CommRing R] [IsDomain R]
    {Z : Set (PrimeSpectrum R)} (hZ : IsConstructible Z)
    (h : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∉ Z) :
    ∃ a : R, a ≠ 0 ∧ ∀ p ∈ Z, a ∈ p.asIdeal := by
  obtain ⟨S, hS⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hZ.compl
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ S.toSet := hS ▸ h
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion] at hmem
  obtain ⟨C, hC, hmem⟩ := hmem
  simp only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
    Ideal.mem_bot, Set.range_subset_iff] at hmem
  refine ⟨C.f, hmem.2, fun p hp ↦ ?_⟩
  by_contra hf
  have : p ∈ S.toSet := by
    simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion]
    refine ⟨C, hC, ?_⟩
    simp only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
      Set.range_subset_iff, hmem.1]
    simp [hf]
  rw [hS] at this
  exact this hp

/-- The coefficient algebra of factorizations `P = F * G` with `deg F, deg G < d`. -/
private abbrev FactorAlg (P : MvPolynomial (Fin n) A) (d : ℕ) :=
  MvPolynomial (Bool × (Fin n → Fin d)) A ⧸ factorIdeal A P d

private lemma isConstructible_range_factorAlg (P : MvPolynomial (Fin n) A) (d : ℕ) :
    IsConstructible (Set.range (PrimeSpectrum.comap (algebraMap A (FactorAlg P d)))) := by
  refine PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr ?_)
  exact Algebra.FinitePresentation.quotient ⟨_, rfl⟩

/-- Every factorization over a field gives a point of the coefficient scheme. -/
private lemma ker_mem_range_factorAlg (P : MvPolynomial (Fin n) A) {k : Type*} [Field k]
    (φ : A →+* k)
    (F G : MvPolynomial (Fin n) k) (hF : totalDegree F < d) (hG : totalDegree G < d)
    (hFG : F * G = map φ P) :
    (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum A) ∈
      Set.range (PrimeSpectrum.comap (algebraMap A (FactorAlg P d))) := by
  obtain ⟨ψ, hψC, hψI⟩ := exists_hom_of_mul_eq P φ F G hF hG hFG
  let χ : FactorAlg P d →+* k := Ideal.Quotient.lift _ ψ hψI
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, ?_⟩
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker, ← hψC,
    RingHom.coe_comp, Function.comp_apply, χ]
  exact Iff.rfl


lemma totalDegree_map_of_injective {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {f : R →+* S} (hf : Function.Injective f) (p : MvPolynomial σ R) :
    totalDegree (map f p) = totalDegree p := by
  simp [totalDegree, support_map_of_injective p hf]

private lemma totalDegree_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) :
    totalDegree (map f p) ≤ totalDegree p :=
  Finset.sup_mono (support_map_subset f p)

private lemma totalDegree_pos_of_irreducible {σ L : Type*} [Field L] {Q : MvPolynomial σ L}
    (hQ : Irreducible Q) : 0 < totalDegree Q := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [totalDegree_eq_zero_iff_eq_C.mp h] at hQ
  by_cases hr : AddMonoidAlgebra.coeff Q 0 = 0
  · rw [hr, map_zero] at hQ
    exact hQ.ne_zero rfl
  · exact hQ.not_isUnit ((isUnit_iff_eq_C_of_isReduced).mpr
      ⟨_, isUnit_iff_ne_zero.mpr hr, rfl⟩)

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- The generic point is not in the reducible locus if `P` is absolutely irreducible. -/
private lemma bot_notMem_range_factorAlg [IsDomain A] (P : MvPolynomial (Fin n) A)
    (K L : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [IsAlgClosed L]
    [Algebra K L] (hP : Irreducible (map ((algebraMap K L).comp (algebraMap A K)) P)) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉
      Set.range (PrimeSpectrum.comap (algebraMap A (FactorAlg P (totalDegree P)))) := by
  set d := totalDegree P with hd
  set I := factorIdeal A P d
  rintro ⟨q, hq⟩
  have hq' : q.asIdeal.comap (algebraMap A (FactorAlg P d)) = ⊥ := congrArg (·.asIdeal) hq
  set q' := q.asIdeal.comap (Ideal.Quotient.mk I)
  have hIq : I ≤ q' := fun x hx ↦ by
    change Ideal.Quotient.mk I x ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.asIdeal.zero_mem
  have hdisj : Disjoint (((nonZeroDivisors A).map
      (C : A →+* MvPolynomial (Bool × (Fin n → Fin d)) A)) :
        Set (MvPolynomial (Bool × (Fin n → Fin d)) A))
      (SetLike.coe q') := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hx
    have : a ∈ q.asIdeal.comap (algebraMap A (FactorAlg P d)) := hx
    rw [hq', Ideal.mem_bot] at this
    exact nonZeroDivisors.coe_ne_zero ⟨a, ha⟩ this
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors A).map (C : A →+* MvPolynomial (Bool × (Fin n → Fin d)) A))
    (MvPolynomial (Bool × (Fin n → Fin d)) K) q' inferInstance hdisj
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hprime.ne_top
  let := Ideal.Quotient.field M
  have : Module.Finite K (MvPolynomial (Bool × (Fin n → Fin d)) K ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  let lift : (MvPolynomial (Bool × (Fin n → Fin d)) K ⧸ M) →ₐ[K] L := IsAlgClosed.lift
  let χ : MvPolynomial (Bool × (Fin n → Fin d)) A →+* L :=
    lift.toRingHom.comp ((Ideal.Quotient.mk M).comp (algebraMap _ _))
  have hχI : I ≤ RingHom.ker χ := fun x hx ↦ by
    have : algebraMap _ (MvPolynomial (Bool × (Fin n → Fin d)) K) x ∈ M :=
      hJM (Ideal.mem_map_of_mem _ (hIq hx))
    rw [algebraMap_def] at this
    simp [χ, Ideal.Quotient.eq_zero_iff_mem.mpr this]
  have hχC : χ.comp C = (algebraMap K L).comp (algebraMap A K) := by
    ext a
    simp only [χ, RingHom.comp_apply, algebraMap_def, map_C]
    exact lift.commutes (algebraMap A K a)
  have hFG := map_generic_mul_eq P χ hχI
  rw [hχC] at hFG
  have hinj : Function.Injective ((algebraMap K L).comp (algebraMap A K)) :=
    (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hdeg := totalDegree_map_of_injective hinj P
  have hd0 : 0 < d := by
    rw [hd, ← hdeg]
    exact totalDegree_pos_of_irreducible hP
  have hlt (b : Bool) : totalDegree (map χ (generic A n d b)) < d :=
    by
    have h1 := totalDegree_generic_lt (A := A) (n := n) hd0 b
    have h2 := totalDegree_map_le χ (generic A n d b)
    exact h2.trans_lt h1
  have hne : map ((algebraMap K L).comp (algebraMap A K)) P ≠ 0 := hP.ne_zero
  rw [← hFG] at hne
  rcases hP.isUnit_or_isUnit hFG.symm with h | h
  · have h0 := ((isUnit_iff_totalDegree_of_isReduced).mp h).2
    have := totalDegree_mul_of_isDomain (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)
    rw [hFG, hdeg, h0, zero_add] at this
    exact (hlt true).ne this.symm
  · have h0 := ((isUnit_iff_totalDegree_of_isReduced).mp h).2
    have := totalDegree_mul_of_isDomain (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)
    rw [hFG, hdeg, h0, add_zero] at this
    exact (hlt false).ne this.symm


private lemma totalDegree_pos_of_not_isUnit {σ k : Type*} [Field k] {F : MvPolynomial σ k}
    (hF : ¬IsUnit F) (hF0 : F ≠ 0) : 0 < totalDegree F := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [totalDegree_eq_zero_iff_eq_C.mp h] at hF hF0
  refine hF ((isUnit_iff_eq_C_of_isReduced).mpr ⟨_, isUnit_iff_ne_zero.mpr ?_, rfl⟩)
  rintro h0
  rw [h0, map_zero] at hF0
  exact hF0 rfl

end BertiniNoether

namespace MvPolynomial

open BertiniNoether

variable {n : ℕ} {A : Type*} [CommRing A]

universe v in
/-- **Bertini–Noether** (core of Stacks 0557). If `P ∈ A[X₁,…,Xₙ]` (`A` a domain with fraction
field `K`) is irreducible over an algebraically closed field `L ⊇ K`, then there is `a ≠ 0` in `A`
such that for every ring map `φ : A → k` to a field with `φ a ≠ 0`, `φ(P)` is irreducible of the
same total degree. -/
theorem bertini_noether [IsDomain A] (P : MvPolynomial (Fin n) A)
    (K L : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [IsAlgClosed L]
    [Algebra K L] (hP : Irreducible (map ((algebraMap K L).comp (algebraMap A K)) P)) :
    ∃ a : A, a ≠ 0 ∧ ∀ {k : Type v} [Field k] (φ : A →+* k), φ a ≠ 0 →
      Irreducible (map φ P) ∧ totalDegree (map φ P) = totalDegree P := by
  set d := totalDegree P with hd
  obtain ⟨a₀, ha₀, ha₀Z⟩ := exists_ne_zero_forall_mem_of_isConstructible
    (isConstructible_range_factorAlg P d) (bot_notMem_range_factorAlg P K L hP)
  have hinj : Function.Injective ((algebraMap K L).comp (algebraMap A K)) :=
    (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hd0 : 0 < d := by
    rw [hd, ← totalDegree_map_of_injective hinj P]
    exact totalDegree_pos_of_irreducible hP
  have hP0 : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    rintro rfl
    exact hP.ne_zero (map_zero _)
  obtain ⟨m₀, hm₀, hm₀d⟩ := Finset.exists_mem_eq_sup P.support hP0 fun s ↦ s.sum fun _ e ↦ e
  refine ⟨a₀ * AddMonoidAlgebra.coeff P m₀, mul_ne_zero ha₀ (mem_support_iff.mp hm₀),
    fun {k} _ φ hφ ↦ ?_⟩
  rw [map_mul] at hφ
  have hdeg : totalDegree (map φ P) = d := by
    refine le_antisymm (totalDegree_map_le φ P) ?_
    rw [hd, totalDegree, hm₀d]
    exact le_totalDegree (mem_support_iff.mpr (by rw [coeff_map]; exact right_ne_zero_of_mul hφ))
  refine ⟨irreducible_iff.mpr ⟨fun hu ↦ ?_, fun F G hFG ↦ ?_⟩, hdeg⟩
  · have := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  · by_contra h
    rw [not_or] at h
    have hne : map φ P ≠ 0 := by
      intro h0
      rw [h0, totalDegree_zero] at hdeg
      omega
    rw [hFG] at hne
    have hF := totalDegree_pos_of_not_isUnit h.1 (left_ne_zero_of_mul hne)
    have hG := totalDegree_pos_of_not_isUnit h.2 (right_ne_zero_of_mul hne)
    have hsum := totalDegree_mul_of_isDomain (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)
    rw [← hFG, hdeg] at hsum
    have hmem := ker_mem_range_factorAlg (d := d) P φ F G (by omega) (by omega) hFG.symm
    exact left_ne_zero_of_mul hφ (ha₀Z _ hmem)

end MvPolynomial

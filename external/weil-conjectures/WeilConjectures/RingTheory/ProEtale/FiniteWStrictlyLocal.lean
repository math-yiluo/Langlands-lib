/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting
public import WeilConjectures.RingTheory.FiniteLocalHenselian
public import WeilConjectures.RingTheory.ProEtale.IntegralLocal
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Finite algebras over w-strictly local rings

A module-finite algebra `B` over a w-strictly local ring `A` is again w-strictly local
(compare Stacks 0966, 0967 and Bhatt–Scholze, *The pro-étale topology for schemes*, §2.2).

The key input is that, over a henselian local ring `R`, every prime of a finite `R`-algebra
lying over the maximal ideal is isolated by an idempotent
(`HenselianLocalRing.exists_isIdempotentElem_notMem`). Applied to the localization
`A_n ⊗_A B` at a maximal ideal `n` of `A`, this shows that every prime of `B` lies below a
unique maximal ideal, and that the local ring of `B` at a maximal ideal `m` is a quotient
of `A_n ⊗_A B` by an idempotent, hence finite over the strictly henselian local ring `A_n`
and so strictly henselian.

## Main results

- `HenselianLocalRing.exists_isIdempotentElem_notMem`
- `IsWStrictlyLocalRing.of_finite`: a module-finite algebra over a w-strictly local ring is
  w-strictly local.
-/

@[expose] public section

universe u

open IsLocalRing

namespace HenselianLocalRing

variable {R C : Type u} [CommRing R] [HenselianLocalRing R] [CommRing C] [Algebra R C]
  [Module.Finite R C]

/-- In a module-finite algebra `C` over a henselian local ring `R`, every prime `P` lying over
the maximal ideal of `R` is isolated by an idempotent: there is an idempotent `ε ∉ P` lying in
every other prime over the maximal ideal. -/
theorem exists_isIdempotentElem_notMem (P : Ideal C) [P.IsPrime]
    (hP : P.comap (algebraMap R C) = maximalIdeal R) :
    ∃ ε : C, IsIdempotentElem ε ∧ ε ∉ P ∧ ∀ P' : Ideal C, P'.IsPrime →
      P'.comap (algebraMap R C) = maximalIdeal R → P' ≠ P → ε ∈ P' := by
  classical
  set I := (maximalIdeal R).map (algebraMap R C) with hI
  have hIP : ∀ P' : Ideal C, P'.comap (algebraMap R C) = maximalIdeal R → I ≤ P' :=
    fun P' h ↦ Ideal.map_le_iff_le_comap.2 h.ge
  have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  -- Every prime of `C ⧸ I` lies over the maximal ideal of `R`.
  have hover : ∀ Q : PrimeSpectrum (C ⧸ I),
      (Q.asIdeal.comap (Ideal.Quotient.mk I)).comap (algebraMap R C) = maximalIdeal R := by
    intro Q
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Ideal.map_le_iff_le_comap, ← hI]
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  -- Hence every prime of `C ⧸ I` is maximal.
  have hmax : ∀ Q : PrimeSpectrum (C ⧸ I), Q.asIdeal.IsMaximal := by
    intro Q
    have : (Q.asIdeal.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) _
        (by rw [Ideal.under_def, hover Q]; infer_instance)
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hmk this with h | h
    · rw [Ideal.map_comap_of_surjective _ hmk] at h
      exact absurd h (Ideal.IsPrime.ne_top inferInstance)
    · rwa [Ideal.map_comap_of_surjective _ hmk] at h
  -- The spectrum of `C ⧸ I` is finite and `T₁`, hence discrete.
  let p₀ : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
  have : Finite (PrimeSpectrum (C ⧸ I)) := by
    have hfin := Algebra.QuasiFinite.finite_comap_preimage_singleton (R := R) (S := C) p₀
    have := hfin.to_subtype
    exact Finite.of_injective (β := ↥(PrimeSpectrum.comap (algebraMap R C) ⁻¹' {p₀}))
      (fun Q ↦ ⟨PrimeSpectrum.comap (Ideal.Quotient.mk I) Q, PrimeSpectrum.ext (hover Q)⟩)
      fun Q Q' h ↦ PrimeSpectrum.comap_injective_of_surjective _ hmk (congrArg Subtype.val h)
  have : T1Space (PrimeSpectrum (C ⧸ I)) :=
    ⟨fun Q ↦ (PrimeSpectrum.isClosed_singleton_iff_isMaximal Q).2 (hmax Q)⟩
  have : DiscreteTopology (PrimeSpectrum (C ⧸ I)) := inferInstance
  have hPI : I ≤ P := hIP P hP
  let Pbar : PrimeSpectrum (C ⧸ I) :=
    ⟨P.map (Ideal.Quotient.mk I), Ideal.map_isPrime_of_surjective hmk (by rwa [Ideal.mk_ker])⟩
  let s₀ : TopologicalSpace.Clopens (PrimeSpectrum (C ⧸ I)) := ⟨{Pbar}, isClopen_discrete _⟩
  let e₀ := (PrimeSpectrum.isIdempotentElemEquivClopens (R := C ⧸ I)).symm s₀
  have he₀ : (PrimeSpectrum.basicOpen e₀.1 : Set (PrimeSpectrum (C ⧸ I))) = {Pbar} :=
    congrArg (fun U : TopologicalSpace.Opens _ ↦ (U : Set (PrimeSpectrum (C ⧸ I))))
      (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm s₀)
  obtain ⟨ε, ⟨hε, hεe⟩, -⟩ :=
    Algebra.existsUnique_isIdempotentElem_of_henselianRing R (maximalIdeal R) C e₀.1 e₀.2
  -- Membership of `ε` in a prime over the maximal ideal is read off in `C ⧸ I`.
  have hmem : ∀ P' : Ideal C, P'.IsPrime → I ≤ P' →
      (ε ∈ P' ↔ e₀.1 ∈ P'.map (Ideal.Quotient.mk I)) := by
    intro P' _ hP'
    rw [← hεe, Ideal.mem_quotient_iff_mem hP']
  refine ⟨ε, hε, ?_, fun P' _ hP'm hne ↦ ?_⟩
  · rw [hmem P inferInstance hPI]
    have : Pbar ∈ (PrimeSpectrum.basicOpen e₀.1 : Set (PrimeSpectrum (C ⧸ I))) := by
      rw [he₀]; rfl
    exact this
  · have hP'I := hIP P' hP'm
    rw [hmem P' inferInstance hP'I]
    let P'bar : PrimeSpectrum (C ⧸ I) :=
      ⟨P'.map (Ideal.Quotient.mk I), Ideal.map_isPrime_of_surjective hmk (by rwa [Ideal.mk_ker])⟩
    have hne' : P'bar ≠ Pbar := by
      intro h
      apply hne
      have h' := congrArg (fun Q : PrimeSpectrum (C ⧸ I) ↦ Q.asIdeal.comap (Ideal.Quotient.mk I))
        h
      simp only [P'bar, Pbar] at h'
      rwa [Ideal.comap_map_of_surjective' _ hmk, Ideal.comap_map_of_surjective' _ hmk,
        Ideal.mk_ker, sup_eq_left.2 hP'I, sup_eq_left.2 hPI] at h'
    have : P'bar ∉ (PrimeSpectrum.basicOpen e₀.1 : Set (PrimeSpectrum (C ⧸ I))) := by
      rw [he₀]; exact hne'
    simpa [PrimeSpectrum.mem_basicOpen] using this

end HenselianLocalRing

namespace FiniteWStrictlyLocal

/-! ### Primes of `B` near a maximal ideal `n` of `A`

In this section `Bn` is the localization of `B` at the image of `A \ n`, viewed as a finite
algebra over the localization `An` of `A` at `n`, assumed henselian. -/

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : Ideal A} [n.IsMaximal]
  (An Bn : Type u) [CommRing An] [CommRing Bn] [Algebra A An] [IsLocalization.AtPrime An n]
  [Algebra An Bn] [Algebra A Bn] [Algebra B Bn] [IsScalarTower A An Bn] [IsScalarTower A B Bn]
  [IsLocalization (Algebra.algebraMapSubmonoid B n.primeCompl) Bn]

lemma disjoint_of_comap_le {c : Ideal B} (hc : c.comap (algebraMap A B) ≤ n) :
    Disjoint (Algebra.algebraMapSubmonoid B n.primeCompl : Set B) (c : Set B) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ hac
  exact ha (hc hac)

omit [Algebra A Bn] [IsScalarTower A B Bn] in
variable {An Bn} in
lemma comap_map_of_comap_le (c : Ideal B) [c.IsPrime] (hc : c.comap (algebraMap A B) ≤ n) :
    (c.map (algebraMap B Bn)).comap (algebraMap B Bn) = c :=
  IsLocalization.under_map_of_isPrime_disjoint _ Bn inferInstance (disjoint_of_comap_le hc)

variable {An Bn} in
lemma comap_map_eq_maximalIdeal [IsLocalRing An] (c : Ideal B) [c.IsPrime]
    (hc : c.comap (algebraMap A B) = n) :
    (c.map (algebraMap B Bn)).comap (algebraMap An Bn) = maximalIdeal An := by
  set J := (c.map (algebraMap B Bn)).comap (algebraMap An Bn)
  have h1 : J.comap (algebraMap A An) = n := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A B Bn,
      ← Ideal.comap_comap, comap_map_of_comap_le c hc.le, hc]
  have h2 : Ideal.map (algebraMap A An) (J.comap (algebraMap A An)) = J :=
    IsLocalization.map_under n.primeCompl An J
  rw [← h2, h1, IsLocalization.AtPrime.map_eq_maximalIdeal]

variable [Module.Finite An Bn] [HenselianLocalRing An]

include An Bn in
/-- Two primes of `B` over the maximal ideal `n` of `A` with a common generization coincide. -/
lemma eq_of_le_of_le {q c c' : Ideal B} [q.IsPrime] [c.IsPrime] [c'.IsPrime]
    (hc : c.comap (algebraMap A B) = n) (hc' : c'.comap (algebraMap A B) = n) (hq : q ≤ c)
    (hq' : q ≤ c') : c = c' := by
  by_contra hne
  have hdc := disjoint_of_comap_le (n := n) hc.le
  have hdc' := disjoint_of_comap_le (n := n) hc'.le
  have hdq := disjoint_of_comap_le (n := n) ((Ideal.comap_mono hq).trans hc.le)
  have := IsLocalization.isPrime_of_isPrime_disjoint _ Bn c inferInstance hdc
  have := IsLocalization.isPrime_of_isPrime_disjoint _ Bn c' inferInstance hdc'
  have := IsLocalization.isPrime_of_isPrime_disjoint _ Bn q inferInstance hdq
  obtain ⟨ε, hε, hεc, hεother⟩ := HenselianLocalRing.exists_isIdempotentElem_notMem
    (c.map (algebraMap B Bn)) (comap_map_eq_maximalIdeal (An := An) c hc)
  have hεc' : ε ∈ c'.map (algebraMap B Bn) := hεother _ inferInstance
    (comap_map_eq_maximalIdeal (An := An) c' hc') fun h ↦ hne (by
      rw [← comap_map_of_comap_le (Bn := Bn) c hc.le, ← h,
        comap_map_of_comap_le (Bn := Bn) c' hc'.le])
  have h0 : ε * (1 - ε) ∈ q.map (algebraMap B Bn) := by
    rw [mul_sub, mul_one, hε.eq, sub_self]
    exact zero_mem _
  rcases (inferInstance : (q.map (algebraMap B Bn)).IsPrime).mem_or_mem h0 with h | h
  · exact hεc (Ideal.map_mono hq h)
  · have h1 : (1 : Bn) ∈ c'.map (algebraMap B Bn) := by
      simpa using add_mem (Ideal.map_mono hq' h) hεc'
    exact (inferInstance : (c'.map (algebraMap B Bn)).IsPrime).ne_top
      ((Ideal.eq_top_iff_one _).2 h1)


omit [HenselianLocalRing An] in
include An Bn in
/-- The local ring of `B` at a prime `c` over `n` is a quotient of `Bn` by an idempotent; if
`An` is strictly henselian, it is therefore finite over `An`, hence strictly henselian. -/
theorem isStrictlyHenselianLocalRing_localization [IsStrictlyHenselianLocalRing An]
    (c : Ideal B) [c.IsPrime] (hc : c.comap (algebraMap A B) = n) :
    IsStrictlyHenselianLocalRing (Localization.AtPrime c) := by
  have hdc := disjoint_of_comap_le (n := n) hc.le
  set P := c.map (algebraMap B Bn)
  have : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Bn c inferInstance hdc
  have hPm := comap_map_eq_maximalIdeal (An := An) (Bn := Bn) c hc
  have hPc := comap_map_of_comap_le (Bn := Bn) c hc.le
  obtain ⟨ε, hε, hεP, hεother⟩ := HenselianLocalRing.exists_isIdempotentElem_notMem P hPm
  set K : Ideal Bn := Ideal.span {1 - ε}
  have h1ε : 1 - ε ∈ P := by
    have h0 : ε * (1 - ε) ∈ P := by
      rw [mul_sub, mul_one, hε.eq, sub_self]
      exact zero_mem _
    exact ((inferInstance : P.IsPrime).mem_or_mem h0).resolve_left hεP
  have hKP : K ≤ P := (Ideal.span_singleton_le_iff_mem _).2 h1ε
  -- Every maximal ideal of `Bn` containing `K` is `P`.
  have hmaxP : ∀ M : Ideal Bn, M.IsMaximal → K ≤ M → M = P := by
    intro M hM hKM
    have hMm : M.comap (algebraMap An Bn) = maximalIdeal An :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal M)
    by_contra hne
    have := hεother M hM.isPrime hMm hne
    have h1 : (1 : Bn) ∈ M := by
      simpa using add_mem this (hKM (Ideal.subset_span rfl))
    exact hM.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hPmax : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := An) _
      (by rw [Ideal.under_def, hPm]; infer_instance)
  have hmk : Function.Surjective (Ideal.Quotient.mk K) := Ideal.Quotient.mk_surjective
  set PD := P.map (Ideal.Quotient.mk K)
  have hmemPD : ∀ x : Bn, Ideal.Quotient.mk K x ∈ PD ↔ x ∈ P := fun x ↦
    Ideal.mem_quotient_iff_mem hKP
  have hPDmax : PD.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hmk hPmax with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk K 1 ∈ PD := by
        change _ ∈ Ideal.map _ P
        rw [h]
        exact Submodule.mem_top
      exact hPmax.ne_top ((Ideal.eq_top_iff_one _).2 ((hmemPD 1).1 h1))
    · exact h
  have : IsLocalRing (Bn ⧸ K) := by
    refine IsLocalRing.of_unique_max_ideal ⟨PD, hPDmax, fun M hM ↦ ?_⟩
    have hM' : (M.comap (Ideal.Quotient.mk K)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ hmk
    have hKM : K ≤ M.comap (Ideal.Quotient.mk K) := fun x hx ↦ by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact zero_mem _
    rw [← Ideal.map_comap_of_surjective _ hmk M, hmaxP _ hM' hKM]
  have hmaxD : maximalIdeal (Bn ⧸ K) = PD := (IsLocalRing.eq_maximalIdeal hPDmax).symm
  have : HenselianLocalRing (Bn ⧸ K) := HenselianLocalRing.finite_local_henselian An (Bn ⧸ K)
  -- `Bn ⧸ K` is the localization of `B` at `c`.
  have hunit : ∀ b : B, b ∉ c → IsUnit (algebraMap B (Bn ⧸ K) b) := by
    intro b hb
    rw [← IsLocalRing.notMem_maximalIdeal, hmaxD, ← Ideal.Quotient.mk_algebraMap, hmemPD]
    intro h
    exact hb (by rw [← hPc]; exact h)
  have hunitBn : ∀ s ∈ Algebra.algebraMapSubmonoid B n.primeCompl,
      algebraMap B Bn s ∉ P := fun s hs h ↦
    (inferInstance : P.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.map_units Bn ⟨s, hs⟩))
  have hloc : IsLocalization.AtPrime (Bn ⧸ K) c := by
    refine (isLocalization_iff _ _).2 ⟨fun y ↦ hunit y.1 y.2, fun z ↦ ?_, fun {x y} hxy ↦ ?_⟩
    · obtain ⟨w, rfl⟩ := hmk z
      obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B n.primeCompl) w
      have hsc : (s : B) ∉ c := fun h ↦ Set.disjoint_left.1 hdc s.2 h
      refine ⟨⟨b, ⟨s, hsc⟩⟩, ?_⟩
      simp only [← Ideal.Quotient.mk_algebraMap, ← map_mul]
      exact congrArg (Ideal.Quotient.mk K) hs
    · have hxy' : algebraMap B Bn (x - y) ∈ K := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap, map_sub, hxy,
          sub_self]
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hxy'
      have hε0 : ε * algebraMap B Bn (x - y) = 0 := by
        rw [← hw, mul_comm w, ← mul_assoc, mul_sub, mul_one, hε.eq, sub_self, zero_mul]
      obtain ⟨⟨b', s'⟩, hs'⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B n.primeCompl) ε
      have h0 : algebraMap B Bn (b' * (x - y)) = algebraMap B Bn 0 := by
        rw [map_mul, ← hs', mul_comm ε, mul_assoc, hε0, mul_zero, map_zero]
      obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid B
        n.primeCompl) (S := Bn) h0
      have htc : (u : B) * b' ∉ c := by
        intro h
        have h' : algebraMap B Bn ((u : B) * b') ∈ P := Ideal.mem_map_of_mem _ h
        rw [map_mul, ← hs'] at h'
        rcases (inferInstance : P.IsPrime).mem_or_mem h' with h'' | h''
        · exact hunitBn u u.2 h''
        · rcases (inferInstance : P.IsPrime).mem_or_mem h'' with h''' | h'''
          · exact hεP h'''
          · exact hunitBn s' s'.2 h'''
      refine ⟨⟨(u : B) * b', htc⟩, ?_⟩
      have := hu
      rw [mul_zero, ← mul_assoc, mul_sub, sub_eq_zero] at this
      exact this
  -- The residue field of `Bn ⧸ K` is algebraic over that of `An`, hence separably closed.
  have : IsLocalHom (algebraMap An (Bn ⧸ K)) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have hmem : algebraMap An Bn a ∈ P := by
      rw [← Ideal.mem_comap, hPm]
      exact (IsLocalRing.mem_maximalIdeal _).2 hna
    have : algebraMap An (Bn ⧸ K) a ∈ maximalIdeal (Bn ⧸ K) := by
      rw [hmaxD, ← Ideal.Quotient.mk_algebraMap, hmemPD]
      exact hmem
    exact (IsLocalRing.mem_maximalIdeal _).1 this ha
  have := Algebra.IsAlgebraic.residueField_of_isIntegral (R := An) (S := Bn ⧸ K)
  have : IsSepClosed (ResidueField (Bn ⧸ K)) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField An)
  have : IsStrictlyHenselianLocalRing (Bn ⧸ K) := ⟨this⟩
  exact IsStrictlyHenselianLocalRing.of_ringEquiv
    (IsLocalization.algEquiv c.primeCompl (Bn ⧸ K) (Localization.AtPrime c)).toRingEquiv

end FiniteWStrictlyLocal

section

open TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A module-finite algebra over a w-strictly local ring is w-strictly local: the closed points
of `Spec B` are the points over closed points of `Spec A`, every point of `Spec B` specializes
to a unique closed point, and the local rings of `B` at maximal ideals are strictly henselian
(`FiniteWStrictlyLocal.eq_of_le_of_le`,
`FiniteWStrictlyLocal.isStrictlyHenselianLocalRing_localization`, applied to
`A_n ⊗_A B`). -/
theorem IsWStrictlyLocalRing.of_finite [IsWStrictlyLocalRing A] : IsWStrictlyLocalRing B := by
  have hmax : ∀ c : PrimeSpectrum B,
      (c.asIdeal.IsMaximal ↔ (c.asIdeal.comap (algebraMap A B)).IsMaximal) := fun c ↦
    ⟨fun _ ↦ Ideal.isMaximal_under_of_isIntegral_of_isMaximal c.asIdeal,
      fun h ↦ Ideal.isMaximal_of_isIntegral_of_isMaximal_under c.asIdeal h⟩
  have hcl : closedPoints (PrimeSpectrum B) =
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' closedPoints (PrimeSpectrum A) := by
    ext x
    simp only [Set.mem_preimage, mem_closedPoints_iff,
      PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    exact hmax x
  have hw : WLocalSpace (PrimeSpectrum B) :=
    { eq_of_specializes := fun {x c c'} hc hc' hxc hxc' ↦ by
        rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hc hc'
        have hn := (hmax c).1 hc
        have hn' := (hmax c').1 hc'
        have hA : PrimeSpectrum.comap (algebraMap A B) c =
            PrimeSpectrum.comap (algebraMap A B) c' :=
          WLocalSpace.eq_of_specializes
            ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hn)
            ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hn')
            (hxc.map (PrimeSpectrum.continuous_comap _))
            (hxc'.map (PrimeSpectrum.continuous_comap _))
        have hA' : c'.asIdeal.comap (algebraMap A B) = c.asIdeal.comap (algebraMap A B) :=
          congrArg PrimeSpectrum.asIdeal hA.symm
        have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization (R := A)
          (c.asIdeal.comap (algebraMap A B))
        exact PrimeSpectrum.ext (FiniteWStrictlyLocal.eq_of_le_of_le
          (n := c.asIdeal.comap (algebraMap A B))
          (Localization.AtPrime (c.asIdeal.comap (algebraMap A B)))
          (Localization.AtPrime (c.asIdeal.comap (algebraMap A B)) ⊗[A] B) rfl hA'
          ((PrimeSpectrum.le_iff_specializes x c).2 hxc)
          ((PrimeSpectrum.le_iff_specializes x c').2 hxc'))
      isClosed_closedPoints := by
        rw [hcl]
        exact WLocalSpace.isClosed_closedPoints.preimage (PrimeSpectrum.continuous_comap _) }
  refine { wLocalSpace_primeSepectrum := hw, isStrictlyHenselianLocalRing_localization := ?_ }
  intro m hm
  have : (m.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization (R := A)
    (m.comap (algebraMap A B))
  exact FiniteWStrictlyLocal.isStrictlyHenselianLocalRing_localization
    (n := m.comap (algebraMap A B)) (Localization.AtPrime (m.comap (algebraMap A B)))
    (Localization.AtPrime (m.comap (algebraMap A B)) ⊗[A] B) m rfl

end

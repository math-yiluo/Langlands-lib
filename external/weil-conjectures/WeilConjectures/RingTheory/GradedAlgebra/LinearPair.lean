/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.CosetCover
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.RingTheory.GradedAlgebra.Standard

/-!
# Linear forms without common zero on a projective curve

Let `S` be a standard graded algebra over an infinite field `k` which is a domain and such that
`Proj S` has dimension one. We show that there are two linear forms `l₀, l₁ ∈ S₁` without
common zero on `Proj S`: choose `l₀ ≠ 0`; its zero locus `V₊(l₀)` is a proper closed subset of
the irreducible Noetherian one-dimensional space `Proj S`, hence finite, and `l₁` is chosen
outside the finitely many proper subspaces `𝔭ₓ ∩ S₁`, `x ∈ V₊(l₀)`.

## Main statements

- `Set.Finite.of_isClosed_ne_univ_of_topologicalKrullDim_eq_one` — a proper closed subset of
  an irreducible Noetherian `T₀` space of dimension one is finite.
- `ProjectiveSpectrum.isEmbedding_toPrimeSpectrum` — `Proj S` is a subspace of `Spec S`; in
  particular it is `T₀`, and Noetherian if `S` is.
- `GradedAlgebra.IsStandard.exists_basicOpen_sup_eq_top` — the existence of `l₀, l₁`.
-/

@[expose] public section

open Set TopologicalSpace Topology Order

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- In a space of Krull dimension one, there is no chain of three irreducible closed subsets. -/
lemma not_lt_lt_of_topologicalKrullDim_eq_one (hdim : topologicalKrullDim X = 1)
    {a b c : IrreducibleCloseds X} (hab : a < b) (hbc : b < c) : False := by
  have h := LTSeries.length_le_krullDim
    (((RelSeries.singleton _ a).snoc b hab).snoc c (by exact hbc))
  rw [← topologicalKrullDim, hdim] at h
  simp at h

/-- In an irreducible Noetherian `T₀` space of Krull dimension one, every proper closed subset
is finite. -/
lemma Set.Finite.of_isClosed_ne_univ_of_topologicalKrullDim_eq_one [NoetherianSpace X]
    [T0Space X] [IrreducibleSpace X] (hdim : topologicalKrullDim X = 1) {Z : Set X}
    (hZ : IsClosed Z) (hne : Z ≠ univ) : Z.Finite := by
  obtain ⟨S, hS, hSZ⟩ := NoetherianSpace.exists_finset_irreducible ⟨Z, hZ⟩
  have hsub (t : Closeds X) (ht : t ∈ S) : (t : Set X).Subsingleton := by
    have htZ : (t : Set X) ⊆ Z := by
      have : t ≤ S.sup id := Finset.le_sup (f := id) ht
      rw [← hSZ] at this
      exact this
    let T : IrreducibleCloseds X := ⟨t, hS ⟨t, ht⟩, t.2⟩
    let U : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hTU : T < U := by
      refine lt_of_le_of_ne (fun _ _ ↦ trivial) fun h ↦ hne ?_
      have : (t : Set X) = univ := congrArg (fun s : IrreducibleCloseds X ↦ (s : Set X)) h
      exact eq_univ_of_univ_subset (this ▸ htZ)
    have hcl (x : X) (hx : x ∈ (t : Set X)) : closure {x} = (t : Set X) := by
      by_contra hne'
      let P : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure,
        isClosed_closure⟩
      have hPT : P < T := lt_of_le_of_ne
        ((t.2.closure_subset_iff).mpr (singleton_subset_iff.mpr hx))
        fun h ↦ hne' (congrArg (fun s : IrreducibleCloseds X ↦ (s : Set X)) h)
      exact not_lt_lt_of_topologicalKrullDim_eq_one hdim hPT hTU
    intro x hx y hy
    exact (inseparable_iff_closure_eq.mpr ((hcl x hx).trans (hcl y hy).symm)).eq
  have hZS : Z = ⋃ t ∈ S, (t : Set X) := by
    have h := congrArg (fun s : Closeds X ↦ (s : Set X)) hSZ
    rw [Closeds.coe_finset_sup] at h
    simpa using h
  rw [hZS]
  exact S.finite_toSet.biUnion fun t ht ↦ (hsub t ht).finite

end Topology

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- A point of the projective spectrum, viewed as a point of the prime spectrum. -/
def toPrimeSpectrum (x : ProjectiveSpectrum 𝒜) : PrimeSpectrum A :=
  ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

/-- The projective spectrum is a subspace of the prime spectrum. -/
lemma isEmbedding_toPrimeSpectrum : IsEmbedding (toPrimeSpectrum 𝒜) := by
  refine ⟨⟨TopologicalSpace.ext_isClosed fun Z ↦ ?_⟩, fun x y h ↦ ?_⟩
  · rw [isClosed_induced_iff, isClosed_iff_zeroLocus]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨PrimeSpectrum.zeroLocus s, PrimeSpectrum.isClosed_zeroLocus s, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).mp ht
      exact ⟨s, rfl⟩
  · exact ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
      (congrArg PrimeSpectrum.asIdeal h))

instance : T0Space (ProjectiveSpectrum 𝒜) :=
  (isEmbedding_toPrimeSpectrum 𝒜).t0Space

instance [IsNoetherianRing A] : NoetherianSpace (ProjectiveSpectrum 𝒜) :=
  (isEmbedding_toPrimeSpectrum 𝒜).isInducing.noetherianSpace

end ProjectiveSpectrum

namespace GradedAlgebra.IsStandard

open ProjectiveSpectrum

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] {𝒜 : ℕ → Submodule k S}
  [GradedAlgebra 𝒜] [IsStandard 𝒜]

/-- In a standard graded algebra, an ideal containing the degree-one part contains the
irrelevant ideal. -/
lemma irrelevant_le_of_grade_one_subset {I : Ideal S} (h : (𝒜 1 : Set S) ⊆ I) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ I := by
  classical
  intro a ha
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  rcases i with _ | j
  · rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff,
      GradedRing.proj_apply] at ha
    rw [ha]
    exact zero_mem _
  · have hmem : (DirectSum.decompose 𝒜 a (j + 1) : S) ∈ 𝒜 1 ^ j * 𝒜 1 := by
      rw [← pow_succ, ← grade_eq_pow]
      exact (DirectSum.decompose 𝒜 a (j + 1)).2
    exact (Submodule.mul_le (P := I.restrictScalars k)).mpr
      (fun x _ y hy ↦ I.mul_mem_left x (h hy)) hmem

/-- A standard graded algebra over a field is Noetherian. -/
lemma isNoetherianRing (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] [IsStandard 𝒜] :
    IsNoetherianRing S := by
  obtain ⟨s, hs⟩ := fg_one (𝒜 := 𝒜)
  have : Algebra.FiniteType k S := ⟨⟨s, by
    rw [← adjoin_one (𝒜 := 𝒜), ← hs]
    exact le_antisymm (Algebra.adjoin_mono Submodule.subset_span)
      (Algebra.adjoin_le (Algebra.span_le_adjoin k _))⟩⟩
  exact Algebra.FiniteType.isNoetherianRing k S

/-- Let `S` be a standard graded algebra over an infinite field `k` which is a domain, such
that `Proj S` has dimension one. Then there are linear forms `l₀, l₁ ∈ S₁` without common zero
on `Proj S`.
(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem exists_basicOpen_sup_eq_top [Infinite k] [IsDomain S]
    (hdim : topologicalKrullDim (ProjectiveSpectrum 𝒜) = 1) :
    ∃ l₀ ∈ 𝒜 1, ∃ l₁ ∈ 𝒜 1, basicOpen 𝒜 l₀ ⊔ basicOpen 𝒜 l₁ = ⊤ := by
  classical
  have := IsStandard.isNoetherianRing 𝒜
  obtain ⟨x₀⟩ : Nonempty (ProjectiveSpectrum 𝒜) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : IsEmpty (IrreducibleCloseds (ProjectiveSpectrum 𝒜)) :=
      ⟨fun t ↦ h.elim t.isIrreducible.nonempty.some⟩
    rw [topologicalKrullDim, krullDim_eq_bot] at hdim
    exact WithBot.bot_ne_one hdim
  obtain ⟨l₀, hl₀, hl₀x⟩ : ∃ l ∈ 𝒜 1, l ∉ x₀.asHomogeneousIdeal := by
    by_contra! h
    exact x₀.not_irrelevant_le (irrelevant_le_of_grade_one_subset h)
  have hl₀0 : l₀ ≠ 0 := fun h ↦ hl₀x (h ▸ zero_mem _)
  have hirr : l₀ ∈ HomogeneousIdeal.irrelevant 𝒜 := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne 𝒜 hl₀ one_ne_zero]
  let η : ProjectiveSpectrum 𝒜 :=
    ⟨⊥, by simpa using Ideal.isPrime_bot, fun h ↦ hl₀0 (by
      have h' := h hirr
      rwa [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h')⟩
  have : IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
    rw [irreducibleSpace_def]
    have hη : closure {η} = (⊤ : Set (ProjectiveSpectrum 𝒜)) :=
      eq_univ_of_forall fun x ↦
        (le_iff_mem_closure 𝒜 η x).mp ((as_ideal_le_as_ideal 𝒜 η x).mp bot_le)
    rw [← hη]
    exact isIrreducible_singleton.closure
  have hZ : (zeroLocus 𝒜 {l₀}).Finite := by
    refine .of_isClosed_ne_univ_of_topologicalKrullDim_eq_one hdim (isClosed_zeroLocus 𝒜 _)
      fun h ↦ hl₀0 ?_
    have hη : η ∈ zeroLocus 𝒜 {l₀} := h ▸ mem_univ η
    simpa [η] using hη
  let W (x : ProjectiveSpectrum 𝒜) : Submodule k (𝒜 1) :=
    (x.asHomogeneousIdeal.toIdeal.restrictScalars k).comap (𝒜 1).subtype
  have hW (x : ProjectiveSpectrum 𝒜) : W x ≠ ⊤ := fun h ↦
    x.not_irrelevant_le (irrelevant_le_of_grade_one_subset fun l hl ↦ by
      have : (⟨l, hl⟩ : 𝒜 1) ∈ W x := h ▸ Submodule.mem_top
      exact this)
  obtain ⟨⟨l₁, hl₁⟩, hl₁W⟩ : ∃ l : 𝒜 1, ∀ x ∈ hZ.toFinset, l ∉ W x := by
    have hcov := Subspace.biUnion_ne_univ_of_top_notMem (s := hZ.toFinset.image W)
      (by simpa using fun x _ ↦ hW x)
    obtain ⟨l, hl⟩ := (ne_univ_iff_exists_notMem _).mp hcov
    refine ⟨l, fun x hx hlx ↦ hl ?_⟩
    simp only [mem_iUnion]
    exact ⟨W x, Finset.mem_image_of_mem W hx, hlx⟩
  refine ⟨l₀, hl₀, l₁, hl₁, eq_top_iff.mpr fun x _ ↦ ?_⟩
  rw [TopologicalSpace.Opens.mem_sup]
  by_cases hx : l₀ ∈ x.asHomogeneousIdeal
  · right
    exact hl₁W x (by simpa [mem_zeroLocus] using hx)
  · exact Or.inl hx

end GradedAlgebra.IsStandard

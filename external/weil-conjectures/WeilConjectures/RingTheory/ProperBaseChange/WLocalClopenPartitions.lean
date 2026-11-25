/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal

/-!
# Clopen partitions of a w-local affine spectrum

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node proposition-w-local-components--1, order 1221
(blueprint: proposition-w-local-components--1).
-/

@[expose] public section

universe u w

namespace PrimeSpectrum

/-- Patch compactness and the closed-point description of clopen partitions of a w-local
spectrum. Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node proposition-w-local-components--1, order 1221
(blueprint: proposition-w-local-components--1).

Proof:
1. Mathlib gives compactness of the constructible topology. A compact open is clopen in
   that topology. The compact-open basis and T0 separation therefore make it totally
   separated and hence Hausdorff.
2. The closed points of a w-local space form a closed spectral T1 subspace, hence are
   compact, Hausdorff and totally disconnected, by the source library's instances.
3. The proved source-library homeomorphism from closed points to connected components
   gives a continuous retraction `r` onto closed points. It fixes closed points and sends
   each point to the closed point of its component. Clopen membership is constant on a
   component, so `x ∈ U ↔ r x ∈ U` for every clopen `U`.
4. Lift each partition part by inverse image under `r`. Inverse image preserves
   clopenness, disjointness and arbitrary unions, and restriction recovers each part.
   Any other lift agrees pointwise by the clopen-membership equivalence, proving uniqueness.
   Conversely restriction of a partition preserves the same three properties.
5. Every point specializes to a closed point. That specialization lies in the same
   component, so w-local uniqueness identifies it with the component's closed point.
   An open containing that closed point contains its generalizations. -/
theorem wLocal_clopen_partition_properties (A : Type u) [CommRing A] :
    (CompactSpace (WithConstructibleTopology (PrimeSpectrum A)) ∧
      T2Space (WithConstructibleTopology (PrimeSpectrum A))) ∧
    (IsWLocalRing A →
      (CompactSpace (closedPoints (PrimeSpectrum A)) ∧
        T2Space (closedPoints (PrimeSpectrum A)) ∧
        TotallyDisconnectedSpace (closedPoints (PrimeSpectrum A))) ∧
      (∀ (I : Type w) (P : I → Set (closedPoints (PrimeSpectrum A))),
        ((∀ i : I, IsClopen (P i)) ∧
          Pairwise (fun i j : I ↦ Disjoint (P i) (P j)) ∧ (⋃ i : I, P i) = Set.univ) ↔
        ∃! Q : I → Set (PrimeSpectrum A),
          (∀ i : I, IsClopen (Q i)) ∧
          Pairwise (fun i j : I ↦ Disjoint (Q i) (Q j)) ∧
          (⋃ i : I, Q i) = Set.univ ∧
          ∀ i : I, (Subtype.val : closedPoints (PrimeSpectrum A) → PrimeSpectrum A) ⁻¹'
            Q i = P i) ∧
      (∀ (E : Set (closedPoints (PrimeSpectrum A))), IsClopen E →
        ∀ (O : Set (PrimeSpectrum A)), IsOpen O → Subtype.val '' E ⊆ O →
          ∀ c ∈ E, connectedComponent (c : PrimeSpectrum A) ⊆ O)) := by
  classical
  constructor
  · refine ⟨inferInstance, ?_⟩
    have hcl (U : Set (PrimeSpectrum A)) (ho : IsOpen U) (hc : IsCompact U) :
        @IsClopen (PrimeSpectrum A) (constructibleTopology (PrimeSpectrum A)) U :=
      ⟨hc.isClosed_constructibleTopology_of_isOpen ho,
        hc.isOpen_constructibleTopology_of_isOpen ho⟩
    have hsep : @TotallySeparatedSpace (PrimeSpectrum A)
        (constructibleTopology (PrimeSpectrum A)) := by
      rw [@totallySeparatedSpace_iff_exists_isClopen]
      intro x y hxy
      obtain ⟨U, hU, hxyU⟩ := exists_isOpen_xor_mem hxy
      rcases hxyU with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · obtain ⟨V, ⟨hVo, hVc⟩, hxV, hVU⟩ :=
          PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx hU
        exact ⟨V, hcl V hVo hVc, hxV, fun hyV ↦ hy (hVU hyV)⟩
      · obtain ⟨V, ⟨hVo, hVc⟩, hyV, hVU⟩ :=
          PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hy hU
        exact ⟨Vᶜ, @IsClopen.compl _ (constructibleTopology _) V (hcl V hVo hVc),
          fun hxV ↦ hx (hVU hxV), fun hyVc ↦ hyVc hyV⟩
    have : @T2Space (PrimeSpectrum A) (constructibleTopology (PrimeSpectrum A)) :=
      @TotallySeparatedSpace.t2Space _ (constructibleTopology _) hsep
    exact @T2Space.of_injective_continuous
      (WithConstructibleTopology (PrimeSpectrum A)) (PrimeSpectrum A) _
      (constructibleTopology (PrimeSpectrum A)) this _
      (WithTopology.ofTopology_injective _) (WithTopology.continuous_ofTopology _)
  · intro hA
    let : IsWLocalRing A := hA
    let X := PrimeSpectrum A
    let e : closedPoints X ≃ₜ ConnectedComponents X := WLocalSpace.closedPointsHomeomorph
    let r : X → closedPoints X := fun x ↦ e.symm (ConnectedComponents.mk x)
    have he (c : closedPoints X) : e c = ConnectedComponents.mk c.val := rfl
    have hr : Continuous r := e.symm.continuous.comp ConnectedComponents.continuous_coe
    have hrc (c : closedPoints X) : r c.val = c := by
      change e.symm (e c) = c
      exact e.symm_apply_apply c
    have hrmk (x : X) : ConnectedComponents.mk (r x).val = ConnectedComponents.mk x := by
      rw [← he]
      exact e.apply_symm_apply _
    have hmem (U : Set X) (hU : IsClopen U) (x : X) : x ∈ U ↔ (r x).val ∈ U := by
      have hc : (r x).val ∈ connectedComponent x :=
        ConnectedComponents.coe_eq_coe'.mp (hrmk x)
      constructor
      · intro hx
        exact hU.connectedComponent_subset hx hc
      · intro hx
        exact hU.connectedComponent_subset hx (ConnectedComponents.coe_eq_coe'.mp (hrmk x).symm)
    refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, ?_, ?_⟩
    · intro I P
      constructor
      · rintro ⟨hP, hd, hc⟩
        let Q : I → Set X := fun i ↦ r ⁻¹' P i
        have hQ (i : I) : IsClopen (Q i) := (hP i).preimage hr
        have hQP (i : I) : Subtype.val ⁻¹' Q i = P i := by
          ext c
          change r c.val ∈ P i ↔ c ∈ P i
          rw [hrc]
        refine ⟨Q, ⟨hQ, ?_, ?_, hQP⟩, ?_⟩
        · intro i j hij
          exact (hd hij).preimage r
        · rw [← Set.preimage_iUnion, hc, Set.preimage_univ]
        · intro Q' hQ'
          funext i
          ext x
          calc
            x ∈ Q' i ↔ (r x).val ∈ Q' i := hmem _ (hQ'.1 i) x
            _ ↔ r x ∈ P i := Set.ext_iff.mp (hQ'.2.2.2 i) (r x)
            _ ↔ x ∈ Q i := Iff.rfl
      · rintro ⟨Q, hQ, _⟩
        refine ⟨?_, ?_, ?_⟩
        · intro i
          rw [← hQ.2.2.2 i]
          exact (hQ.1 i).preimage continuous_subtype_val
        · intro i j hij
          rw [← hQ.2.2.2 i, ← hQ.2.2.2 j]
          exact (hQ.2.1 hij).preimage Subtype.val
        · simp_rw [← hQ.2.2.2]
          rw [← Set.preimage_iUnion, hQ.2.2.1, Set.preimage_univ]
    · intro E _ O hO hEO c hc x hx
      obtain ⟨d, hd, hxd⟩ := exists_isClosed_specializes x
      have hdc : d = c.val := WLocalSpace.closedPoints_eq_of_mk_eq
        (mem_closedPoints_iff.mpr hd) c.property
        (hxd.connectedComponents_mk_eq.symm.trans
          (ConnectedComponents.coe_eq_coe'.mpr hx))
      exact (hdc ▸ hxd).mem_open hO (hEO ⟨c, hc, rfl⟩)

end PrimeSpectrum

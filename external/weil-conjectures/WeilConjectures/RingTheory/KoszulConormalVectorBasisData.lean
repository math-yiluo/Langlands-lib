/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence

/-! Auxiliary linear independence and spanning result for conormal generators.
(blueprint: lem-sc-koszul-conormal-basis-data)
-/

@[expose] public section

universe u

namespace ExteriorAlgebra

private theorem oneEquiv_symm_coe
    (A : Type u) [CommRing A] (r : ℕ) (v : Fin r →₀ A) :
    ((exteriorPower.oneEquiv A (Fin r →₀ A)).symm v :
      ExteriorAlgebra A (Fin r →₀ A)) = ExteriorAlgebra.ι A v := by
  simp [exteriorPower.oneEquiv_symm_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply]

private theorem boundary_two
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (v : Fin 2 → (Fin r →₀ A)) :
    (exteriorPower.oneEquiv A (Fin r →₀ A))
      (koszulBoundary A r f 1 (exteriorPower.ιMulti A 2 v)) =
      (Finsupp.linearCombination A f) (v 0) • v 1 -
        (Finsupp.linearCombination A f) (v 1) • v 0 := by
  apply (exteriorPower.oneEquiv A (Fin r →₀ A)).symm.injective
  apply Subtype.val_injective
  simp only [LinearEquiv.symm_apply_apply, koszulBoundary, LinearMap.codRestrict_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, exteriorPower.ιMulti_apply_coe]
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
    mul_one, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι]
  rw [oneEquiv_symm_coe]
  simp only [map_sub, map_smul]
  rw [← Algebra.commutes, ← Algebra.smul_def]
  rfl

/-- Every coefficient of an exact relation of an H₁-regular sequence belongs to
its generated ideal.

Source: Stacks Project, Tag 062I, first paragraph, the displayed exact sequence.

Proof: identify degree one of the Koszul complex with the free module using
`exteriorPower.oneEquiv`. The inclusion of degree zero into the exterior
algebra is injective, and contraction of a vector is its linear combination
embedded by `algebraMap`.
The degree-one differential is the linear combination with coefficients `f`.
Thus the vector with coordinates `a` is a cycle. Vanishing of first homology
expresses it as a boundary of an element of the second exterior power.
This exterior power is spanned by wedges of two basis vectors. Contraction
sends `e_i ∧ e_j` to `f_i e_j - f_j e_i`, whose coordinates all belong to
`Ideal.span (Set.range f)`. The submodule of vectors with coordinates in that
ideal is closed under sums and scalar multiplication, so every boundary,
and hence every coordinate of `a`, belongs to that ideal. This also covers
the empty sequence and the zero ring. -/
private theorem koszulRelation_coefficients_mem
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsH1Regular f)
    (a : Fin r → A) (ha : ∑ i, a i * f i = 0) :
    ∀ i, a i ∈ Ideal.span (Set.range f) := by
  classical
  let E := Fin r →₀ A
  let v : E := Finsupp.equivFunOnFinite.symm a
  let e := exteriorPower.oneEquiv A E
  have hv : (Finsupp.linearCombination A f) v = 0 := by
    simpa [v, Finsupp.linearCombination_apply, Finsupp.sum_fintype] using ha
  have hcycle : koszulBoundary A r f 0 (e.symm v) = 0 := by
    apply Subtype.val_injective
    change CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm A E)) (Finsupp.linearCombination A f)
        (e.symm v : ExteriorAlgebra A E) = 0
    rw [oneEquiv_symm_coe, CliffordAlgebra.contractLeft_ι, hv, map_zero]
  have hexact : (koszulComplex A r f).ExactAt 1 :=
    ((koszulComplex A r f).exactAt_iff_isZero_homology 1).mpr hreg
  rw [(koszulComplex A r f).exactAt_iff' 2 1 0 (by simp) (by simp)] at hexact
  have hd (n : ℕ) : (koszulComplex A r f).d (n + 1) n =
      ModuleCat.ofHom (koszulBoundary A r f n) := by
    dsimp only [koszulComplex]
    exact ChainComplex.of_d _ _ n
  obtain ⟨x, hx⟩ := (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mp hexact
    (e.symm v) (by
      change ((koszulComplex A r f).d 1 0).hom (e.symm v) = 0
      rw [hd 0]
      exact hcycle)
  have hboundary : koszulBoundary A r f 1 x = e.symm v := by
    change ((koszulComplex A r f).d 2 1).hom x = e.symm v at hx
    rw [hd 1] at hx
    exact hx
  have hcoords (z : ⋀[A]^2 E) :
      ∀ i, e (koszulBoundary A r f 1 z) i ∈ Ideal.span (Set.range f) := by
    have hz : z ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
      rw [exteriorPower.ιMulti_span]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun z _ ↦
      ∀ i, e (koszulBoundary A r f 1 z) i ∈ Ideal.span (Set.range f))
      ?_ ?_ ?_ ?_ hz
    · rintro z ⟨w, rfl⟩ i
      rw [boundary_two]
      have hcomb (t : E) :
          (Finsupp.linearCombination A f) t ∈ Ideal.span (Set.range f) := by
        change _ ∈ Submodule.span A (Set.range f)
        rw [← Finsupp.range_linearCombination]
        exact LinearMap.mem_range_self _ _
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (hcomb (w 0)))
        (Ideal.mul_mem_right _ _ (hcomb (w 1)))
    · intro i
      simp only [map_zero]
      exact Ideal.zero_mem _
    · intro y z hy hz hyy hzz i
      simp only [map_add]
      exact Ideal.add_mem _ (hyy i) (hzz i)
    · intro c z hz hzz i
      simp only [map_smul]
      exact Ideal.mul_mem_left _ _ (hzz i)
  intro i
  have hi := hcoords x i
  rw [hboundary, LinearEquiv.apply_symm_apply] at hi
  change (Finsupp.equivFunOnFinite (Finsupp.equivFunOnFinite.symm a)) i ∈ _ at hi
  simpa only [Equiv.apply_symm_apply] using hi

private theorem square_coefficients
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) {x : A} (hx : x ∈ I ^ 2) :
    ∃ b : Fin r → A, (∀ i, b i ∈ I) ∧ ∑ i, b i * f i = x := by
  classical
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro y hy z hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hf.symm ▸ hz)
    refine ⟨fun i ↦ y * c i, fun i ↦ I.mul_mem_right _ hy, ?_⟩
    simp only [mul_assoc, ← Finset.mul_sum, hc]
  · rintro y z ⟨b, hb, hbe⟩ ⟨c, hc, hce⟩
    refine ⟨b + c, fun i ↦ I.add_mem (hb i) (hc i), ?_⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hbe, hce]

private theorem conormal_generators_span
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    ⊤ ≤ Submodule.span (A ⧸ I)
      (Set.range (fun i ↦ koszulConormalVector A I r f hf (Finsupp.single i 1))) := by
  intro y _
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
  have hx : (x : A) ∈ Ideal.span (Set.range f) := hf.symm ▸ x.property
  simp only [koszulConormalVector, Finsupp.linearCombination_single, one_smul]
  refine Submodule.span_induction
    (p := fun z hz ↦ I.toCotangent ⟨z, hf ▸ hz⟩ ∈ _)
    ?_ ?_ ?_ ?_ hx
  · rintro z ⟨j, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self j)
  · change I.toCotangent 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy hxx hyy
    change I.toCotangent (⟨x, hf ▸ hx⟩ + ⟨y, hf ▸ hy⟩) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ hxx hyy
  · intro a x hx hxx
    change I.toCotangent (a • ⟨x, hf ▸ hx⟩) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ (Ideal.Quotient.mk I a) hxx

/-- The conormal classes of a Koszul-regular generating sequence are linearly
independent and span the cotangent module.

Source: Stacks Project, More on Algebra, Tag 062I, first paragraph of the proof.
The proof identifies the cotangent module with the cokernel of the second
Koszul differential after tensoring with `A ⧸ I`; regularity makes the kernel
of the generator map equal to that image, while every coefficient of that
differential lies in `I`, so the induced map has zero source differential.
(blueprint: lem-sc-koszul-conormal-basis-data)
-/
theorem koszulConormalVector_linearIndependent_and_span
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f)
    (hf : Ideal.span (Set.range f) = I) :
    LinearIndependent (A ⧸ I)
        (fun i => koszulConormalVector A I r f hf (Finsupp.single i 1)) ∧
      ⊤ ≤ Submodule.span (A ⧸ I)
        (Set.range (fun i => koszulConormalVector A I r f hf (Finsupp.single i 1))) := by
  classical
  refine ⟨?_, conormal_generators_span A I r f hf⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  obtain ⟨a, ha⟩ :=
    Classical.axiomOfChoice (fun j ↦ Ideal.Quotient.mk_surjective (c j))
  have hsum : I.toCotangent
      (∑ j, a j • (⟨f j, hf ▸ Ideal.subset_span (Set.mem_range_self j)⟩ : I)) = 0 := by
    simpa only [map_sum, map_smul, ← ha, koszulConormalVector,
      Finsupp.linearCombination_single, one_smul, ← Ideal.Quotient.algebraMap_eq,
      IsScalarTower.algebraMap_smul] using hc
  have hsquare : ∑ j, a j * f j ∈ I ^ 2 := by
    simpa using (I.toCotangent_eq_zero _).mp hsum
  obtain ⟨b, hb, hbe⟩ := square_coefficients A I r f hf hsquare
  have hrel : ∑ j, (a j - b j) * f j = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, hbe, sub_self]
  have hmem := hf ▸ koszulRelation_coefficients_mem A r f (hreg 1 (by decide))
    (fun j ↦ a j - b j) hrel i
  rw [← ha i, Ideal.Quotient.eq_zero_iff_mem]
  simpa using I.add_mem hmem (hb i)

end ExteriorAlgebra

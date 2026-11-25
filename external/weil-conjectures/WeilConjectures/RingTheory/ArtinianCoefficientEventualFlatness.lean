/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.ArtinianCoefficientPresentation
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Flatness after adjoining finitely many relation coefficients

Source: Stacks Project, Tag 07FG, proof of lemma-helper, final presentation paragraph.
(blueprint: lem-weil-pbc-artinian-coefficient-eventual-flatness).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

-- A nilpotent ideal makes every module adically complete, not only the ring itself.
private theorem module_complete_of_nilpotent {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (hI : IsNilpotent I) :
    IsAdicComplete I M := by
  obtain ⟨N, hN⟩ := hI
  refine { haus' := fun x hx ↦ ?_, prec' := fun f hf ↦ ⟨f N, fun m ↦ ?_⟩ }
  · simpa [hN, SModEq.bot] using hx N
  · by_cases hm : m ≤ N
    · exact hf hm
    · have hNm : N ≤ m := by omega
      have heq : f N = f m := by simpa [hN, SModEq.bot] using hf hNm
      rw [heq]

private theorem evaluation_surjective
    (Λ : Type v) [CommRing Λ] [IsArtinianRing Λ] [IsLocalRing Λ]
    (σ : IsLocalRing.ResidueField Λ →+* Λ) (t : Finset Λ)
    (hσ : (IsLocalRing.residue Λ).comp σ = RingHom.id _)
    (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ) :
    Function.Surjective (MvPolynomial.eval₂Hom σ (fun i : t ↦ (i : Λ))) := by
  let e := MvPolynomial.eval₂Hom σ (fun i : t ↦ (i : Λ))
  let S := e.range
  let f : S →+* Λ := S.subtype
  let m := IsLocalRing.maximalIdeal Λ
  let J := m.comap f
  have hmap : J.map f = m := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mpr le_rfl
    · change IsLocalRing.maximalIdeal Λ ≤ _
      rw [← ht]
      apply Ideal.span_le.mpr
      intro x hx
      have hxS : x ∈ S := ⟨MvPolynomial.X ⟨x, hx⟩, by simp [e]⟩
      have hxm : x ∈ m := by
        change x ∈ IsLocalRing.maximalIdeal Λ
        rw [← ht]
        exact Ideal.subset_span hx
      exact Ideal.mem_map_of_mem f (show (⟨x, hxS⟩ : S) ∈ J from hxm)
  have hnil := (isArtinianRing_iff_isNilpotent_maximalIdeal Λ).mp
    (inferInstance : IsArtinianRing Λ)
  have hJ : IsNilpotent J := by
    obtain ⟨N, hN⟩ := hnil
    refine ⟨N, eq_bot_iff.mpr ?_⟩
    intro x hx
    have hx' := Ideal.le_comap_pow f N hx
    have hz : f x = 0 := by simpa [m, hN] using hx'
    exact Subtype.val_injective (by simpa [f] using hz)
  let : IsAdicComplete J S := module_complete_of_nilpotent J hJ
  let : IsAdicComplete (J.map f) Λ := hmap ▸ module_complete_of_nilpotent m hnil
  have hsurj : Function.Surjective ((Ideal.Quotient.mk (J.map f)).comp f) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hσS : σ (IsLocalRing.residue Λ a) ∈ S :=
      ⟨MvPolynomial.C (IsLocalRing.residue Λ a), by simp [e]⟩
    refine ⟨⟨σ (IsLocalRing.residue Λ a), hσS⟩, ?_⟩
    change Ideal.Quotient.mk (J.map f) (σ (IsLocalRing.residue Λ a)) =
      Ideal.Quotient.mk (J.map f) a
    rw [hmap]
    exact RingHom.congr_fun hσ _
  have hf : Function.Surjective f := surjective_of_mk_map_comp_surjective f hsurj
  intro x
  obtain ⟨y, hy⟩ := hf x
  obtain ⟨p, hp⟩ := y.property
  exact ⟨p, hp.trans hy⟩

private theorem flat_polynomial_map {F K ι : Type*} [Field F] [Field K]
    (f : F →+* K) : (MvPolynomial.map (σ := ι) f).Flat := by
  let : Algebra F K := f.toAlgebra
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := ι) F K
  have hl : (Algebra.TensorProduct.includeLeft (S := F)
      (R := F) (A := MvPolynomial ι F) (B := K)).toRingHom.Flat := by
    change (algebraMap (MvPolynomial ι F) (TensorProduct F (MvPolynomial ι F) K)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hf : (Algebra.TensorProduct.includeRight
      (R := F) (A := K) (B := MvPolynomial ι F)).toRingHom.Flat :=
    hl.comp (.of_bijective (Algebra.TensorProduct.comm F (MvPolynomial ι F) K).bijective)
  have heq : MvPolynomial.map (σ := ι) f =
      e.toRingEquiv.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom := by
    apply RingHom.ext
    intro p
    change MvPolynomial.map f p = e (TensorProduct.tmul F 1 p)
    simp only [e, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl
  rw [heq]
  exact hf.comp (.of_bijective e.bijective)

private theorem flat_range_of_kernel_descends {A B C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : f.Flat) (hg : Function.Surjective g)
    (hker : (RingHom.ker (g.comp f)).map f = RingHom.ker g) :
    (g.comp f).range.subtype.Flat := by
  let I := RingHom.ker (g.comp f)
  let q := Ideal.quotientMap (RingHom.ker g) f
    (hker ▸ Ideal.le_comap_map)
  have hq_aux (J : Ideal B) (hJ : I.map f = J) :
      (Ideal.quotientMap J f (hJ ▸ Ideal.le_comap_map)).Flat := by
    subst J
    let : Algebra A B := f.toAlgebra
    have : Module.Flat A B := hf
    change (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv
  have hq : q.Flat := hq_aux _ hker
  let eA := (g.comp f).quotientKerEquivRange
  let eB := g.quotientKerEquivOfSurjective hg
  have heq : (g.comp f).range.subtype.comp eA.toRingHom =
      eB.toRingHom.comp q := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  apply (RingHom.Flat.comp_iff_of_bijective_right
    (f := (g.comp f).range.subtype) (g := eA.toRingHom) eA.bijective).mp
  rw [heq]
  exact hq.comp (.of_bijective eB.bijective)

private theorem evaluation_range {R S ι : Type*} [CommRing R] [CommRing S]
    (σ : R →+* S) (x : ι → S) :
    (MvPolynomial.eval₂Hom σ x).range =
      Subring.closure (Set.range x ∪ Set.range σ) := by
  apply le_antisymm
  · rintro y ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on with
    | C a =>
      simpa using (Subring.subset_closure
        (s := Set.range x ∪ Set.range σ) (Or.inr (Set.mem_range_self a)))
    | add p q hp hq => simpa using (Subring.closure (Set.range x ∪ Set.range σ)).add_mem hp hq
    | mul_X p i hp =>
      simpa using (Subring.closure (Set.range x ∪ Set.range σ)).mul_mem hp
        (Subring.subset_closure
          (s := Set.range x ∪ Set.range σ) (Or.inl (Set.mem_range_self i)))
  · apply Subring.closure_le.mpr
    rintro y (⟨i, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨MvPolynomial.X i, by simp⟩
    · exact ⟨MvPolynomial.C a, by simp⟩

/-- Flatness of the coefficient subalgebra inclusion holds once the finite coefficient
set contains the coefficients of generators of the polynomial evaluation kernel.
Only flatness is asserted; no local structure or essential finite type is part of this lemma.

Source: Stacks Project, Tag 07FG, proof of lemma-helper, final presentation paragraph.
(blueprint: lem-weil-pbc-artinian-coefficient-eventual-flatness).

Proof:
Put K=ResidueField Λ and evaluate K[X_i | i in t] in Λ using sigma and t. This map
is surjective: Λ=sigma(K)+m, and substituting generators of m successively expresses
every element as a polynomial plus a remainder in m^r. Since m is nilpotent the
remainder eventually vanishes. The polynomial ring is Noetherian by Hilbert basis,
so choose finitely many generators g_j of the evaluation kernel. Let d consist of
all their coefficients. If s contains d and c, all g_j descend to F=k(s). Put
I=ker(F[X_i] -> Λ). Since every g_j descends, extending I to K[X_i] gives the
full evaluation kernel. The polynomial coefficient map F[X_i] -> K[X_i] is flat,
by the tensor presentation and freeness of K over F. Quotient base change gives a
flat map F[X_i]/I -> K[X_i]/ker(e). The first isomorphism theorem identifies these
quotients with the restricted evaluation image and Λ, respectively. The restricted
image is the subring generated by sigma(F) and t. Since c is contained in s, the
hypothesis on c implies that this image contains the original structure map from k.
Therefore it is exactly artinianCoefficientSubalgebra k Λ sigma t s. Transporting
flatness through these isomorphisms proves the claim. -/
theorem exists_artinian_coefficient_eventual_flatness
    (k : Type u) [Field k] (Λ : Type v) [CommRing Λ] [Algebra k Λ]
    [IsArtinianRing Λ] [IsLocalRing Λ]
    (σ : IsLocalRing.ResidueField Λ →+* Λ) (t : Finset Λ)
    (c : Finset (IsLocalRing.ResidueField Λ))
    (hσ : (IsLocalRing.residue Λ).comp σ = RingHom.id _)
    (ht : Ideal.span (t : Set Λ) = IsLocalRing.maximalIdeal Λ)
    (hc : ∀ a : k, algebraMap k Λ a ∈ Subring.closure ((t : Set Λ) ∪
      σ '' (IntermediateField.adjoin k (c : Set (IsLocalRing.ResidueField Λ)) :
        Set (IsLocalRing.ResidueField Λ)))) :
    ∃ d : Finset (IsLocalRing.ResidueField Λ),
      ∀ s : Finset (IsLocalRing.ResidueField Λ), d ⊆ s → c ⊆ s →
        RingHom.Flat (artinianCoefficientSubalgebra k Λ σ t s).val.toRingHom := by
  classical
  let K := IsLocalRing.ResidueField Λ
  let e : MvPolynomial t K →+* Λ := MvPolynomial.eval₂Hom σ (fun i : t ↦ (i : Λ))
  have he : Function.Surjective e := evaluation_surjective Λ σ t hσ ht
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian (RingHom.ker e)
  let d := G.biUnion MvPolynomial.coeffs
  refine ⟨d, fun s hds hcs ↦ ?_⟩
  let F := IntermediateField.adjoin k (s : Set K)
  let f : MvPolynomial t F →+* MvPolynomial t K := MvPolynomial.map F.subtype
  have hker : (RingHom.ker (e.comp f)).map f = RingHom.ker e := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mpr le_rfl
    · rw [← hG]
      apply Ideal.span_le.mpr
      intro p hp
      have hpcoeff : (p.coeffs : Set K) ⊆ Set.range F.subtype := by
        intro a ha
        have had : a ∈ d := Finset.mem_biUnion.mpr ⟨p, hp, ha⟩
        have haF : a ∈ F := IntermediateField.subset_adjoin k _ (hds had)
        exact ⟨⟨a, haF⟩, rfl⟩
      obtain ⟨q, hq⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hpcoeff
      have hpker : p ∈ RingHom.ker e := by rw [← hG]; exact Ideal.subset_span hp
      exact hq ▸ Ideal.mem_map_of_mem f
        (show q ∈ RingHom.ker (e.comp f) from by
          change e (f q) = 0
          rw [show f q = p from hq]
          exact hpker)
  have hf : f.Flat := flat_polynomial_map (F := F) (K := K) (ι := t) F.subtype
  have hflat : (e.comp f).range.subtype.Flat :=
    flat_range_of_kernel_descends (A := MvPolynomial t F) (B := MvPolynomial t K)
      (C := Λ) f e hf he hker
  have hcomp : e.comp f = MvPolynomial.eval₂Hom (σ.comp F.subtype)
      (fun i : t ↦ (i : Λ)) := by
    apply RingHom.ext
    intro p
    exact MvPolynomial.eval₂Hom_map_hom F.subtype _ σ p
  have hrange : (e.comp f).range =
      (artinianCoefficientSubalgebra k Λ σ t s).toSubring := by
    rw [hcomp, evaluation_range (R := F) (S := Λ) (ι := t)
      (σ.comp F.subtype) (fun i : t ↦ (i : Λ))]
    have hx : Set.range (fun i : t ↦ (i : Λ)) = (t : Set Λ) := Subtype.range_coe
    have hcoeff : Set.range (fun b : F ↦ σ (b : K)) = σ '' (F : Set K) := by
      ext a
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, b.property, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
    rw [hx]
    change Subring.closure ((t : Set Λ) ∪ Set.range (fun b : F ↦ σ (b : K))) = _
    rw [hcoeff, artinianCoefficientSubalgebra, Algebra.adjoin_eq_ring_closure]
    apply le_antisymm
    · exact Subring.closure_mono (Set.subset_union_right)
    · apply Subring.closure_le.mpr
      rintro a (⟨b, rfl⟩ | ha)
      · apply (Subring.closure_mono (s := (t : Set Λ) ∪
          σ '' (IntermediateField.adjoin k (c : Set K) : Set K)) ?_) (hc b)
        exact Set.union_subset_union_right _
          (Set.image_mono
            (IntermediateField.adjoin.mono k _ _ (Finset.coe_subset.mpr hcs)))
      · exact Subring.subset_closure ha
  change (artinianCoefficientSubalgebra k Λ σ t s).toSubring.subtype.Flat
  rw [← hrange]
  exact hflat

end Algebra

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# A lift of the fibre idempotent gives the localization isomorphism

Source: literature/stacks-project/more-algebra.tex:2542-2549, proof of Lemma Tag 09XH
(blueprint: `lem-weil-pbc-integral-closure-finite-fibre-choose-g`)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w₁ w₂ w₃ w₄


/-- A neighbourhood of the first factor of a finite fibre contains a principal open
on which the integral-closure map is an isomorphism.

Source: literature/stacks-project/more-algebra.tex:2542-2549, proof of Lemma Tag 09XH
(blueprint: `lem-weil-pbc-integral-closure-finite-fibre-choose-g`).
Here `B'` is `integralClosure A B`. -/
theorem integralClosure.exists_bijective_awayMap_of_isIso_restrict
    (A : Type v) (B : Type u)
    (C₁ : Type w₁) (C₂ : Type w₂) (C₁' : Type w₃) (C₂' : Type w₄)
    [CommRing A] [CommRing B]
    [CommRing C₁] [CommRing C₂] [CommRing C₁'] [CommRing C₂']
    [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A)
    [Algebra (A ⧸ I) C₁] [Algebra (A ⧸ I) C₂]
    [Algebra (A ⧸ I) C₁'] [Algebra (A ⧸ I) C₂']
    [Module.Finite (A ⧸ I) C₁]
    (eB : (B ⧸ Ideal.map (algebraMap A B) I) ≃+* C₁ × C₂)
    (eB' : (integralClosure A B ⧸ Ideal.map (algebraMap A (integralClosure A B)) I) ≃+*
      C₁' × C₂')
    (heB : ∀ a : A,
      eB (Ideal.Quotient.mk _ (algebraMap A B a)) =
        algebraMap (A ⧸ I) (C₁ × C₂) (Ideal.Quotient.mk I a))
    (heB' : ∀ a : A,
      eB' (Ideal.Quotient.mk _ (algebraMap A (integralClosure A B) a)) =
        algebraMap (A ⧸ I) (C₁' × C₂') (Ideal.Quotient.mk I a))
    (f₁ : C₁' →ₐ[A ⧸ I] C₁) (f₂ : C₂' →ₐ[A ⧸ I] C₂)
    (hprod : ∀ b : integralClosure A B,
      eB (Ideal.Quotient.mk _ (algebraMap (integralClosure A B) B b)) =
        (f₁ (eB' (Ideal.Quotient.mk _ b)).1, f₂ (eB' (Ideal.Quotient.mk _ b)).2))
    (U : (Spec (.of (integralClosure A B))).Opens)
    (hU : ∀ p : PrimeSpectrum C₁',
      (PrimeSpectrum.comap (Ideal.Quotient.mk _)
        (PrimeSpectrum.comap ((RingHom.fst C₁' C₂').comp eB'.toRingHom) p) :
        PrimeSpectrum (integralClosure A B)) ∈ U)
    (hIso : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap (integralClosure A B) B)) ∣_ U)) :
    ∃ g : integralClosure A B,
      Ideal.Quotient.mk (Ideal.map (algebraMap A (integralClosure A B)) I) g =
        eB'.symm (1, 0) ∧
      (∀ p : PrimeSpectrum (integralClosure A B), g ∉ (p.1 : Set (integralClosure A B)) →
        (p : Spec (.of (integralClosure A B))) ∈ U) ∧
      Function.Bijective (Localization.awayMap (algebraMap (integralClosure A B) B) g) := by
  -- These compatibility hypotheses belong to the fixed statement; the proof is more general.
  have _ := heB
  have _ := heB'
  have _ := hprod
  have hex : ∃ g : integralClosure A B,
      Ideal.Quotient.mk (Ideal.map (algebraMap A (integralClosure A B)) I) g =
        eB'.symm (1, 0) ∧
      (∀ p : PrimeSpectrum (integralClosure A B), g ∉ (p.1 : Set (integralClosure A B)) →
        (p : Spec (.of (integralClosure A B))) ∈ U) := by
    let R : Type u := integralClosure A B
    let W : TopologicalSpace.Opens (PrimeSpectrum R) := U
    let Q := Ideal.map (algebraMap A R) I
    let q : R →+* C₁' × C₂' := eB'.toRingHom.comp (Ideal.Quotient.mk Q)
    have hq : Function.Surjective q := eB'.surjective.comp Ideal.Quotient.mk_surjective
    let f : R →+* C₁' := (RingHom.fst C₁' C₂').comp q
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨r, hr⟩ := hq (x, 0)
      exact ⟨r, congrArg Prod.fst hr⟩
    let K := RingHom.ker f
    let J := PrimeSpectrum.vanishingIdeal ((W : Set (PrimeSpectrum R))ᶜ)
    have hJ : PrimeSpectrum.zeroLocus (J : Set R) = (W : Set (PrimeSpectrum R))ᶜ := by
      exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans
        W.isOpen.isClosed_compl.closure_eq
    have hK : PrimeSpectrum.zeroLocus (K : Set R) ⊆ (W : Set (PrimeSpectrum R)) := by
      rw [← range_comap_of_surjective C₁' f hf]
      rintro _ ⟨p, rfl⟩
      exact hU p
    have hJK : J ⊔ K = ⊤ := by
      apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
      rw [PrimeSpectrum.zeroLocus_sup, hJ]
      exact Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ hp.1 (hK hp.2)
    obtain ⟨j, hj, k, hk, hjk⟩ :=
      (Submodule.mem_sup.mp (show (1 : R) ∈ J ⊔ K from hJK ▸ trivial))
    obtain ⟨g₀, hg₀⟩ := hq (1, 0)
    have hk0 : (q k).1 = 0 := hk
    have hj1 : (q j).1 = 1 := by
      have h := congrArg (fun r : R ↦ (q r).1) hjk
      simpa only [map_add, map_one, Prod.fst_add, Prod.fst_one, hk0, add_zero] using h
    have hg : q (g₀ * j) = (1, 0) := by
      rw [map_mul, hg₀]
      apply Prod.ext
      · simpa using hj1
      · simp
    refine ⟨g₀ * j, ?_, ?_⟩
    · apply eB'.injective
      exact hg.trans (eB'.apply_symm_apply (1, 0)).symm
    · intro p hp
      by_contra hn
      have hmem : g₀ * j ∈ J := J.mul_mem_left g₀ hj
      exact hp ((PrimeSpectrum.mem_zeroLocus _ _).mp (hJ.symm ▸ hn) hmem)
  obtain ⟨g, hg, hD⟩ := hex
  refine ⟨g, hg, hD, ?_⟩
  let f := Spec.map (CommRingCat.ofHom (algebraMap (integralClosure A B) B))
  have : IsIso (f ∣_ U) := hIso
  have hle : PrimeSpectrum.basicOpen g ≤ U := hD
  let V := U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen g
  have hV : U.ι ''ᵁ V = PrimeSpectrum.basicOpen g := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hle
  have hrestrict : IsIso (f ∣_ PrimeSpectrum.basicOpen g) := by
    rw [← hV]
    exact (Arrow.isIso_iff_isIso_of_isIso (morphismRestrictRestrict f U V).hom).mp
      inferInstance
  exact isIso_SpecMap_iff.mp
    ((Arrow.isIso_iff_isIso_of_isIso
      (SpecMapRestrictBasicOpenIso
        (CommRingCat.ofHom (algebraMap (integralClosure A B) B)) g).hom).mp hrestrict)


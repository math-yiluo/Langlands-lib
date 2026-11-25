/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Closed localization of a w-contractible ring

Source: Stacks Project, Tags 096V, 0987 and 09AH
(blueprint: lem-weil-pbc-wcontractible-closed-localization).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace IsLocalization

/-- The finite family of principal opens and the closed localization, indexed by `Option (Fin r)`.
The `none` member is `Spec B`. Source: Stacks Project, Tags 0987 and 09AH
(blueprint: lem-weil-pbc-wcontractible-closed-localization). -/
noncomputable def closedLocalizationFamily (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    {r : ℕ} (f : Fin r → R) : PreZeroHypercover (Spec (.of R)) where
  I₀ := Option (Fin r)
  X j := match j with
    | none => Spec (.of B)
    | some k => Spec (.of (Localization.Away (f k)))
  f j := match j with
    | none => Spec.map (CommRingCat.ofHom (algebraMap R B))
    | some k => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f k))))

private theorem weaklyEtale_of_bijective {A : Type*} {C : Type*}
    [CommRing A] [CommRing C] (g : A →+* C) (hg : Function.Bijective g) :
    g.WeaklyEtale := by
  let := g.toAlgebra
  let e : A ≃ₐ[A] C :=
    { __ := RingEquiv.ofBijective g hg, commutes' := fun _ ↦ rfl }
  have : Algebra.Etale A C := Algebra.Etale.of_equiv e
  exact (RingHom.weaklyEtale_algebraMap_iff).mpr inferInstance

private theorem weaklyEtale_pi {A : Type u} [CommRing A] {ι : Type u}
    [Finite ι] {C : ι → Type u} [∀ i, CommRing (C i)] (g : ∀ i, A →+* C i)
    (hg : ∀ i, (g i).WeaklyEtale) : (RingHom.pi g).WeaklyEtale := by
  classical
  let T : ι → CommRingCat := fun i ↦ .of (C i)
  let h := Spec.map (CommRingCat.ofHom (RingHom.pi g))
  have hh : sigmaSpec T ≫ h = Limits.Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (g i))) := by
    apply Limits.Sigma.hom_ext
    intro i
    simp only [ι_sigmaSpec_assoc, Limits.Sigma.ι_comp_desc]
    dsimp only [h]
    rw [← Spec.map_comp]
    rfl
  have hw : ∀ i, WeaklyEtale (Spec.map (CommRingCat.ofHom (g i))) :=
    fun i ↦ (WeaklyEtale.Spec_iff _).mpr (hg i)
  have hw' : WeaklyEtale (sigmaSpec T ≫ h) := by
    rw [hh]
    exact IsZariskiLocalAtSource.sigmaDesc hw
  have : WeaklyEtale h :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @WeaklyEtale) _ _).mp hw'
  exact (WeaklyEtale.Spec_iff _).mp this

/-- Closed localization and preservation of the retraction property called w-contractibility.
Source: Stacks Project, Tags 096V, 0987 and 09AH
(blueprint: lem-weil-pbc-wcontractible-closed-localization).

Proof: (1) Localization primes are primes disjoint from the denominator monoid. Such a prime
`p` is disjoint precisely when `p + I` is proper, equivalently when some prime `q` contains
both `p` and `I` (localization prime correspondence and existence of maximal ideals).
(2) Basic opens pull back to basic opens, and every denominator is invertible, so this
bijection is a homeomorphism onto its image with the subspace topology.
(3) The fraction map `a/s ↦ (a mod I)/(s mod I)` is surjective with kernel `IB`, inducing
the canonical quotient isomorphism, including when the quotient is zero.
(4) Localizations are flat and have invertible diagonal, hence are weakly etale. The
principal opens together with the localization image cover the spectrum, by the equality
of zero loci. The finite affine family therefore satisfies the full fpqc cover condition.
(5) Given a faithfully flat weakly etale map `B → D`, replace the `B` member by `D`;
its image is unchanged by faithful flatness. The w-contractible-cover-section lemma gives
a section of this finite cover over `R`.
(6) Restrict the section to `Spec B`. Points over `V(I)` must land in the `D` summand,
since each `f k` is in `I`. Every point specializes to one of these points, so the clopen
`D` summand contains the entire image. Restriction to that open summand gives `Spec B → Spec D`.
(7) Affine full faithfulness gives an `R`-map `D → B`. Its composite with `B → D` agrees
with the identity on `R` and hence on all fractions, so is a retraction. The same argument
covers the empty list, the unit ideal, and the zero ring. -/
theorem wcontractible_closed_localization (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] (I : Ideal R)
    [IsLocalization ((IsUnit.submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)) B]
    (r : ℕ) (f : Fin r → R) (hf : ∀ k, f k ∈ I)
    (hV : PrimeSpectrum.zeroLocus (I : Set R) =
      PrimeSpectrum.zeroLocus (Set.range f)) :
    Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap R B)) ∧
    Set.range (PrimeSpectrum.comap (algebraMap R B)) =
      {p | ∃ q : PrimeSpectrum R, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal} ∧
    (∃ e : (B ⧸ I.map (algebraMap R B)) ≃+* (R ⧸ I),
      ∀ a : R, e (Ideal.Quotient.mk _ (algebraMap R B a)) = Ideal.Quotient.mk I a) ∧
    (closedLocalizationFamily R B f).presieve₀ ∈ Scheme.proetalePrecoverage (Spec (.of R)) ∧
    ((∀ (D : Type (max u v)) [CommRing D] (g : R →+* D),
        g.FaithfullyFlat → g.WeaklyEtale → ∃ t : D →+* R, t.comp g = RingHom.id R) →
      ∀ (D : Type (max u v)) [CommRing D] (g : B →+* D),
        g.FaithfullyFlat → g.WeaklyEtale → ∃ t : D →+* B, t.comp g = RingHom.id B) := by
  classical
  let S := (IsUnit.submonoid (R ⧸ I)).comap (Ideal.Quotient.mk I)
  have hdisj (p : PrimeSpectrum R) :
      Disjoint (S : Set R) p.asIdeal ↔
        ∃ q : PrimeSpectrum R, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal := by
    constructor
    · intro hd
      have hproper : p.asIdeal ⊔ I ≠ ⊤ := by
        intro htop
        obtain ⟨a, ha, b, hb, hab⟩ :=
          Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
        have hua : a ∈ S := by
          change IsUnit (Ideal.Quotient.mk I a)
          have heq : Ideal.Quotient.mk I a = 1 := by
            have hh := congrArg (Ideal.Quotient.mk I) hab
            simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hb] using hh
          rw [heq]
          exact isUnit_one
        exact Set.disjoint_left.mp hd hua ha
      obtain ⟨q, hq, hpq⟩ := Ideal.exists_le_maximal (p.asIdeal ⊔ I) hproper
      exact ⟨⟨q, hq.isPrime⟩, le_trans le_sup_right hpq, le_trans le_sup_left hpq⟩
    · rintro ⟨q, hIq, hpq⟩
      apply Set.disjoint_left.mpr
      intro a ha hap
      have hua : IsUnit (Ideal.Quotient.mk I a) := ha
      let φ : (R ⧸ I) →+* (R ⧸ q.asIdeal) :=
        Ideal.Quotient.factor hIq
      have huq : IsUnit (Ideal.Quotient.mk q.asIdeal a) := by
        exact hua.map φ
      have hz : Ideal.Quotient.mk q.asIdeal a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hpq hap)
      exact not_isUnit_zero (hz ▸ huq)
  have himage : Set.range (PrimeSpectrum.comap (algebraMap R B)) =
      {p | ∃ q : PrimeSpectrum R, I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal} := by
    rw [PrimeSpectrum.localization_comap_range B S]
    exact Set.ext (fun p ↦ hdisj p)
  have hquot : ∃ e : (B ⧸ I.map (algebraMap R B)) ≃+* (R ⧸ I),
      ∀ a : R, e (Ideal.Quotient.mk _ (algebraMap R B a)) = Ideal.Quotient.mk I a := by
    let M := Algebra.algebraMapSubmonoid (R ⧸ I) S
    have hM : M ≤ IsUnit.submonoid (R ⧸ I) := by
      rintro x ⟨a, ha, rfl⟩
      exact ha
    let e := (IsLocalization.atUnits (R ⧸ I) M
      (S := B ⧸ I.map (algebraMap R B)) hM).symm
    refine ⟨e.toRingEquiv, fun a ↦ ?_⟩
    exact e.apply_symm_apply (Ideal.Quotient.mk I a)
  refine ⟨PrimeSpectrum.localization_comap_isEmbedding B S, himage, hquot, ?_, ?_⟩
  · let E := closedLocalizationFamily R B f
    have hc : ∀ x, ∃ j, x ∈ Set.range (E.f j) := by
      intro x
      by_cases hx : x ∈ PrimeSpectrum.zeroLocus (I : Set R)
      · refine ⟨none, ?_⟩
        change x ∈ Set.range (PrimeSpectrum.comap (algebraMap R B))
        rw [himage]
        exact ⟨x, hx, le_rfl⟩
      · rw [hV] at hx
        change ¬ Set.range f ⊆ x.asIdeal at hx
        simp only [Set.range_subset_iff, SetLike.mem_coe, not_forall] at hx
        obtain ⟨k, hk⟩ := hx
        refine ⟨some k, ?_⟩
        change x ∈ Set.range (PrimeSpectrum.comap
          (algebraMap R (Localization.Away (f k))))
        rw [PrimeSpectrum.localization_away_comap_range _ (f k)]
        exact hk
    have hw : ∀ j, WeaklyEtale (E.f j) := by
      intro j
      cases j with
      | none =>
        let := Algebra.WeaklyEtale.of_isLocalization R S B
        exact inferInstanceAs
          (WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R B))))
      | some k =>
        exact inferInstanceAs (WeaklyEtale (Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away (f k))))))
    have : Finite E.I₀ := inferInstanceAs (Finite (Option (Fin r)))
    have hqc : ∀ j, QuasiCompact (E.f j) := by
      intro j
      cases j <;> dsimp [E, closedLocalizationFamily] <;> infer_instance
    have : QuasiCompactCover E := by
      constructor
      intro U hU
      exact IsCompactOpenCovered.of_finite_of_isSpectralMap
        (fun j ↦ (E.f j).isSpectralMap) (fun x _ ↦ hc x) U.2 hU.isCompact
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr inferInstance,
      (Scheme.presieve₀_mem_precoverage_iff E).mpr ⟨hc, hw⟩⟩
  · intro hsplit D _ g hg hgw
    -- Use the finite product of Tag 0987 directly. Its component idempotents implement
    -- restriction to the D summand after localizing at the units modulo I.
    let J := ULift.{max u v} (Option (Fin r))
    let A : J → Type (max u v) := fun j ↦ match j.down with
      | none => D
      | some k => ULift.{v} (Localization.Away (f k))
    let (j : J) : CommRing (A j) := by
      rcases j with ⟨j⟩
      cases j <;> dsimp [A] <;> infer_instance
    let a : ∀ j, R →+* A j := fun ⟨j⟩ ↦ match j with
      | none => g.comp (algebraMap R B)
      | some k => ULift.ringEquiv.symm.toRingHom.comp
          (algebraMap R (Localization.Away (f k)))
    have ha : ∀ j, (a j).WeaklyEtale := by
      intro j
      rcases j with ⟨j⟩
      cases j with
      | none =>
        exact ((RingHom.weaklyEtale_algebraMap_iff).mpr
          (Algebra.WeaklyEtale.of_isLocalization R S B)).comp hgw
      | some k =>
        let e : ULift.{v} (Localization.Away (f k)) ≃+* Localization.Away (f k) :=
          ULift.ringEquiv
        exact ((RingHom.weaklyEtale_algebraMap_iff).mpr inferInstance).comp
          (weaklyEtale_of_bijective e.symm.toRingHom e.symm.bijective)
    let F : R →+* (∀ j, A j) := RingHom.pi a
    have hFw : F.WeaklyEtale := by
      let e : ULift.{v} R ≃+* R := ULift.ringEquiv
      let a' : ∀ j, ULift.{v} R →+* A j := fun j ↦ (a j).comp e.toRingHom
      have ha' : ∀ j, (a' j).WeaklyEtale := fun j ↦
        (weaklyEtale_of_bijective e.toRingHom e.bijective).comp (ha j)
      have h := (weaklyEtale_of_bijective e.symm.toRingHom e.symm.bijective).comp
        (weaklyEtale_pi a' ha')
      convert h using 1
      rfl
    have hpoints : ∀ p : PrimeSpectrum R,
        ∃ (j : J) (q : PrimeSpectrum (A j)), PrimeSpectrum.comap (a j) q = p := by
      intro p
      by_cases hp : p ∈ PrimeSpectrum.zeroLocus (I : Set R)
      · have hp' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R B)) := by
          rw [himage]
          exact ⟨p, hp, le_rfl⟩
        obtain ⟨q, hq⟩ := hp'
        obtain ⟨q', hq'⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hg).2 q
        refine ⟨⟨none⟩, q', ?_⟩
        change PrimeSpectrum.comap (g.comp (algebraMap R B)) q' = p
        rw [PrimeSpectrum.comap_comp_apply, hq', hq]
      · rw [hV] at hp
        change ¬ Set.range f ⊆ p.asIdeal at hp
        simp only [Set.range_subset_iff, SetLike.mem_coe, not_forall] at hp
        obtain ⟨k, hk⟩ := hp
        have hp' : p ∈ Set.range (PrimeSpectrum.comap
            (algebraMap R (Localization.Away (f k)))) := by
          rw [PrimeSpectrum.localization_away_comap_range _ (f k)]
          exact hk
        obtain ⟨q, hq⟩ := hp'
        refine ⟨⟨some k⟩, PrimeSpectrum.comap ULift.ringEquiv.toRingHom q, ?_⟩
        change PrimeSpectrum.comap
          (ULift.ringEquiv.symm.toRingHom.comp
            (algebraMap R (Localization.Away (f k))))
          (PrimeSpectrum.comap ULift.ringEquiv.toRingHom q) = p
        rw [← PrimeSpectrum.comap_comp_apply]
        convert hq using 1
        congr 1
    have hF : F.FaithfullyFlat := by
      apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
      refine ⟨?_, ?_⟩
      · let := F.toAlgebra
        have : Algebra.WeaklyEtale R (∀ j, A j) := hFw
        exact (RingHom.flat_algebraMap_iff).mpr inferInstance
      · intro p
        obtain ⟨j, q, hq⟩ := hpoints p
        refine ⟨PrimeSpectrum.comap (Pi.evalRingHom A j) q, ?_⟩
        rw [← PrimeSpectrum.comap_comp_apply]
        exact hq
    obtain ⟨t, ht⟩ := hsplit (∀ j, A j) F hF hFw
    have htF (x : R) : t (F x) = x := RingHom.congr_fun ht x
    let e : (∀ j, A j) := fun ⟨j⟩ ↦ match j with
      | none => 1
      | some _ => 0
    have hmem : ∀ k, t (Pi.single (ULift.up (some k)) 1) ∈ I := by
      intro k
      have hu : IsUnit (a (ULift.up (some k)) (f k)) := by
        exact (IsLocalization.Away.algebraMap_isUnit (f k)).map
          (ULift.ringEquiv : ULift.{v} (Localization.Away (f k)) ≃+* _).symm.toRingHom
      obtain ⟨c, hc⟩ := hu.exists_right_inv
      have heq : F (f k) * Pi.single (ULift.up (some k)) c = Pi.single (ULift.up (some k)) 1 := by
        ext j
        by_cases hj : j = ULift.up (some k)
        · subst j
          simpa [F] using hc
        · simp [hj]
      rw [← heq, map_mul, htF]
      exact I.mul_mem_right _ (hf k)
    have he : Ideal.Quotient.mk I (t e) = 1 := by
      have heq :
          e + ∑ k : Fin r, Pi.single (ULift.up (some k)) (1 : A (ULift.up (some k))) = 1 := by
        ext j
        rcases j with ⟨j⟩
        cases j with
        | none => simp [e]
        | some k =>
          rw [Pi.add_apply, Finset.sum_apply]
          simp only [e, zero_add]
          rw [Finset.sum_eq_single k]
          · simp
          · intro b _ hbk
            exact Pi.single_eq_of_ne (by simpa using hbk.symm) 1
          · simp
      have h := congrArg (fun x ↦ Ideal.Quotient.mk I (t x)) heq
      simpa only [map_add, map_sum, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (hmem _),
        Finset.sum_const_zero, add_zero] using h
    have heunit : IsUnit (algebraMap R B (t e)) := by
      apply IsLocalization.map_units B (⟨t e, ?_⟩ : S)
      change IsUnit (Ideal.Quotient.mk I (t e))
      rw [he]
      exact isUnit_one
    have heone : algebraMap R B (t e) = 1 := by
      apply (IsIdempotentElem.iff_eq_one_of_isUnit heunit).mp
      have heid : e * e = e := by
        ext ⟨j⟩; cases j <;> simp [e]
      change algebraMap R B (t e) * algebraMap R B (t e) = algebraMap R B (t e)
      rw [← map_mul, ← map_mul, heid]
    let inc : D → (∀ j, A j) := fun d ⟨j⟩ ↦ match j with
      | none => d
      | some _ => 0
    let s : D →+* B :=
      { toFun := fun d ↦ algebraMap R B (t (inc d))
        map_zero' := by
          have hi : inc 0 = 0 := by ext ⟨j⟩; cases j <;> rfl
          rw [hi, map_zero, map_zero]
        map_one' := by
          have hi : inc 1 = e := by ext ⟨j⟩; cases j <;> simp [inc, e]
          rw [hi]
          exact heone
        map_add' := by
          intro d d'
          have hi : inc (d + d') = inc d + inc d' := by
            ext ⟨j⟩; cases j <;> simp [inc]
          simp only [hi, map_add]
        map_mul' := by
          intro d d'
          have hi : inc (d * d') = inc d * inc d' := by
            ext ⟨j⟩; cases j <;> simp [inc]
          simp only [hi, map_mul] }
    refine ⟨s, IsLocalization.ringHom_ext S ?_⟩
    ext x
    change algebraMap R B (t (inc (g (algebraMap R B x)))) = algebraMap R B x
    have hi : inc (g (algebraMap R B x)) = e * F x := by
      ext j
      rcases j with ⟨j⟩
      cases j <;> simp [inc, e, F, a]
      rfl
    rw [hi, map_mul, map_mul, heone, one_mul, htF]

end IsLocalization

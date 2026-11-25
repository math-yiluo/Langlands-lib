/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.RetractionsStrictlyHenselian
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
public import Mathlib.RingTheory.Unramified.Finite

/-!
# Étale algebras over strictly henselian local rings split off copies of the base

Let `A` be a strictly henselian local ring with maximal ideal `m` and `B` an étale `A`-algebra.
Every point of the closed fibre of `Spec B` is the image of a section `σ : B →ₐ[A] A`, and a
section of an unramified algebra cuts out a copy of `A` in `B`: there is an idempotent `e` with
`b * e = σ b * e` for all `b`. Gathering finitely many of these idempotents, one obtains an
idempotent `f ∈ m B` such that `B (1 - f)` is spanned over `A` by idempotents. In other words,
`B ≅ Aⁿ × B''` with `B'' = m B''`.

## Main statements

- `Algebra.FormallyUnramified.exists_isIdempotentElem_of_algHom`: the idempotent cut out by a
  section of an unramified algebra.
- `Algebra.Etale.exists_isIdempotentElem_mem_map_maximalIdeal`: the splitting of an étale
  algebra over a strictly henselian local ring.
-/

@[expose] public section

universe u

open IsLocalRing
open scoped TensorProduct

/-- A section `σ : B →ₐ[A] A` of a formally unramified algebra of essentially finite type is cut
out by an idempotent: there is an idempotent `e` of `B` with `σ e = 1` and `b * e = σ b * e` for
all `b`. It is the image of the diagonal idempotent of `B ⊗[A] B` under `σ ⊗ id`. -/
theorem Algebra.FormallyUnramified.exists_isIdempotentElem_of_algHom {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    (σ : B →ₐ[A] A) :
    ∃ e : B, IsIdempotentElem e ∧ σ e = 1 ∧ ∀ b, b * e = algebraMap A B (σ b) * e := by
  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := B)).mp inferInstance
  let φ : B ⊗[A] B →ₐ[A] B :=
    Algebra.TensorProduct.productMap ((Algebra.ofId A B).comp σ) (AlgHom.id A B)
  have hφ : σ.comp φ = σ.comp (TensorProduct.lmul' A) := by
    ext <;> simp [φ]
  have key (b : B) : b * φ t = algebraMap A B (σ b) * φ t := by
    have h := congrArg φ (ht b)
    simp only [map_mul, map_sub, map_zero, φ, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.comp_apply, map_one, AlgHom.id_apply, one_mul, mul_one, Algebra.ofId_apply,
      sub_mul] at h
    exact sub_eq_zero.mp h
  have hσ : σ (φ t) = 1 := by
    rw [← AlgHom.comp_apply, hφ, AlgHom.comp_apply, ht1, map_one]
  refine ⟨φ t, ?_, hσ, key⟩
  rw [IsIdempotentElem, key, hσ, map_one, one_mul]

/-- Over a strictly henselian local ring `A`, every prime `q` of an étale `A`-algebra `B` lying
over the maximal ideal is the preimage of the maximal ideal under a section `B →ₐ[A] A`. -/
theorem Algebra.Etale.exists_algHom_mem_maximalIdeal_iff {A : Type u} [CommRing A]
    [IsStrictlyHenselianLocalRing A] {B : Type u} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime] (hq : q.comap (algebraMap A B) = maximalIdeal A) :
    ∃ σ : B →ₐ[A] A, ∀ b, σ b ∈ maximalIdeal A ↔ b ∈ q := by
  have H (D : Type u) [CommRing D] [Algebra A D] (_ : Algebra.Etale A D)
      (hD : Function.Surjective (PrimeSpectrum.comap (algebraMap A D))) :
      ∃ f : D →+* A, f.comp (algebraMap A D) = RingHom.id A := by
    have : Module.FaithfullyFlat A D := .of_comap_surjective hD
    exact IsStrictlyHenselianLocalRing.exists_retraction_of_weaklyEtale
  obtain ⟨ρ, hρ⟩ := Algebra.Etale.exists_algHom_localization_atPrime_comap_eq H
    (maximalIdeal A) B q hq
  let e : A ≃ₐ[A] Localization.AtPrime (maximalIdeal A) :=
    IsLocalization.atUnits A (maximalIdeal A).primeCompl fun x hx ↦ by
      by_contra h
      exact hx ((mem_maximalIdeal x).mpr h)
  refine ⟨e.symm.toAlgHom.comp ρ, fun b ↦ ?_⟩
  rw [← hρ, Ideal.mem_comap, AlgHom.comp_apply, mem_maximalIdeal, mem_nonunits_iff,
    mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr (isUnit_map_iff e.symm (ρ b))

/-- **Étale algebras over a strictly henselian local ring split.** Let `A` be a strictly
henselian local ring and `B` an étale `A`-algebra. There is an idempotent `f ∈ m B` such that
`B (1 - f)` is spanned over `A` by idempotents; i.e. `B ≅ Aⁿ × B''` with `B'' = m B''`.

Each point `q` of the closed fibre is cut out by a section `σ_q`, hence by an idempotent `e_q`
with `σ_q (e_q) = 1` and `b e_q = σ_q (b) e_q`; finitely many of the open sets `D(e_q)` cover the
quasi-compact closed fibre and `f = ∏ (1 - e_q)` lies in every prime over `m`, hence in `m B`. -/
theorem Algebra.Etale.exists_isIdempotentElem_mem_map_maximalIdeal {A : Type u} [CommRing A]
    [IsStrictlyHenselianLocalRing A] (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.Etale A B] :
    ∃ f : B, IsIdempotentElem f ∧ f ∈ (maximalIdeal A).map (algebraMap A B) ∧
      ∀ b : B, b * (1 - f) ∈ Submodule.span A {e : B | IsIdempotentElem e} := by
  classical
  set Z := PrimeSpectrum.zeroLocus ((maximalIdeal A).map (algebraMap A B) : Set B)
  have hZ (p : Z) : (p.1.asIdeal).comap (algebraMap A B) = maximalIdeal A := by
    refine ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [← Ideal.map_le_iff_le_comap]
    exact p.2
  choose σ hσ using fun p : Z ↦ exists_algHom_mem_maximalIdeal_iff p.1.asIdeal (hZ p)
  choose e he he1 heb using fun p : Z ↦
    Algebra.FormallyUnramified.exists_isIdempotentElem_of_algHom (σ p)
  have hcover : (Z : Set (PrimeSpectrum B)) ⊆
      ⋃ p : Z, (PrimeSpectrum.basicOpen (e p) : Set (PrimeSpectrum B)) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    intro hmem
    have h := (hσ ⟨x, hx⟩ _).mpr hmem
    rw [he1] at h
    exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  obtain ⟨t, ht⟩ := (PrimeSpectrum.isClosed_zeroLocus _).isCompact.elim_finite_subcover _
    (fun p ↦ (PrimeSpectrum.basicOpen (e p)).isOpen) hcover
  set f := ∏ p ∈ t, (1 - e p)
  -- `f` and the partial products are idempotent, and `b (1 - f)` is spanned by idempotents.
  have key (s : Finset Z) : IsIdempotentElem (∏ p ∈ s, (1 - e p)) ∧
      ∀ b : B, b * (1 - ∏ p ∈ s, (1 - e p)) ∈ Submodule.span A {e : B | IsIdempotentElem e} := by
    induction s using Finset.induction_on with
    | empty => simp [IsIdempotentElem]
    | insert p s hps ih =>
      rw [Finset.prod_insert hps]
      refine ⟨(he p).one_sub.mul ih.1, fun b ↦ ?_⟩
      have h : b * (1 - (1 - e p) * ∏ i ∈ s, (1 - e i)) =
          b * (1 - ∏ i ∈ s, (1 - e i)) + σ p b • (e p * ∏ i ∈ s, (1 - e i)) := by
        rw [Algebra.smul_def, ← mul_assoc, ← heb]
        ring
      rw [h]
      exact add_mem (ih.2 b) (Submodule.smul_mem _ _
        (Submodule.subset_span ((he p).mul ih.1)))
  refine ⟨f, (key t).1, ?_, (key t).2⟩
  -- `f` lies in every prime over `m`, hence in the radical of `m B`.
  have hrad : f ∈ ((maximalIdeal A).map (algebraMap A B)).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hP, hPp⟩
    have hPZ : (⟨P, hPp⟩ : PrimeSpectrum B) ∈ Z := hP
    obtain ⟨p, hpt, hp⟩ := Set.mem_iUnion₂.mp (ht hPZ)
    have hpP : 1 - e p ∈ P := by
      refine (hPp.mem_or_mem ?_).resolve_left hp
      rw [mul_sub, mul_one, (he p).eq, sub_self]
      exact P.zero_mem
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hpt) hpP
  obtain ⟨n, hn⟩ := hrad
  rcases n with _ | n
  · rw [pow_zero] at hn
    simpa using Ideal.mul_mem_left _ f hn
  · rwa [(key t).1.pow_succ_eq] at hn

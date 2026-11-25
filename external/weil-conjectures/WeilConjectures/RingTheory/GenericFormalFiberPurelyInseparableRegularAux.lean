/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

import WeilConjectures.RingTheory.PowerSeriesPolynomialFormalFiber
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.GeometricRegularityFieldIso
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.CompletionRegularLocal

/-!
# Regularity of the generic formal fibre in field and Cohen models

Source: Stacks Project, More on Algebra, Proposition Tag 07PS, last two paragraphs,
and Lemma Tag 07PR in positive characteristic.
(blueprint: new-lem-generic-formal-fibre-purely-inseparable-regular-field)
(blueprint: new-lem-generic-formal-fibre-purely-inseparable-regular-cohen)
-/

@[expose] public section

universe u

private def semilinearEquiv
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B] (e : R ≃+* S)
    [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r)) :
    LinearEquiv (e : R →+* S) (σ' := (e.symm : S →+* R)) A B :=
  { f.toAddEquiv with
    map_smul' := fun r x ↦ by
      simp only [Algebra.smul_def]
      exact (f.map_mul _ _).trans (congrArg (fun t ↦ t * f x) (h r)) }

private def tensorRingEquiv
    {R S A B C D : Type*}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra S C] [Algebra S D]
    (e : R ≃+* S) (f : A ≃+* C) (g : B ≃+* D)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S C (e r))
    (hg : ∀ r, g (algebraMap R B r) = algebraMap S D (e r)) :
    TensorProduct R A B ≃+* TensorProduct S C D := by
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.of_ringEquiv_symm e
  let F := semilinearEquiv e f hf
  let G := semilinearEquiv e g hg
  let E := TensorProduct.congr (σ₂₁ := (e.symm : S →+* R)) F G
  refine { E.toAddEquiv with map_mul' := ?_ }
  intro x y
  change E (x * y) = E x * E y
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [E, TensorProduct.congr_tmul]
      change f (a * c) ⊗ₜ[S] g (b * d) = (f a ⊗ₜ[S] g b) * (f c ⊗ₜ[S] g d)
      simp only [map_mul, Algebra.TensorProduct.tmul_mul_tmul]

private theorem genericFiber_transport {A B : Type u} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] (e : A ≃+* B) (P : Ideal A) [P.IsPrime]
    (Q : Ideal B) [Q.IsPrime] (hPQ : P = Q.comap e.toRingHom)
    (hB : Algebra.IsGeometricallyRegular (⊥ : Ideal B).ResidueField
      ((⊥ : Ideal B).Fiber
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (Localization.AtPrime Q)))) :
    Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
          (Localization.AtPrime P))) := by
  let L := Localization.localRingEquiv P Q e hPQ
  obtain ⟨E, hE⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) L
    (IsLocalRing.map_ringEquiv_maximalIdeal L).symm
  have hbot : (⊥ : Ideal A) = (⊥ : Ideal B).comap e.toRingHom := by
    ext a
    simp
  let σ := Ideal.residueFieldRingEquiv (⊥ : Ideal A) (⊥ : Ideal B) e hbot
  have hσ (a : A) : σ (algebraMap A (⊥ : Ideal A).ResidueField a) =
      algebraMap B (⊥ : Ideal B).ResidueField (e a) :=
    Ideal.ResidueField.map_algebraMap _ _ e.toRingHom hbot a
  have hC (a : A) :
      E (algebraMap A
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
          (Localization.AtPrime P)) a) =
      algebraMap B
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
          (Localization.AtPrime Q)) (e a) := by
    rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime P)]
    have hEa := DFunLike.congr_fun hE ((algebraMap A (Localization.AtPrime P)) a)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hEa
    rw [hEa]
    change algebraMap _ _
      (Localization.localRingHom P Q e.toRingHom hPQ
        (algebraMap A (Localization.AtPrime P) a)) = _
    rw [Localization.localRingHom_to_map]
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) _ (e a)).symm
  let T := tensorRingEquiv e σ E hσ hC
  apply Algebra.isGeometricallyRegular_of_fieldIso σ.symm T.symm ?_ hB
  intro x y
  apply T.injective
  simp only [RingEquiv.apply_symm_apply]
  -- The tensor equivalence respects multiplication and the residue-field action.
  symm
  change T (σ.symm x • T.symm y) = x • y
  rw [Algebra.smul_def, map_mul]
  have ht : T (algebraMap (⊥ : Ideal A).ResidueField _ (σ.symm x)) =
      algebraMap (⊥ : Ideal B).ResidueField _ x := by
    change σ (σ.symm x) ⊗ₜ[B] E 1 = x ⊗ₜ[B] 1
    simp
  rw [ht, RingEquiv.apply_symm_apply, Algebra.smul_def]

private theorem regular_genericFiber (A : Type u) [CommRing A] [IsDomain A]
    [IsRegularLocalRing A] (P : Ideal A) [P.IsPrime] :
    IsRegularRing ((⊥ : Ideal A).Fiber
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P))) := by
  let R := Localization.AtPrime P
  let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have : IsRegularLocalRing R :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing P).1
  have : IsRegularLocalRing C := (AdicCompletion.isRegularLocalRing_iff R).mp inferInstance
  have : IsRegularRing C :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal C)).2
  let F := (⊥ : Ideal A).ResidueField
  let M := Algebra.algebraMapSubmonoid C (nonZeroDivisors A)
  let : Algebra C (TensorProduct A F C) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization M (TensorProduct A F C) := inferInstance
  have : IsRegularRing (Localization M) := by
    apply isRegularRing_iff.mpr
    intro q hq
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (IsLocalization.algEquiv M (Localization M) (TensorProduct A F C)).toRingEquiv

private theorem regular_genericFiber_charZero (A : Type u) [CommRing A] [IsDomain A]
    [IsRegularLocalRing A] [CharZero A] (P : Ideal A) [P.IsPrime]
    (k' : Type u) [Field k'] [Algebra ((⊥ : Ideal A).ResidueField) k']
    [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'] :
    IsRegularRing (TensorProduct ((⊥ : Ideal A).ResidueField) k'
      ((⊥ : Ideal A).Fiber
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
          (Localization.AtPrime P)))) := by
  let F := (⊥ : Ideal A).ResidueField
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (Localization.AtPrime P)
  have : CharZero F := IsFractionRing.charZero_of_isFractionRing A
  have : IsRegularRing ((⊥ : Ideal A).Fiber C) := regular_genericFiber A P
  have hb := IsPurelyInseparable.bijective_algebraMap_of_isSeparable F k'
  let E := AlgEquiv.ofBijective
    (Algebra.TensorProduct.includeRight :
      ((⊥ : Ideal A).Fiber C) →ₐ[F] TensorProduct F k' ((⊥ : Ideal A).Fiber C))
    (Algebra.TensorProduct.includeRight_bijective hb)
  exact IsRegularRing.of_ringEquiv E.toRingEquiv

private theorem cohen_charZero (Λ : Type u) [CommRing Λ] (p : ℕ)
    (hc : IsCohenRing p Λ) : CharZero Λ := by
  obtain ⟨hp, hd, hv, hm, _⟩ := hc
  have := hd
  have := hv
  apply (CharZero.charZero_iff_forall_prime_ne_zero Λ).mpr
  intro q hq hzero
  by_cases heq : q = p
  · subst q
    have hbot : IsLocalRing.maximalIdeal Λ = ⊥ := by
      rw [hm, hzero, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_isField Λ
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
  · have hcop : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr
      (fun h ↦ heq ((hq.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one).symm)
    have hunit : IsUnit (p : Λ) := by
      have h : IsCoprime (p : Λ) (q : Λ) := by
        simpa only [map_natCast] using hcop.isCoprime.map (Int.castRingHom Λ)
      simpa only [hzero, isCoprime_zero_right] using h
    have hmem : (p : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
      rw [hm]
      exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit

/-- Regularity of the purely inseparable tensor product in the field-model case.
Source: Stacks Project, More on Algebra, Proposition 07PS, last two paragraphs.
This is the field-model branch of the generic formal fibre argument.
(blueprint: new-lem-generic-formal-fibre-purely-inseparable-regular-field) -/
theorem isRegular_genericFormalFiber_fieldModel
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (k : Type u) [Field k] (d : ℕ)
    (e : Nonempty (A ≃+* MvPowerSeries (Fin d) k))
    (P : Ideal A) [P.IsPrime]
    (k' : Type (max u u)) [Field k']
    [Algebra ((⊥ : Ideal A).ResidueField) k']
    [Module.Finite ((⊥ : Ideal A).ResidueField) k']
    [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'] :
    IsRegularRing
      (TensorProduct ((⊥ : Ideal A).ResidueField) k'
        ((⊥ : Ideal A).Fiber
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
            (Localization.AtPrime P)))) := by
  obtain ⟨e⟩ := e
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hzero
  · have : Fact (ringChar k).Prime := ⟨hp⟩
    let B := MvPolynomial (Fin 0) (MvPowerSeries (Fin d) k)
    have : IsDomain (MvPowerSeries (Fin d) k) := NoZeroDivisors.to_isDomain _
    let E : A ≃+* B := e.trans (MvPolynomial.isEmptyRingEquiv _ (Fin 0)).symm
    let Q : Ideal B := P.comap E.symm.toRingHom
    have : Q.IsPrime := Ideal.comap_isPrime _ P
    have hPQ : P = Q.comap E.toRingHom := by
      ext a
      change (a ∈ P) ↔ E.symm (E a) ∈ P
      rw [RingEquiv.symm_apply_apply]
    have hB := (MvPowerSeries.formalFiber_polynomial_isGeometricallyRegular
      k (ringChar k) d 0 Q).2
    exact (genericFiber_transport E P Q hPQ hB).2 k'
  · have : CharP k 0 := hzero ▸ inferInstance
    have : CharZero k := CharP.charP_to_charZero k
    have : CharZero (MvPowerSeries (Fin d) k) :=
      charZero_of_injective_ringHom (f := MvPowerSeries.C) MvPowerSeries.C_injective
    have : CharZero A := charZero_of_injective_ringHom
      (f := e.symm.toRingHom) e.symm.injective
    exact regular_genericFiber_charZero A P k'

/-- Regularity of the purely inseparable tensor product in the Cohen-model case.
Source: Stacks Project, More on Algebra, Proposition 07PS, last two paragraphs.
This is the Cohen-model branch of the generic formal fibre argument.
(blueprint: new-lem-generic-formal-fibre-purely-inseparable-regular-cohen) -/
theorem isRegular_genericFormalFiber_cohenModel
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (Λ : Type u) [CommRing Λ] (d p : ℕ)
    (hc : IsCohenRing p Λ)
    (e : Nonempty (A ≃+* MvPowerSeries (Fin d) Λ))
    (P : Ideal A) [P.IsPrime]
    (k' : Type (max u u)) [Field k']
    [Algebra ((⊥ : Ideal A).ResidueField) k']
    [Module.Finite ((⊥ : Ideal A).ResidueField) k']
    [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'] :
    IsRegularRing
      (TensorProduct ((⊥ : Ideal A).ResidueField) k'
        ((⊥ : Ideal A).Fiber
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
            (Localization.AtPrime P)))) := by
  obtain ⟨e⟩ := e
  have : CharZero Λ := cohen_charZero Λ p hc
  have : CharZero (MvPowerSeries (Fin d) Λ) :=
    charZero_of_injective_ringHom (f := MvPowerSeries.C) MvPowerSeries.C_injective
  have : CharZero A := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  exact regular_genericFiber_charZero A P k'

end

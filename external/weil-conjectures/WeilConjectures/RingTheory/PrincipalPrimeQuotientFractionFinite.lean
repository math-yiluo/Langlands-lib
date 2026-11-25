/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.RingTheory.DimOneResidueFieldsFinite
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Finite quotient fraction fields over a principal prime

Source: Stacks Project, Tags 032P and 031F, residue-field finiteness.
(blueprint: lem-weil-pbc-principal-prime-quotient-fraction-finite).
-/

@[expose] public section

universe uR uS uK uL
set_option autoImplicit false

attribute [local instance] FractionRing.liftAlgebra

private theorem finite_fraction_transport
    {A B K L K' L' : Type*} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Field K] [Field L] [Field K'] [Field L']
    [Algebra A K] [Algebra A K'] [IsFractionRing A K]
    [Algebra B L] [Algebra B L'] [Algebra K L] [Algebra K' L']
    [Algebra A L] [Algebra A L'] [IsScalarTower A K L]
    [IsScalarTower A K' L'] [IsScalarTower A B L] [IsScalarTower A B L']
    [FiniteDimensional K L] (e : K ≃ₐ[A] K') (f : L ≃ₐ[B] L') :
    FiniteDimensional K' L' := by
  exact Module.Finite.of_equiv_equiv e.toRingEquiv f.toRingEquiv
    (by ext a; exact IsFractionRing.algEquiv_commutes e f a)

/-- A prime over a principal prime in a finite extension of fraction fields has
finite quotient fraction field extension.
Source: Stacks Project, Tag 032P, localization and application of Tag 031F.
(blueprint: lem-weil-pbc-principal-prime-quotient-fraction-finite).

Proof: If x = 0, the contraction of Q is zero. Localizing S at the nonzero
 elements of R gives a K-subalgebra of L. Each element is algebraic over K,
 so this domain is a field. Consequently the only prime over zero is zero,
 and the quotient fraction fields identify with K and L. If x is nonzero,
 the principal prime xR has height one by the principal ideal theorem and
 the strict chain (0) < xR. Its localization is a one-dimensional Noetherian
 local domain. Localize S at Q; the fraction fields are still K and L,
 and the localized maximal ideal contracts to the base maximal ideal.
 Apply Tag 031F to obtain a finite extension of residue fields. For any
 prime ideal, its residue field is a fraction field of the quotient domain.
 Transport the finite-dimensionality along the canonical equivalences with
 the fraction fields of R/(Q ∩ R) and S/Q. No integrality or normality of S
 is needed for this residue-field argument. -/
theorem principal_prime_quotient_fraction_finite
    (R : Type uR) (S : Type uS) (K : Type uK) (L : Type uL)
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [FiniteDimensional K L]
    (x : R) (Q : Ideal S) [Q.IsPrime]
    (hcontract : Q.comap (algebraMap R S) = Ideal.span ({x} : Set R)) :
    letI : FaithfulSMul (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
    FiniteDimensional (FractionRing (R ⧸ Q.comap (algebraMap R S)))
      (FractionRing (S ⧸ Q)) := by
  classical
  let p : Ideal R := Q.comap (algebraMap R S)
  let : FaithfulSMul (R ⧸ p) (S ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  by_cases hx : x = 0
  · have hp : p = ⊥ := by simp [p, hcontract, hx]
    have hQ : Q = ⊥ := by
      apply eq_bot_iff.mpr
      intro s hs
      by_contra hs0
      have halg : IsAlgebraic R s := by
        apply (isAlgebraic_algebraMap_iff (IsFractionRing.injective S L)).mp
        exact (IsFractionRing.isAlgebraic_iff R K L).mpr
          (Algebra.IsAlgebraic.isAlgebraic _)
      exact (Q.under_ne_bot_of_algebraic_mem hs0 hs halg) hp
    subst Q
    let A := R ⧸ p
    let B := S ⧸ (⊥ : Ideal S)
    let eR : A ≃+* R := (Ideal.quotEquivOfEq hp).trans (RingEquiv.quotientBot R)
    let eS : B ≃+* S := RingEquiv.quotientBot S
    let : Algebra A K := ((algebraMap R K).comp eR.toRingHom).toAlgebra
    let : Algebra B L := ((algebraMap S L).comp eS.toRingHom).toAlgebra
    let : Algebra A L := ((algebraMap R L).comp eR.toRingHom).toAlgebra
    let : IsFractionRing A K := IsFractionRing.of_ringEquiv_left eR (fun _ ↦ rfl)
    let : IsFractionRing B L := IsFractionRing.of_ringEquiv_left eS (fun _ ↦ rfl)
    let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap R L (eR a) = algebraMap K L (algebraMap R K (eR a))
      exact IsScalarTower.algebraMap_apply R K L _
    let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change algebraMap R L a = algebraMap S L (algebraMap R S a)
      exact IsScalarTower.algebraMap_apply R S L a
    exact finite_fraction_transport
      (IsLocalization.algEquiv (nonZeroDivisors A) K (FractionRing A))
      (IsLocalization.algEquiv (nonZeroDivisors B) L (FractionRing B))
  · let Rp := Localization.AtPrime p
    let Sp := Localization.AtPrime Q
    let : Algebra Rp K := IsLocalization.localizationAlgebraOfSubmonoidLe Rp K
      p.primeCompl (nonZeroDivisors R) p.primeCompl_le_nonZeroDivisors
    let : IsScalarTower R Rp K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le Rp K
        p.primeCompl (nonZeroDivisors R) p.primeCompl_le_nonZeroDivisors
    let : IsFractionRing Rp K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl Rp K
    let : Algebra Sp L := IsLocalization.localizationAlgebraOfSubmonoidLe Sp L
      Q.primeCompl (nonZeroDivisors S) Q.primeCompl_le_nonZeroDivisors
    let : IsScalarTower S Sp L :=
      IsLocalization.localization_isScalarTower_of_submonoid_le Sp L
        Q.primeCompl (nonZeroDivisors S) Q.primeCompl_le_nonZeroDivisors
    let : IsFractionRing Sp L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl Sp L
    let φ : Rp →+* Sp := Localization.localRingHom p Q (algebraMap R S) rfl
    have hcompat : ∀ r : Rp,
        algebraMap K L (algebraMap Rp K r) = algebraMap Sp L (φ r) := by
      have heq : (algebraMap K L).comp (algebraMap Rp K) =
          (algebraMap Sp L).comp φ := by
        apply IsLocalization.ringHom_ext p.primeCompl
        ext r
        change algebraMap K L (algebraMap Rp K (algebraMap R Rp r)) =
          algebraMap Sp L (φ (algebraMap R Rp r))
        rw [show φ (algebraMap R Rp r) = algebraMap S Sp (algebraMap R S r) from
          Localization.localRingHom_to_map p Q (algebraMap R S) rfl r]
        rw [← IsScalarTower.algebraMap_apply R Rp K,
          ← IsScalarTower.algebraMap_apply S Sp L,
          ← IsScalarTower.algebraMap_apply R K L,
          ← IsScalarTower.algebraMap_apply R S L]
      exact DFunLike.congr_fun heq
    have hφ : Function.Injective φ := by
      intro a b h
      apply IsFractionRing.injective Rp K
      apply (algebraMap K L).injective
      rw [hcompat, hcompat, h]
    have hdim : ringKrullDim Rp = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rp]
      have hunit : ¬ IsUnit x := by
        intro hu
        have : p = ⊤ := hcontract.trans (Ideal.span_singleton_eq_top.mpr hu)
        exact (inferInstance : p.IsPrime).ne_top this
      rw [show p = Ideal.span ({x} : Set R) from hcontract]
      exact_mod_cast Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hx) hunit
    let n : PrimeSpectrum Sp := ⟨IsLocalRing.maximalIdeal Sp, inferInstance⟩
    have hn : n.asIdeal.comap φ = IsLocalRing.maximalIdeal Rp :=
      IsLocalRing.maximalIdeal_comap φ
    have hf := (Ideal.dim_one_residue_fields_finite Rp Sp K L φ hφ hcompat hdim).2.2 n hn
    let qR := IsLocalRing.maximalIdeal Rp
    let qS := IsLocalRing.maximalIdeal Sp
    let E := qR.ResidueField
    let F := qS.ResidueField
    let ιR : p.ResidueField →+* E := Ideal.ResidueField.map p qR
      (algebraMap R Rp) (IsLocalization.AtPrime.under_maximalIdeal Rp p).symm
    let ιS : Q.ResidueField →+* F := Ideal.ResidueField.map Q qS
      (algebraMap S Sp) (IsLocalization.AtPrime.under_maximalIdeal Sp Q).symm
    let : Algebra E F := (Ideal.ResidueField.map qR qS φ hn.symm).toAlgebra
    have : FiniteDimensional E F := hf
    let A := R ⧸ p
    let B := S ⧸ Q
    let : Algebra A E := (ιR.comp (algebraMap A p.ResidueField)).toAlgebra
    let : Algebra B F := (ιS.comp (algebraMap B Q.ResidueField)).toAlgebra
    let : Algebra A F := ((algebraMap E F).comp (algebraMap A E)).toAlgebra
    let : IsScalarTower A E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let : IsScalarTower A B F := IsScalarTower.of_algebraMap_eq fun a ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change (Ideal.ResidueField.map qR qS φ hn.symm)
        (ιR (algebraMap R p.ResidueField a)) =
        ιS (algebraMap S Q.ResidueField (algebraMap R S a))
      rw [Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.map_algebraMap,
        Ideal.ResidueField.map_algebraMap]
      congr 1
      exact Localization.localRingHom_to_map p Q (algebraMap R S) rfl a
    let eR : p.ResidueField ≃ₐ[A] E :=
      { RingEquiv.ofBijective ιR
          (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
            (RingHom.surjectiveOnStalks_of_isLocalization p.primeCompl Rp) p qR
              (IsLocalization.AtPrime.under_maximalIdeal Rp p).symm) with
        commutes' := fun _ ↦ rfl }
    let eS : Q.ResidueField ≃ₐ[B] F :=
      { RingEquiv.ofBijective ιS
          (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
            (RingHom.surjectiveOnStalks_of_isLocalization Q.primeCompl Sp) Q qS
              (IsLocalization.AtPrime.under_maximalIdeal Sp Q).symm) with
        commutes' := fun _ ↦ rfl }
    let : IsFractionRing A E := IsFractionRing.of_algEquiv eR
    let : IsFractionRing B F := IsFractionRing.of_algEquiv eS
    exact finite_fraction_transport
      (IsLocalization.algEquiv (nonZeroDivisors A) E (FractionRing A))
      (IsLocalization.algEquiv (nonZeroDivisors B) F (FractionRing B))

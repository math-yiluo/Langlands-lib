/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Algebraic.Integral

/-! # Local DVR diagram of a normalized compositum

Source: Stacks Project, Tags 032L, 00PD, and Remark 09EM.
(blueprint: lem-sbc-dvr-normalized-compositum-local-diagram) -/

@[expose] public section

universe u

namespace RingTheory

/-- A prime of a finite normalization selects compatible local DVRs in the two fields.

Source: Stacks Project, Tag 032L, Tag 00PD, and the normalization diagram in
Remark 09EM preceding Abhyankar's lemma 0BRM.
(blueprint: lem-sbc-dvr-normalized-compositum-local-diagram)

Proof: The field map iE is injective. The kernel of A -> F contracts to zero
in B by compatibility; integrality and the domain A imply that this kernel
is zero. Algebraicity of E over B follows by clearing fraction-field
denominators; it transfers through iE and extends from B to A. Generation
therefore makes F algebraic over A. The integral closure S has fraction
field F by the algebraic integral-closure theorem. The finite integral closure S
of A in F is a normal one-dimensional Noetherian domain; Q is nonzero since
it contracts to the nonzero maximal ideal of A. Thus S_Q is a DVR and has
fraction field F. Restrict iE to C = integralClosure B E: its image lies in
S, since a monic equation over B is also a monic equation over A. Contract
Q along this restriction to obtain R. Compatibility shows R lies above the
maximal ideal of B. Since C is finite over B, it too is a normal
one-dimensional Noetherian domain; consequently C_R is a DVR with fraction
field E. Localizing the restriction C -> S at these primes produces the
local homomorphism j and its two compatibility identities. The canonical
map B -> C_R is local. The ramification length formula in a DVR identifies
R.ramificationIdx B with the exponent in the displayed ideal equality.
Finally identify the prime residue fields at R and its contraction with
those of C_R and B; transport the separability in htame along these canonical
field isomorphisms. Its unit and divisibility assertions give the other two
returned properties. This construction uses no ramification cancellation
or assertion about the residue field of S_Q. -/
theorem dvr_normalized_compositum_local_diagram
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ)
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A] [FaithfulSMul B A]
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    [Algebra B E] [IsScalarTower B (FractionRing B) E]
    [FiniteDimensional (FractionRing B) E] [Algebra.IsSeparable (FractionRing B) E]
    [Module.Finite B (integralClosure B E)]
    (htame : ∀ (R : Ideal (integralClosure B E)) (hR : R.IsPrime),
      letI := hR
      R.comap (algebraMap B (integralClosure B E)) = IsLocalRing.maximalIdeal B →
      letI := Localization.AtPrime.algebraOfLiesOver (R.under B) R
      IsUnit (R.ramificationIdx B : B) ∧ R.ramificationIdx B ∣ n ∧
        Algebra.IsSeparable (R.under B).ResidueField R.ResidueField)
    (F : Type u) [Field F] [Algebra A F]
    (iE : E →+* F)
    (hcomm : ∀ b : B, iE (algebraMap B E b) =
      algebraMap A F (algebraMap B A b))
    (hgen : Algebra.adjoin A (Set.range iE) = ⊤)
    [Module.Finite A (integralClosure A F)]
    (Q : Ideal (integralClosure A F)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A (integralClosure A F)) = IsLocalRing.maximalIdeal A) :
    ∃ (R : Ideal (integralClosure B E)) (hR : R.IsPrime),
    letI := hR
    let U := Localization.AtPrime R
    let T := Localization.AtPrime Q
    ∃ (hBU : IsLocalHom (algebraMap B U))
      (_hU : IsDiscreteValuationRing U) (_hT : IsDiscreteValuationRing T)
      (aUE : Algebra U E),
    letI := aUE
    ∃ (_hfracUE : IsFractionRing U E) (_hBUE : IsScalarTower B U E)
      (aTF : Algebra T F),
    letI := aTF
    ∃ (_hfracTF : IsFractionRing T F) (_hATF : IsScalarTower A T F)
      (j : U →+* T),
      IsLocalHom j ∧
      (∀ b : B, j (algebraMap B U b) = algebraMap A T (algebraMap B A b)) ∧
      (∀ c : U, algebraMap T F (j c) = iE (algebraMap U E c)) ∧
      IsUnit (R.ramificationIdx B : B) ∧ R.ramificationIdx B ∣ n ∧
      (IsLocalRing.maximalIdeal B).map (algebraMap B U) =
        IsLocalRing.maximalIdeal U ^ R.ramificationIdx B ∧
      letI := hBU
      Algebra.IsSeparable (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField U) := by
  classical
  let C := integralClosure B E
  let S := integralClosure A F
  let T := Localization.AtPrime Q
  let : Algebra B F := ((algebraMap A F).comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A F := IsScalarTower.of_algebraMap_eq' rfl
  have hinjBE : Function.Injective (algebraMap B E) := by
    rw [IsScalarTower.algebraMap_eq B (FractionRing B) E]
    exact (algebraMap (FractionRing B) E).injective.comp
      (IsFractionRing.injective B (FractionRing B))
  have : FaithfulSMul B E := (faithfulSMul_iff_algebraMap_injective B E).2 hinjBE
  have : Module.IsTorsionFree B C := IsIntegralClosure.isTorsionFree B E
  let fE : E →ₐ[B] F := { toRingHom := iE, commutes' := hcomm }
  have hinjA : Function.Injective (algebraMap A F) := by
    apply (RingHom.injective_iff_ker_eq_bot _).2
    apply Ideal.eq_bot_of_under_eq_bot (R := B)
    ext b
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    rw [← IsScalarTower.algebraMap_apply B A F, ← fE.commutes]
    constructor
    · intro h
      apply hinjBE
      apply iE.injective
      change iE (algebraMap B E b) = 0 at h
      simpa only [map_zero] using h
    · intro h
      simp [h]
  have : Algebra.IsAlgebraic B E := IsFractionRing.comap_isAlgebraic_iff.mpr
    (inferInstance : Algebra.IsAlgebraic (FractionRing B) E)
  have : Algebra.IsAlgebraic A F := by
    constructor
    intro z
    have halg : (Algebra.adjoin A (Set.range iE)).IsAlgebraic :=
      Algebra.isAlgebraic_adjoin_iff.mpr (by
        rintro _ ⟨e, rfl⟩
        exact ((Algebra.IsAlgebraic.isAlgebraic (R := B) e).algHom fE).extendScalars
          (FaithfulSMul.algebraMap_injective B A))
    exact halg z (hgen ▸ (show z ∈ (⊤ : Subalgebra A F) from trivial))
  have hinjAS : Function.Injective (algebraMap A S) := by
    intro x y h
    apply hinjA
    simpa only [← IsScalarTower.algebraMap_apply A S F] using
      congrArg (algebraMap S F) h
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hinjAS
  have : IsFractionRing S F := integralClosure.isFractionRing_of_algebraic
    (fun a ha ↦ hinjA (ha.trans (map_zero _).symm))
  have : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  have : Ring.DimensionLEOne S := inferInstance
  have : IsIntegrallyClosed S := IsIntegrallyClosed.of_isIntegrallyClosedIn S F
  have : IsDedekindDomain S :=
    (isDedekindDomain_iff S F).2 ⟨inferInstance, inferInstance, inferInstance,
      fun hx ↦ IsIntegrallyClosed.algebraMap_eq_of_integral hx⟩
  let iC : C →+* S :=
    { toFun := fun c ↦ ⟨iE c, by
        have hc : IsIntegral B (iE c) := IsIntegral.map fE c.property
        exact hc.tower_top⟩
      map_zero' := Subtype.ext (map_zero iE)
      map_one' := Subtype.ext (map_one iE)
      map_add' := fun _ _ ↦ Subtype.ext (map_add iE _ _)
      map_mul' := fun _ _ ↦ Subtype.ext (map_mul iE _ _) }
  let R := Q.comap iC
  have hR : R.IsPrime := Ideal.comap_isPrime iC Q
  have hRover : R.comap (algebraMap B C) = IsLocalRing.maximalIdeal B := by
    change (Q.comap iC).comap (algebraMap B C) = _
    rw [Ideal.comap_comap]
    have hmap : iC.comp (algebraMap B C) =
        (algebraMap A S).comp (algebraMap B A) := by
      ext b
      exact hcomm b
    rw [hmap, ← Ideal.comap_comap, hQ]
    exact IsLocalRing.maximalIdeal_comap (algebraMap B A)
  have hQne : Q ≠ ⊥ := by
    intro h
    have hz : IsLocalRing.maximalIdeal A = ⊥ := by
      rw [← hQ, h]
      exact (RingHom.injective_iff_ker_eq_bot (algebraMap A S)).1
        (FaithfulSMul.algebraMap_injective A S)
    exact IsDiscreteValuationRing.not_isField A (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hz)
  have hT : IsDiscreteValuationRing T :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hQne T
  have : IsDedekindDomain C := inferInstance
  have hRne : R ≠ ⊥ := by
    intro h
    apply IsDiscreteValuationRing.not_a_field B
    rw [← hRover, h]
    exact (RingHom.injective_iff_ker_eq_bot (algebraMap B C)).1
      (FaithfulSMul.algebraMap_injective B C)
  let U := Localization.AtPrime R
  have hU : IsDiscreteValuationRing U :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hRne U
  have hBU : IsLocalHom (algebraMap B U) := by
    apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq B C U, ← Ideal.comap_comap]
    rw [show (IsLocalRing.maximalIdeal U).comap (algebraMap C U) = R from
      Localization.AtPrime.under_maximalIdeal (I := R)]
    exact hRover
  have : IsFractionRing C E :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing B) E
  let fUE := Localization.mapToFractionRing E R.primeCompl U
    R.primeCompl_le_nonZeroDivisors
  let aUE := fUE.toRingHom.toAlgebra
  let : Algebra U E := aUE
  have hCUE : IsScalarTower C U E :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (fUE.commutes c).symm
  have hBUE : IsScalarTower B U E := IsScalarTower.to₁₃₄ B C U E
  have hfracUE : IsFractionRing U E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization R.primeCompl U E
  let fTF := Localization.mapToFractionRing F Q.primeCompl T
    Q.primeCompl_le_nonZeroDivisors
  let aTF := fTF.toRingHom.toAlgebra
  let : Algebra T F := aTF
  have hSTF : IsScalarTower S T F :=
    IsScalarTower.of_algebraMap_eq fun s ↦ (fTF.commutes s).symm
  have hATF : IsScalarTower A T F := IsScalarTower.to₁₃₄ A S T F
  have hfracTF : IsFractionRing T F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl T F
  let j : U →+* T := Localization.localRingHom R Q iC rfl
  have hj : IsLocalHom j := Localization.isLocalHom_localRingHom R Q iC rfl
  have hjB : ∀ b : B, j (algebraMap B U b) =
      algebraMap A T (algebraMap B A b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B C U,
      Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply A S T]
    congr 1
    apply Subtype.ext
    exact hcomm b
  have hjE : ∀ c : U, algebraMap T F (j c) = iE (algebraMap U E c) := by
    have hh : (algebraMap T F).comp j = iE.comp (algebraMap U E) := by
      apply IsLocalization.ringHom_ext R.primeCompl
      ext c
      change algebraMap T F
        (Localization.localRingHom R Q iC rfl (algebraMap C U c)) =
        iE (algebraMap U E (algebraMap C U c))
      rw [Localization.localRingHom_to_map R Q iC rfl c,
        ← IsScalarTower.algebraMap_apply S T F,
        ← IsScalarTower.algebraMap_apply C U E]
      rfl
    exact RingHom.congr_fun hh
  have hinjBU : Function.Injective (algebraMap B U) := by
    intro x y h
    apply hinjBE
    simpa only [← IsScalarTower.algebraMap_apply B U E] using
      congrArg (algebraMap U E) h
  have hIne : (IsLocalRing.maximalIdeal B).map (algebraMap B U) ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_a_field B
      (((IsLocalRing.maximalIdeal B).map_eq_bot_iff_of_injective hinjBU).mp h)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible U
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hIne hπ
  have hk' : (IsLocalRing.maximalIdeal B).map (algebraMap B U) =
      IsLocalRing.maximalIdeal U ^ k := by
    rw [hk, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hram : R.ramificationIdx B = k := by
    rw [Ideal.ramificationIdx_def]
    change (Module.length U (U ⧸ (R.under B).map (algebraMap B U))).toNat = k
    rw [show R.under B = IsLocalRing.maximalIdeal B from hRover, hk',
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal U k, ENat.toNat_natCast]
  have hindexU : (IsLocalRing.maximalIdeal B).map (algebraMap B U) =
      IsLocalRing.maximalIdeal U ^ R.ramificationIdx B := by
    simpa only [hram] using hk'
  obtain ⟨he, hedvd, hsepR⟩ := htame R hR hRover
  refine ⟨R, hR, hBU, hU, hT, aUE, hfracUE, hBUE, aTF, hfracTF, hATF,
    j, hj, hjB, hjE, he, hedvd, hindexU, ?_⟩
  let := hBU
  let p := R.under B
  have hpmax : p.IsMaximal := by
    change (R.under B).IsMaximal
    rw [show R.under B = IsLocalRing.maximalIdeal B from hRover]
    infer_instance
  let := Localization.AtPrime.algebraOfLiesOver p R
  let : Algebra.IsSeparable p.ResidueField R.ResidueField := hsepR
  let ef : (B ⧸ p) ≃+* p.ResidueField :=
    .ofBijective _ p.bijective_algebraMap_quotient_residueField
  let eq : (B ⧸ p) ≃+* IsLocalRing.ResidueField B := Ideal.quotEquivOfEq hRover
  let e1 := ef.symm.trans eq
  have he1 (b : B) : e1 (algebraMap B p.ResidueField b) = IsLocalRing.residue B b := by
    change eq (ef.symm (algebraMap B p.ResidueField b)) = _
    rw [IsScalarTower.algebraMap_apply B (B ⧸ p) p.ResidueField]
    change eq (ef.symm (ef (Ideal.Quotient.mk p b))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  apply Algebra.IsSeparable.of_equiv_equiv e1 (RingEquiv.refl R.ResidueField)
  apply RingHom.ext
  intro x
  obtain ⟨b, rfl⟩ := p.algebraMap_residueField_surjective x
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom,
    he1, RingEquiv.refl_apply, IsLocalRing.ResidueField.algebraMap_residue]
  simp only [← IsScalarTower.algebraMap_apply B p.ResidueField R.ResidueField]
  rfl

end RingTheory

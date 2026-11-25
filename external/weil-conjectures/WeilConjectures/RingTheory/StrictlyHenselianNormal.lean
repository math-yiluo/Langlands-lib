/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.RingTheory.Invariant.Profinite

/-!
# Normal local domains with separably closed fraction field are strictly henselian

Let `A` be an integrally closed local domain whose fraction field `Ω` is separably closed (for
instance the localization at a maximal ideal of the integral closure of a domain in a separable
closure of its fraction field). Then `A` is strictly henselian
(`IsStrictlyHenselianLocalRing.of_isFractionRing_of_isSepClosed`).

This is `HenselianLocalRing.of_isSepClosed_fractionRing` together with
`IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing`.
-/

@[expose] public section

open IsLocalRing

namespace IsStrictlyHenselianLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsIntegrallyClosed A]

/-- An integrally closed local domain whose fraction field is separably closed is strictly
henselian. -/
theorem of_isFractionRing_of_isSepClosed (Ω : Type*) [Field Ω] [IsSepClosed Ω] [Algebra A Ω]
    [IsFractionRing A Ω] : IsStrictlyHenselianLocalRing A :=
  have := HenselianLocalRing.of_isSepClosed_fractionRing (A := A) Ω
  ⟨IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing Ω⟩

end IsStrictlyHenselianLocalRing

namespace Ideal

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]

/-- The localization at a prime `Q` of the integral closure of `R` in a field `Ω` maps to `Ω`. -/
noncomputable def atPrimeToField : Localization.AtPrime Q →+* Ω :=
  IsLocalization.lift (M := Q.primeCompl) (g := (integralClosure R Ω).val.toRingHom) fun s ↦
    IsUnit.mk0 _ fun h ↦ s.2 (by
      have : s.1 = 0 := Subtype.ext h
      rw [this]
      exact Q.zero_mem)

@[simp]
lemma atPrimeToField_algebraMap (b : integralClosure R Ω) :
    atPrimeToField Q (algebraMap _ (Localization.AtPrime Q) b) = b :=
  IsLocalization.lift_eq _ _

lemma injective_atPrimeToField : Function.Injective (atPrimeToField Q) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl x
  rw [atPrimeToField, IsLocalization.lift_mk'_spec, mul_zero] at hx
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨1, by rw [OneMemClass.coe_one, one_mul]; exact Subtype.ext hx⟩

section StrictlyHenselian

variable [IsSepClosed Ω] [Algebra.IsAlgebraic R Ω]

/-- The localization at a prime of the integral closure of a domain `R` in a separably closed
field `Ω` algebraic over `R` is strictly henselian. -/
theorem isStrictlyHenselianLocalRing_atPrime (hR : Function.Injective (algebraMap R Ω)) :
    IsStrictlyHenselianLocalRing (Localization.AtPrime Q) := by
  have : IsFractionRing (integralClosure R Ω) Ω := integralClosure.isFractionRing_of_algebraic
    fun x hx ↦ hR (hx.trans (map_zero _).symm)
  have : IsIntegrallyClosed (integralClosure R Ω) :=
    (IsIntegrallyClosed.integralClosure_eq_bot_iff Ω).mp integralClosure_idem
  have : IsIntegrallyClosed (Localization.AtPrime Q) :=
    isIntegrallyClosed_of_isLocalization _ Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime Q) Ω := (atPrimeToField Q).toAlgebra
  have : IsScalarTower (integralClosure R Ω) (Localization.AtPrime Q) Ω :=
    IsScalarTower.of_algebraMap_eq fun b ↦ (atPrimeToField_algebraMap Q b).symm
  have : IsFractionRing (Localization.AtPrime Q) Ω :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl _ Ω
  exact IsStrictlyHenselianLocalRing.of_isFractionRing_of_isSepClosed Ω

end StrictlyHenselian

section Action

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G Ω] [SMulCommClass G R Ω]

omit [Q.IsPrime] in
lemma comap_toRingHom_eq_of_mem_stabilizer {g : G} (hg : g ∈ MulAction.stabilizer G Q) :
    Q = Q.comap (MulSemiringAction.toRingHom G (integralClosure R Ω) g) := by
  ext x
  rw [Ideal.mem_comap, MulSemiringAction.toRingHom_apply]
  conv_rhs => rw [← (MulAction.mem_stabilizer_iff.1 hg : g • Q = Q)]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]

/-- The automorphism of `B_Q` induced by an element `g` of the stabiliser of `Q`. -/
noncomputable def atPrimeMap (g : G) (hg : g ∈ MulAction.stabilizer G Q) :
    Localization.AtPrime Q →+* Localization.AtPrime Q :=
  Localization.localRingHom Q Q (MulSemiringAction.toRingHom G (integralClosure R Ω) g)
    (comap_toRingHom_eq_of_mem_stabilizer Q hg)

instance (g : G) (hg : g ∈ MulAction.stabilizer G Q) : IsLocalHom (atPrimeMap Q g hg) :=
  Localization.isLocalHom_localRingHom _ _ _ _

lemma atPrimeMap_algebraMap (g : G) (hg : g ∈ MulAction.stabilizer G Q)
    (b : integralClosure R Ω) :
    atPrimeMap Q g hg (algebraMap _ (Localization.AtPrime Q) b) =
      algebraMap _ (Localization.AtPrime Q) (g • b) :=
  Localization.localRingHom_to_map _ _ _ _ _

lemma atPrimeMap_algebraMap_base (g : G) (hg : g ∈ MulAction.stabilizer G Q) (r : R) :
    atPrimeMap Q g hg (algebraMap R (Localization.AtPrime Q) r) =
      algebraMap R (Localization.AtPrime Q) r := by
  rw [IsScalarTower.algebraMap_apply R (integralClosure R Ω) (Localization.AtPrime Q),
    atPrimeMap_algebraMap]
  congr 1
  exact Subtype.ext (smul_algebraMap g r)

lemma atPrimeToField_atPrimeMap (g : G) (hg : g ∈ MulAction.stabilizer G Q)
    (x : Localization.AtPrime Q) :
    atPrimeToField Q (atPrimeMap Q g hg x) = g • atPrimeToField Q x := by
  have : (atPrimeToField Q).comp (atPrimeMap Q g hg) =
      (MulSemiringAction.toRingHom G Ω g).comp (atPrimeToField Q) := by
    refine IsLocalization.ringHom_ext Q.primeCompl (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, atPrimeMap_algebraMap, atPrimeToField_algebraMap,
      MulSemiringAction.toRingHom_apply, integralClosure.coe_smul]
  exact RingHom.congr_fun this x

lemma residue_atPrimeMap_of_mem_inertia {g : G} (hg : g ∈ Q.inertia G)
    (x : Localization.AtPrime Q) :
    IsLocalRing.residue _ (atPrimeMap Q g (Ideal.inertia_le_stabilizer Q hg) x) =
      IsLocalRing.residue _ x := by
  have : (IsLocalRing.residue _).comp (atPrimeMap Q g (Ideal.inertia_le_stabilizer Q hg)) =
      IsLocalRing.residue (Localization.AtPrime Q) := by
    refine IsLocalization.ringHom_ext Q.primeCompl (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply, atPrimeMap_algebraMap]
    rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q]
    exact hg b
  exact RingHom.congr_fun this x

end Action

section Galois

open scoped Pointwise

variable {K : Type*} [Field K] [Algebra R K] [Algebra K Ω] [IsScalarTower R K Ω] [IsGalois K Ω]
  [IsIntegrallyClosedIn R K] (P : Ideal R) [Q.IsMaximal] [Q.LiesOver P]

include P in
/-- Every automorphism of the residue field of `B_Q` fixing the image of `R` is induced by an
element of the decomposition group of `Q` in `Gal(Ω / K)`. -/
theorem exists_residueField_map_atPrimeMap_eq
    (φ : IsLocalRing.ResidueField (Localization.AtPrime Q) ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime Q))
    (hφ : ∀ r : R, φ (algebraMap R _ r) = algebraMap R _ r) :
    ∃ (σ : Gal(Ω/K)) (hσ : σ ∈ MulAction.stabilizer Gal(Ω/K) Q),
      ∀ x, IsLocalRing.ResidueField.map (atPrimeMap Q σ hσ) x = φ x := by
  let e : (integralClosure R Ω ⧸ Q) ≃+* IsLocalRing.ResidueField (Localization.AtPrime Q) :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal Q (Localization.AtPrime Q)).toRingEquiv
  have he (b : integralClosure R Ω) :
      e (Ideal.Quotient.mk Q b) = IsLocalRing.residue _ (algebraMap _ _ b) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk Q (Localization.AtPrime Q) b
  let ψ₀ : (integralClosure R Ω ⧸ Q) ≃+* (integralClosure R Ω ⧸ Q) := (e.trans φ).trans e.symm
  have hψ₀ (x : R ⧸ P) : ψ₀ (algebraMap (R ⧸ P) _ x) = algebraMap (R ⧸ P) _ x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : e (algebraMap (R ⧸ P) _ (Ideal.Quotient.mk P r)) =
        algebraMap R (IsLocalRing.ResidueField (Localization.AtPrime Q)) r := by
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver, he,
        ← IsScalarTower.algebraMap_apply R (integralClosure R Ω) (Localization.AtPrime Q),
        IsScalarTower.algebraMap_apply R (Localization.AtPrime Q)
          (IsLocalRing.ResidueField (Localization.AtPrime Q))]
      rfl
    change e.symm (φ (e _)) = _
    rw [h1, hφ, ← h1, RingEquiv.symm_apply_apply]
  let ψ : (integralClosure R Ω ⧸ Q) ≃ₐ[R ⧸ P] (integralClosure R Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv hψ₀
  obtain ⟨⟨σ, hσ⟩, hσψ⟩ := Ideal.Quotient.stabilizerHom_surjective_integralClosure (K := K) P Q ψ
  refine ⟨σ, hσ, fun x ↦ ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, e (Ideal.Quotient.mk Q b) = x := by
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨b, rfl⟩
  have h2 : Ideal.Quotient.mk Q (σ • b) = ψ (Ideal.Quotient.mk Q b) := by
    rw [← hσψ]
    rfl
  rw [he, IsLocalRing.ResidueField.map_residue, atPrimeMap_algebraMap, ← he, h2]
  exact e.apply_symm_apply _

end Galois

end Ideal

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite

/-!
# The Galois group of a Galois extension acting on an integral closure

Let `R` be a ring, `K` an `R`-algebra which is a field and `Ω / K` a Galois extension. The Galois
group `Gal(Ω / K)`, with its Krull topology, acts continuously on the integral closure `B` of `R`
in `Ω`, `B` being discrete (`Algebra.continuousSMul_integralClosure`). If `R` is integrally closed
in `K`, then `R` is the ring of invariants (`Algebra.isInvariant_integralClosure`), so the results
on profinite groups acting on rings apply: the decomposition group `D` of a prime `Q` of `B` over
`P` surjects onto the automorphism group of `(B ⧸ Q) / (R ⧸ P)` with kernel the inertia group, and
`D / I ≅ Aut((B ⧸ Q) / (R ⧸ P))` (`Ideal.Quotient.stabilizerQuotientInertiaEquivIntegralClosure`).
For a normal subextension `M / K`, an automorphism acting trivially modulo `Q` on `B ∩ M`
agrees on `M` with an element of the inertia group of `Q` (`Ideal.exists_mem_inertia_eqOn`).
-/

@[expose] public section

open scoped Pointwise

namespace Algebra

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- The fixed points of a subgroup `H` form a subalgebra over which the action of `H` is
invariant. -/
instance isInvariant_fixedPoints_subalgebra (H : Subgroup G) :
    IsInvariant (FixedPoints.subalgebra A B H) B H :=
  ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩

end Algebra

section Galois

variable (R K Ω : Type*) [CommRing R] [Field K] [Field Ω] [Algebra R K] [Algebra K Ω]
  [Algebra R Ω] [IsScalarTower R K Ω]

instance (priority := low) AlgEquiv.smulCommClass_of_isScalarTower :
    SMulCommClass Gal(Ω/K) R Ω where
  smul_comm σ r x := by
    rw [algebra_compatible_smul K r, algebra_compatible_smul K r]
    exact smul_comm σ (algebraMap R K r) x

namespace Algebra

/-- The Galois group of an algebraic extension `Ω / K`, with its Krull topology, acts
continuously on the integral closure of `R` in `Ω`, with the discrete topology. -/
theorem continuousSMul_integralClosure [Algebra.IsIntegral K Ω]
    [TopologicalSpace (integralClosure R Ω)] [DiscreteTopology (integralClosure R Ω)] :
    ContinuousSMul Gal(Ω/K) (integralClosure R Ω) := by
  refine ⟨continuous_prod_of_discrete_right.mpr fun b ↦ continuous_discrete_rng.mpr fun c ↦ ?_⟩
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨σ • (MulAction.stabilizer Gal(Ω/K) (b : Ω) : Set Gal(Ω/K)), ?_,
    (stabilizer_isOpen_of_isIntegral (b : Ω)).smul σ, ⟨1, one_mem _, mul_one σ⟩⟩
  rintro _ ⟨τ, hτ, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hσ ⊢
  rw [← hσ]
  apply Subtype.ext
  change (σ * τ) • (b : Ω) = σ • (b : Ω)
  rw [mul_smul, show τ • (b : Ω) = b from hτ]

/-- If `R` is integrally closed in `K` and `Ω / K` is Galois, then `R` is the ring of invariants
of `Gal(Ω / K)` acting on the integral closure of `R` in `Ω`. -/
theorem isInvariant_integralClosure [IsGalois K Ω] [IsIntegrallyClosedIn R K] :
    IsInvariant R (integralClosure R Ω) Gal(Ω/K) := by
  refine ⟨fun b hb ↦ ?_⟩
  have hfix : (b : Ω) ∈ IntermediateField.fixedField (⊥ : IntermediateField K Ω).fixingSubgroup :=
    fun σ ↦ congrArg Subtype.val (hb σ)
  rw [InfiniteGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hfix
  obtain ⟨k, hk⟩ := hfix
  have hint : IsIntegral R k := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R K Ω) (algebraMap K Ω).injective]
    have := b.2
    rw [mem_integralClosure_iff, ← hk] at this
    exact this
  obtain ⟨r, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  exact ⟨r, Subtype.ext (by simp [← hk, ← IsScalarTower.algebraMap_apply])⟩

end Algebra

namespace Ideal.Quotient

variable {R K Ω} [IsGalois K Ω] [IsIntegrallyClosedIn R K] (P : Ideal R)
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] [Q.LiesOver P]

/-- The decomposition group in `Gal(Ω / K)` of a prime `Q` of the integral closure of `R` in `Ω`
surjects onto the automorphism group of the residue extension. -/
theorem stabilizerHom_surjective_integralClosure :
    Function.Surjective (stabilizerHom Q P Gal(Ω/K)) := by
  let : TopologicalSpace (integralClosure R Ω) := ⊥
  have : DiscreteTopology (integralClosure R Ω) := ⟨rfl⟩
  have := Algebra.continuousSMul_integralClosure R K Ω
  have := Algebra.isInvariant_integralClosure R K Ω
  exact stabilizerHom_surjective_of_profinite P Q

/-- **Decomposition modulo inertia.** The decomposition group of `Q` modulo the inertia group is
the automorphism group of the residue extension `(B ⧸ Q) / (R ⧸ P)`. -/
noncomputable def stabilizerQuotientInertiaEquivIntegralClosure :
    MulAction.stabilizer Gal(Ω/K) Q ⧸ Q.inertia (MulAction.stabilizer Gal(Ω/K) Q) ≃*
      ((integralClosure R Ω ⧸ Q) ≃ₐ[R ⧸ P] (integralClosure R Ω ⧸ Q)) :=
  QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer Gal(Ω/K) Q))
    (stabilizerHom_surjective_integralClosure P Q) (ker_stabilizerHom Q P Gal(Ω/K)).symm

end Ideal.Quotient

namespace Ideal

variable {R K Ω} [IsGalois K Ω]

lemma mem_of_mem_fixingSubgroup_smul (M : IntermediateField K Ω) {x : Ω}
    (hx : ∀ σ ∈ M.fixingSubgroup, σ • x = x) : x ∈ M := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup M]
  exact fun σ ↦ hx σ σ.2

omit [IsGalois K Ω] in
lemma smul_mem_of_normal (M : IntermediateField K Ω) [Normal K M] (σ : Gal(Ω/K)) {x : Ω}
    (hx : x ∈ M) : σ x ∈ M := by
  have h1 := AlgEquiv.restrictNormal_commutes σ M ⟨x, hx⟩
  have h2 := (σ.restrictNormal M ⟨x, hx⟩).2
  change ((σ.restrictNormal M ⟨x, hx⟩ : M) : Ω) = σ x at h1
  rwa [h1] at h2

/-- **Lifting inertia to the separable closure.** Let `M / K` be a normal subextension of
`Ω / K` and `Q` a maximal ideal of the integral closure `B` of `R` in `Ω`. An automorphism `τ`
of `Ω / K` acting trivially modulo `Q` on `B ∩ M` agrees on `M` with an element of the inertia
group of `Q`. -/
theorem exists_mem_inertia_eqOn (M : IntermediateField K Ω) [Normal K M]
    (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] (τ : Gal(Ω/K))
    (hτ : ∀ b : integralClosure R Ω, (b : Ω) ∈ M → τ • b - b ∈ Q) :
    ∃ σ ∈ Q.inertia Gal(Ω/K), ∀ x ∈ M, σ x = τ x := by
  let B := integralClosure R Ω
  let N := M.fixingSubgroup
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have hcs := Algebra.continuousSMul_integralClosure R K Ω
  have : CompactSpace N :=
    isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed M).isCompact
  have : ContinuousSMul N B := ⟨(hcs.continuous_smul).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
  let A := FixedPoints.subalgebra R B N
  have : SMulCommClass N A B :=
    ⟨fun σ a b ↦ by
      change σ • ((a : B) * b) = (a : B) * (σ • b)
      rw [smul_mul', a.2 σ]⟩
  have hA (a : A) : ((a : B) : Ω) ∈ M :=
    mem_of_mem_fixingSubgroup_smul M fun σ hσ ↦ congrArg Subtype.val (a.2 ⟨σ, hσ⟩)
  have hNM (ρ : N) (x : Ω) (hx : x ∈ M) : (ρ : Gal(Ω/K)) x = x := ρ.2 ⟨x, hx⟩
  -- `τ Q` and `Q` lie over the same prime of `A = B ^ N`
  have hτQ : (τ • Q).under A = Q.under A := by
    ext a
    change (a : B) ∈ τ • Q ↔ (a : B) ∈ Q
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hmem : ((τ⁻¹ • (a : B) : B) : Ω) ∈ M := smul_mem_of_normal M τ⁻¹ (hA a)
    have h := hτ _ hmem
    rw [smul_inv_smul] at h
    constructor
    · intro ha
      have := Q.add_mem h ha
      simpa using this
    · intro ha
      have := Q.sub_mem ha h
      simpa using this
  have : (τ • Q).IsPrime := by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isPrime _ _
  obtain ⟨ρ, hρ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := N)
    (τ • Q) Q hτQ
  -- `σ₁ = ρ τ` stabilises `Q` and agrees with `τ` on `M`
  set σ₁ : Gal(Ω/K) := (ρ : Gal(Ω/K)) * τ
  have hσ₁ : σ₁ • Q = Q := by
    rw [mul_smul]
    exact hρ.symm
  have hσ₁M (x : Ω) (hx : x ∈ M) : σ₁ x = τ x := by
    change (ρ : Gal(Ω/K)) (τ x) = τ x
    exact hNM ρ _ (smul_mem_of_normal M τ hx)
  -- `σ₁` acts on `B ⧸ Q` linearly over `A ⧸ (Q ∩ A)`
  let g : MulAction.stabilizer Gal(Ω/K) Q := ⟨σ₁, hσ₁⟩
  let f₀ := Ideal.Quotient.stabilizerHom Q (Q.under R) Gal(Ω/K) g
  let f : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) :=
    { f₀.toRingEquiv with
      commutes' := by
        intro x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        change f₀ (Ideal.Quotient.mk Q (a : B)) = Ideal.Quotient.mk Q (a : B)
        rw [Ideal.Quotient.stabilizerHom_apply, Ideal.Quotient.eq]
        change σ₁ • (a : B) - (a : B) ∈ Q
        have h1 : σ₁ • (a : B) = τ • (a : B) := Subtype.ext (hσ₁M _ (hA a))
        rw [h1]
        exact hτ _ (hA a) }
  obtain ⟨ρ', hρ'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := N)
    (Q.under A) Q f
  refine ⟨(ρ'.1 : Gal(Ω/K))⁻¹ * σ₁, ?_, fun x hx ↦ ?_⟩
  · intro b
    have hb := congrArg (fun e ↦ e (Ideal.Quotient.mk Q b)) hρ'
    simp only [Ideal.Quotient.stabilizerHom_apply] at hb
    change Ideal.Quotient.mk Q (ρ'.1 • b) = Ideal.Quotient.mk Q (σ₁ • b) at hb
    rw [Ideal.Quotient.eq] at hb
    have hρ'Q : (ρ'.1 : Gal(Ω/K))⁻¹ • Q = Q := by
      rw [inv_smul_eq_iff]
      exact (ρ'.2).symm
    have := Q.smul_mem_pointwise_smul ((ρ'.1 : Gal(Ω/K))⁻¹) _ (Q.neg_mem_iff.2 hb)
    rw [hρ'Q] at this
    have e : ((ρ'.1 : Gal(Ω/K))⁻¹ • (ρ'.1 • b) : B) = b := inv_smul_smul (ρ'.1 : Gal(Ω/K)) b
    have key : ((ρ'.1 : Gal(Ω/K))⁻¹ * σ₁) • b - b =
        (ρ'.1 : Gal(Ω/K))⁻¹ • -(ρ'.1 • b - σ₁ • b) := by
      rw [smul_neg, smul_sub, e, mul_smul, neg_sub]
    change ((ρ'.1 : Gal(Ω/K))⁻¹ * σ₁) • b - b ∈ Q
    rw [key]
    exact this
  · change ((ρ'.1 : Gal(Ω/K))⁻¹ : Gal(Ω/K)) (σ₁ x) = τ x
    rw [hσ₁M x hx]
    have := hNM ρ'.1⁻¹ (τ x) (smul_mem_of_normal M τ hx)
    exact this

end Ideal

end Galois

section ResidueField

variable {R K Ω : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [Algebra.IsAlgebraic K Ω]

omit [IsDomain R] [IsFractionRing R K] [Algebra.IsAlgebraic K Ω] in
/-- The integral closure of `R` in `Ω` is integrally closed in `Ω`. -/
instance integralClosure.isIntegrallyClosedIn_self :
    IsIntegrallyClosedIn (integralClosure R Ω) Ω :=
  ⟨Subtype.val_injective, fun {x} ↦ ⟨fun hx ↦ ⟨⟨x, isIntegral_trans (R := R) _ hx⟩, rfl⟩,
    by rintro ⟨y, rfl⟩; exact isIntegral_algebraMap⟩⟩

variable (K) in
include K in
/-- The integral closure of `R` in an algebraic extension `Ω` of its fraction field has fraction
field `Ω`. -/
lemma integralClosure.isFractionRing_of_isAlgebraic :
    IsFractionRing (integralClosure R Ω) Ω := by
  have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic (S := K) (nonZeroDivisors R)
  have : Algebra.IsAlgebraic R Ω := Algebra.IsAlgebraic.trans R K Ω
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  exact integralClosure.isFractionRing_of_algebraic fun x hx ↦
    hinj (hx.trans (map_zero _).symm)

variable (K) in
include K in
/-- The residue fields at maximal ideals of the integral closure of `R` in a separably closed
algebraic extension of its fraction field are separably closed. -/
lemma Ideal.isSepClosed_quotient_integralClosure [IsSepClosed Ω] (Q : Ideal (integralClosure R Ω))
    [Q.IsMaximal] :
    letI := Ideal.Quotient.field Q
    IsSepClosed (integralClosure R Ω ⧸ Q) := by
  let := Ideal.Quotient.field Q
  have := integralClosure.isFractionRing_of_isAlgebraic (R := R) K (Ω := Ω)
  have : IsIntegrallyClosed (integralClosure R Ω) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).2 inferInstance
  have : IsIntegrallyClosed (Localization.AtPrime Q) :=
    isIntegrallyClosed_of_isLocalization _ Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : IsSepClosed (FractionRing (integralClosure R Ω)) :=
    IsSepClosed.of_ringEquiv (FractionRing.algEquiv (integralClosure R Ω) Ω).symm.toRingEquiv
  have := IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing
    (A := Localization.AtPrime Q) (FractionRing (integralClosure R Ω))
  have : IsSepClosed Q.ResidueField := this
  exact IsSepClosed.of_ringEquiv (RingEquiv.ofBijective _
    (Ideal.bijective_algebraMap_quotient_residueField Q)).symm

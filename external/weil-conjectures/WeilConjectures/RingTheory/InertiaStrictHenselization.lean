/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import WeilConjectures.RingTheory.StrictlyHenselianInvariants
public import WeilConjectures.RingTheory.StrictlyHenselianNormal

/-!
# The inertia invariants of `B_Q`

Let `R` be a domain, `Ω` a separably closed field algebraic over `R`, `B` the integral closure of
`R` in `Ω` and `Q` a prime of `B`. The localization `B_Q` is strictly henselian
(`Ideal.isStrictlyHenselianLocalRing_atPrime`), and the inertia group `I_Q` of `Q` in a group `G`
acting on `Ω` acts on `B_Q` (`Ideal.inertiaAtPrimeAction`) trivially on the residue field. Hence
the ring of invariants `B_Q^{I_Q}` is strictly henselian
(`Ideal.isStrictlyHenselianLocalRing_fixedPoints_atPrime`): for `R` the ring of an affine chart
of a curve at a boundary point `z`, `Ω` a separable closure of the function field and
`G = Gal(Ω / K)`, it is the strict henselization at `z` of blueprint
`lemma-boundary-stalk--1`.

For `Ω / K` Galois and `R` with fraction field `K`, the inertia group is closed in the Krull
topology (`Ideal.isClosed_inertia_integralClosure`), so it is the Galois group of `Ω` over its
fixed field (`Ideal.fixingSubgroup_fixedField_inertia`): the invariants of the generic stalk
under `Gal(Ω / Ω^{I_Q})` are the inertia invariants.
-/

@[expose] public section

open IsLocalRing
open scoped Pointwise

namespace Ideal

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
  (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]

section Action

variable (G : Type*) [Group G] [MulSemiringAction G Ω] [SMulCommClass G R Ω]

lemma atPrimeMap_one (x : Localization.AtPrime Q) :
    atPrimeMap Q (1 : G) (MulAction.stabilizer G Q).one_mem x = x := by
  have : atPrimeMap Q (1 : G) (MulAction.stabilizer G Q).one_mem = RingHom.id _ :=
    IsLocalization.ringHom_ext Q.primeCompl (RingHom.ext fun b ↦ by
      simp only [RingHom.comp_apply, atPrimeMap_algebraMap, one_smul, RingHom.id_apply])
  exact RingHom.congr_fun this x

variable {G} in
lemma atPrimeMap_mul {g h : G} (hg : g ∈ MulAction.stabilizer G Q)
    (hh : h ∈ MulAction.stabilizer G Q) (x : Localization.AtPrime Q) :
    atPrimeMap Q (g * h) (mul_mem hg hh) x = atPrimeMap Q g hg (atPrimeMap Q h hh x) := by
  have : atPrimeMap Q (g * h) (mul_mem hg hh) = (atPrimeMap Q g hg).comp (atPrimeMap Q h hh) :=
    IsLocalization.ringHom_ext Q.primeCompl (RingHom.ext fun b ↦ by
      simp only [RingHom.comp_apply, atPrimeMap_algebraMap, mul_smul])
  exact RingHom.congr_fun this x

/-- The action of the inertia group of `Q` on `B_Q`. It is not an instance, to keep instance
search on `B_Q` fast. -/
@[instance_reducible]
noncomputable def inertiaAtPrimeAction :
    MulSemiringAction (Q.inertia G) (Localization.AtPrime Q) where
  smul g x := atPrimeMap Q g (Ideal.inertia_le_stabilizer Q g.2) x
  one_smul := atPrimeMap_one Q G
  mul_smul _ _ := atPrimeMap_mul Q _ _
  smul_zero _ := map_zero _
  smul_add _ := map_add _
  smul_one _ := map_one _
  smul_mul _ := map_mul _

/-- The inertia group acts trivially on the residue field of `B_Q`. -/
lemma atPrimeMap_sub_mem_maximalIdeal (g : Q.inertia G) (x : Localization.AtPrime Q) :
    atPrimeMap Q g (Ideal.inertia_le_stabilizer Q g.2) x - x ∈
      maximalIdeal (Localization.AtPrime Q) := by
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact residue_atPrimeMap_of_mem_inertia Q g.2 x

variable [IsSepClosed Ω] [Algebra.IsAlgebraic R Ω]

/-- **The inertia invariants of `B_Q` are strictly henselian**: `B_Q` is strictly henselian and
the inertia group acts trivially on its residue field. -/
theorem isStrictlyHenselianLocalRing_fixedPoints_atPrime
    (hR : Function.Injective (algebraMap R Ω)) :
    letI := inertiaAtPrimeAction Q G
    IsStrictlyHenselianLocalRing
      (FixedPoints.subring (Localization.AtPrime Q) (Q.inertia G)) :=
  letI := inertiaAtPrimeAction Q G
  have := isStrictlyHenselianLocalRing_atPrime Q hR
  FixedPoints.isStrictlyHenselianLocalRing_subring (atPrimeMap_sub_mem_maximalIdeal Q G)

end Action

section Galois

variable {K : Type*} [Field K] [Algebra R K] [Algebra K Ω] [IsScalarTower R K Ω]
  [Algebra.IsAlgebraic K Ω]

omit [Q.IsPrime] in
/-- **The inertia group is closed** in the Krull topology: an automorphism moving some `x` modulo
`Q` moves it modulo `Q` on a whole coset of the open subgroup fixing `K(x)`. -/
theorem isClosed_inertia_integralClosure :
    IsClosed (Q.inertia Gal(Ω/K) : Set Gal(Ω/K)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  obtain ⟨x, hx⟩ : ∃ x, σ • x - x ∉ Q := by
    by_contra! h
    exact hσ h
  let E : IntermediateField K Ω := IntermediateField.adjoin K {(x : Ω)}
  have : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (x : Ω))
  refine ⟨(σ * ·) '' (E.fixingSubgroup : Set Gal(Ω/K)), ?_, ?_, ⟨1, one_mem _, mul_one σ⟩⟩
  · rintro _ ⟨τ, hτ, rfl⟩ hστ
    have hτx : τ (x : Ω) = x :=
      (IntermediateField.mem_fixingSubgroup_iff E τ).1 hτ _
        (IntermediateField.subset_adjoin K _ rfl)
    apply hx
    have h := hστ x
    have hsx : (σ * τ) • x = σ • x := Subtype.ext (by
      change (σ * τ) (x : Ω) = σ (x : Ω)
      rw [AlgEquiv.mul_apply, hτx])
    rwa [hsx] at h
  · exact (Homeomorph.mulLeft σ).isOpenMap _ (IntermediateField.fixingSubgroup_isOpen E)

omit [Q.IsPrime] in
/-- The inertia group is the Galois group of `Ω` over its fixed field. -/
theorem fixingSubgroup_fixedField_inertia [IsGalois K Ω] :
    (IntermediateField.fixedField (Q.inertia Gal(Ω/K))).fixingSubgroup = Q.inertia Gal(Ω/K) :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨Q.inertia Gal(Ω/K), isClosed_inertia_integralClosure Q⟩

end Galois

end Ideal

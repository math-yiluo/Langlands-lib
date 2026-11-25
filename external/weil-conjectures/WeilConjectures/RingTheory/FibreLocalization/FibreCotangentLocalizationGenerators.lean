/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Module.TransferInstance

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Fibre cotangent comparison after localization with generator bound

Source: Stacks Project, Algebra, Tag 00RV (lemma-differentials-base-change),
followed by localization and tensor comparison in Morphisms, Tag 01V9(4)
(blueprint: lem-trf-fibre-cotangent-localization-generators).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open scoped TensorProduct

namespace KaehlerDifferential.FibreLocalization

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The contracted base prime. Source: Stacks 01V9(4)
(blueprint: lem-trf-fibre-cotangent-localization-generators). -/
abbrev basePrime (q : Ideal A) : Ideal R := q.comap (algebraMap R A)

/-- The fibre ring, using the existing Mathlib construction. Source: Stacks 01V9(4)
(blueprint: lem-trf-fibre-cotangent-localization-generators). -/
abbrev fibre (q : Ideal A) [q.IsPrime] := (basePrime (R := R) q).Fiber A

/-- The canonical fibre map to the residue field at the original prime.
Source: Stacks 00RV and residue field functoriality, Section 07BH
(blueprint: lem-trf-fibre-cotangent-localization-generators). -/
noncomputable def residueMap (q : Ideal A) [q.IsPrime] :
    fibre (R := R) q →ₐ[R] q.ResidueField :=
  Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ (basePrime (R := R) q) q (Algebra.ofId R A) rfl)
    (IsScalarTower.toAlgHom R A q.ResidueField) (fun _ _ ↦ Commute.all _ _)

/-- The canonical prime in the fibre is the kernel of its residue map.
Source: Stacks 01V9(4), with Section 07BH
(blueprint: lem-trf-fibre-cotangent-localization-generators). -/
noncomputable def fibrePoint (q : Ideal A) [q.IsPrime] :
    PrimeSpectrum (fibre (R := R) q) :=
  ⟨RingHom.ker (residueMap (R := R) q).toRingHom,
    RingHom.ker_isPrime (residueMap (R := R) q).toRingHom⟩

/-- The residue field of the canonical fibre prime. Source: Stacks 01V9(4)
(blueprint: lem-trf-fibre-cotangent-localization-generators). -/
noncomputable abbrev fibreField (q : Ideal A) [q.IsPrime] :=
  (fibrePoint (R := R) q).asIdeal.ResidueField

/-- The standard right-factor algebra structure on the fibre.
Source: Stacks 00CX, 00RV (blueprint: lem-trf-fibre-cotangent-localization-generators). -/
noncomputable abbrev fibreAlgebra (q : Ideal A) [q.IsPrime] : Algebra A (fibre (R := R) q) :=
  Algebra.TensorProduct.rightAlgebra

/-- The inverse of the canonical differential base-change isomorphism is beta.
Source: Stacks 00RV (lemma-differentials-base-change)
(blueprint: lem-trf-fibre-cotangent-localization-generators). -/
noncomputable def beta (q : Ideal A) [q.IsPrime] :
    letI := fibreAlgebra (R := R) q
    KaehlerDifferential (basePrime (R := R) q).ResidueField (fibre (R := R) q) ≃ₗ[
      fibre (R := R) q] (fibre (R := R) q) ⊗[A] KaehlerDifferential R A :=
  letI := fibreAlgebra (R := R) q
  (KaehlerDifferential.tensorKaehlerEquiv R (basePrime (R := R) q).ResidueField
    A (fibre (R := R) q)).symm

/-- Exact pure-tensor and generator specification for the canonical comparison,
using right-factor scalar actions transported through tensor commutativity.
Source: Stacks 00RV followed by the comparison in 01V9(4)
(blueprint: lem-trf-fibre-cotangent-localization-generators). -/
def ComparisonAlong (q : Ideal A) [q.IsPrime]
    (ρ : Localization.AtPrime q →+* fibreField (R := R) q) : Prop :=
  letI := fibreAlgebra (R := R) q
  letI := ρ.toAlgebra
  let M := KaehlerDifferential R A
  let Mq := LocalizedModule q.primeCompl M
  let F := fibre (R := R) q
  let L := fibreField (R := R) q
  let N := KaehlerDifferential (basePrime (R := R) q).ResidueField F
  let Aq := Localization.AtPrime q
  letI : Module L (Mq ⊗[Aq] L) :=
    (TensorProduct.comm Aq Mq L).toAddEquiv.module L
  letI : Module L (N ⊗[F] L) := (TensorProduct.comm F N L).toAddEquiv.module L
  ∃ θ : Mq ⊗[Aq] L ≃ₗ[L] N ⊗[F] L,
    (∀ (ω : M) (a : A) (ha : a ∉ q) (z : L),
      θ (LocalizedModule.mk ω ⟨a, ha⟩ ⊗ₜ[Aq] z) =
        (beta (R := R) q).symm (1 ⊗ₜ[A] ω) ⊗ₜ[F]
          (z / ((algebraMap F L).comp (algebraMap A F) a))) ∧
    (∀ (b : F) (ω : M) (z : L),
      θ.symm ((beta (R := R) q).symm (b ⊗ₜ[A] ω) ⊗ₜ[F] z) =
        LocalizedModule.mk ω ⟨1, q.primeCompl.one_mem⟩ ⊗ₜ[Aq] (algebraMap F L b * z)) ∧
    ∀ (r : ℕ) (m : Fin r → Mq), Submodule.span Aq (Set.range m) = ⊤ →
      Submodule.span L (Set.range (fun i : Fin r ↦ θ (m i ⊗ₜ[Aq] (1 : L)))) = ⊤ ∧
        FiniteDimensional L (N ⊗[F] L) ∧ Module.finrank L (N ⊗[F] L) ≤ r

private noncomputable def scalarCancel
    {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] [Algebra B D] [Algebra C D]
    (P : Type*) [AddCommGroup P] [Module B P] (h : IsScalarTower B C D) :
    D ⊗[C] (C ⊗[B] P) ≃ₗ[D] D ⊗[B] P := by
  let : IsScalarTower B C D := h
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange B C D D P

private theorem scalarCancel_tmul
    {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] [Algebra B D] [Algebra C D]
    (P : Type*) [AddCommGroup P] [Module B P] (h : IsScalarTower B C D)
    (z : D) (b : C) (p : P) :
    scalarCancel P h (z ⊗ₜ[C] (b ⊗ₜ[B] p)) = (algebraMap C D b * z) ⊗ₜ[B] p := by
  rw [← Algebra.smul_def]
  rfl

private theorem scalarCancel_symm_tmul
    {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] [Algebra B D] [Algebra C D]
    (P : Type*) [AddCommGroup P] [Module B P] (h : IsScalarTower B C D)
    (z : D) (p : P) :
    (scalarCancel P h).symm (z ⊗ₜ[B] p) = z ⊗ₜ[C] ((1 : C) ⊗ₜ[B] p) := rfl

/-- Localizing the relative differentials and then taking the fibre gives the
canonical comparison with the differentials of the fibre ring; finite generators
span the target and bound its dimension.

Source: Stacks Project, Algebra, Tag 00RV and Morphisms, Tag 01V9(4)
(blueprint: lem-trf-fibre-cotangent-localization-generators).

Proof:
1. The residue map at q has kernel q. The canonical fibre residue map has prime
   kernel Q with contraction q, so every a outside q has nonzero image in L.
   The localization universal property supplies rho extending A to L.
2. Differential base change (00RV) gives beta, whose inverse is F-linear.
3. The map (omega/a) tensor z to omega tensor (z/a) is well-defined by the
   fraction relation: multiplying a relation by an invertible denominator in L
   gives equality. It is Aq-balanced; its inverse sends omega tensor z to
   (omega/1) tensor z. Both composites are identities on pure tensors.
4. Reassociate (F tensor_A M) tensor_F L with M tensor_A L using the map
   (b tensor omega) tensor z to omega tensor (b*z), with inverse
   omega tensor z to (1 tensor omega) tensor z. Compose with beta inverse
   tensored with L and the localization comparison. These maps give theta and
   both displayed formulas; pure tensors generate, so the formulas determine it.
5. Expressing m as a linear combination of the m_i and balancing tensors shows
   that the m_i tensor 1 span the source; theta transports the spanning family.
6. Extract an independent subfamily of the r spanning vectors. Its span is the
   whole target and its dimension is its cardinality, at most r. For r=0 this
   says the target is zero, finite-dimensional of dimension zero. -/
theorem comparison {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime] :
    ∃ ρ : Localization.AtPrime q →+* fibreField (R := R) q,
      (∀ a : A, ρ (algebraMap A (Localization.AtPrime q) a) =
        algebraMap (fibre (R := R) q) (fibreField (R := R) q)
          (Algebra.TensorProduct.includeRight a)) ∧ ComparisonAlong (R := R) q ρ := by
  classical
  let := fibreAlgebra (R := R) q
  let F := fibre (R := R) q
  let L := fibreField (R := R) q
  let Aq := Localization.AtPrime q
  let M := KaehlerDifferential R A
  let Mq := LocalizedModule q.primeCompl M
  let N := KaehlerDifferential (basePrime (R := R) q).ResidueField F
  let g : A →+* L := (algebraMap F L).comp (algebraMap A F)
  have hg (a : q.primeCompl) : IsUnit (g a) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hmem : algebraMap A F (a : A) ∈ (fibrePoint (R := R) q).asIdeal :=
      Ideal.algebraMap_residueField_eq_zero.mp h
    change residueMap (R := R) q (1 ⊗ₜ[R] (a : A)) = 0 at hmem
    have hz : algebraMap A q.ResidueField (a : A) = 0 := by
      simpa only [residueMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
        IsScalarTower.toAlgHom_apply] using hmem
    exact a.property (Ideal.algebraMap_residueField_eq_zero.mp hz)
  let ρ : Aq →+* L := IsLocalization.lift (S := Aq) hg
  have hρ (a : A) : ρ (algebraMap A Aq a) = g a := IsLocalization.lift_eq hg a
  refine ⟨ρ, hρ, ?_⟩
  let : Algebra Aq L := ρ.toAlgebra
  let : Algebra A L := g.toAlgebra
  have hAq : IsScalarTower A Aq L :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (hρ a).symm)
  have hF : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : Module L (Mq ⊗[Aq] L) :=
    (TensorProduct.comm Aq Mq L).toAddEquiv.module L
  let : Module L (N ⊗[F] L) := (TensorProduct.comm F N L).toAddEquiv.module L
  let c₁ : Mq ⊗[Aq] L ≃ₗ[L] L ⊗[Aq] Mq :=
    (TensorProduct.comm Aq Mq L).toAddEquiv.linearEquiv L
  let c₂ : N ⊗[F] L ≃ₗ[L] L ⊗[F] N :=
    (TensorProduct.comm F N L).toAddEquiv.linearEquiv L
  let e₁ := LinearEquiv.baseChange Aq L _ _
    (LocalizedModule.equivTensorProduct q.primeCompl M)
  let e₂ := scalarCancel M hAq
  let e₃ := scalarCancel M hF
  let e₄ := LinearEquiv.baseChange F L _ _ (beta (R := R) q).symm
  let θ := c₁ ≪≫ₗ e₁ ≪≫ₗ e₂ ≪≫ₗ e₃.symm ≪≫ₗ e₄ ≪≫ₗ c₂.symm
  change ∃ θ : Mq ⊗[Aq] L ≃ₗ[L] N ⊗[F] L, _
  refine ⟨θ, ?_, ?_, ?_⟩
  · change ∀ (ω : M) (a : A) (ha : a ∈ q.primeCompl) (z : L), _
    intro ω a ha z
    have hfrac : algebraMap Aq L (Localization.mk 1 ⟨a, ha⟩) = (g a)⁻¹ := by
      change IsLocalization.lift hg (Localization.mk 1 ⟨a, ha⟩) = (g a)⁻¹
      rw [Localization.mk_eq_mk'_apply]
      apply (IsLocalization.lift_mk'_spec hg 1 ((g a)⁻¹) ⟨a, ha⟩).2
      rw [map_one]
      exact (mul_inv_cancel₀ (hg ⟨a, ha⟩).ne_zero).symm
    apply c₂.injective
    change c₂ (c₂.symm (e₄ (e₃.symm
      (e₂ (e₁ (z ⊗ₜ[Aq] LocalizedModule.mk ω ⟨a, ha⟩)))))) =
        (z / g a) ⊗ₜ[F] (beta (R := R) q).symm (1 ⊗ₜ[A] ω)
    rw [c₂.apply_symm_apply]
    have he₁ : e₁ (z ⊗ₜ[Aq] LocalizedModule.mk ω ⟨a, ha⟩) =
        z ⊗ₜ[Aq] (Localization.mk 1 ⟨a, ha⟩ ⊗ₜ[A] ω) :=
      congrArg (fun t : Aq ⊗[A] M ↦ z ⊗ₜ[Aq] t)
        (LocalizedModule.equivTensorProduct_apply_mk q.primeCompl ω ⟨a, ha⟩)
    rw [he₁, scalarCancel_tmul M hAq, scalarCancel_symm_tmul M hF]
    change ((algebraMap Aq L (Localization.mk 1 ⟨a, ha⟩)) * z) ⊗ₜ[F]
      (beta (R := R) q).symm (1 ⊗ₜ[A] ω) = _
    apply congrArg (fun c : L ↦ c ⊗ₜ[F] (beta (R := R) q).symm (1 ⊗ₜ[A] ω))
    rw [hfrac, div_eq_mul_inv]
    exact mul_comm _ _
  · intro b ω z
    apply c₁.injective
    dsimp only [θ, LinearEquiv.symm_trans_apply]
    rw [c₁.apply_symm_apply]
    change e₁.symm (e₂.symm (e₃ (e₄.symm
      ((z : L) ⊗ₜ[F] (beta (R := R) q).symm (b ⊗ₜ[A] ω))))) =
        (algebraMap F L b * z) ⊗ₜ[Aq] LocalizedModule.mk ω 1
    have hβ : e₄.symm (z ⊗ₜ[F] (beta (R := R) q).symm (b ⊗ₜ[A] ω)) =
        z ⊗ₜ[F] (b ⊗ₜ[A] ω) :=
      congrArg (fun t : F ⊗[A] M ↦ z ⊗ₜ[F] t)
        ((beta (R := R) q).apply_symm_apply (b ⊗ₜ[A] ω))
    rw [hβ, scalarCancel_tmul M hF, scalarCancel_symm_tmul M hAq]
    exact congrArg (fun t : Mq ↦ (algebraMap F L b * z) ⊗ₜ[Aq] t)
      (LocalizedModule.equivTensorProduct_symm_apply_tmul_one q.primeCompl ω)
  · intro r m hm
    have hs : Submodule.span L (Set.range (fun i : Fin r ↦ (1 : L) ⊗ₜ[Aq] m i)) = ⊤ := by
      change Submodule.span L (Set.range (TensorProduct.mk Aq L Mq 1 ∘ m)) = ⊤
      rw [Set.range_comp, ← Submodule.baseChange_span, hm, Submodule.baseChange_top]
    let e := c₁.symm ≪≫ₗ θ
    have ht : Submodule.span L
        (Set.range (fun i : Fin r ↦ θ (m i ⊗ₜ[Aq] (1 : L)))) = ⊤ := by
      have h := congrArg (fun p : Submodule L (L ⊗[Aq] Mq) ↦ p.map e.toLinearMap) hs
      simpa [Submodule.map_span, ← Set.range_comp, Function.comp_def, e, c₁] using h
    refine ⟨ht, ?_, ?_⟩
    · apply Module.Finite.of_fg_top
      rw [← ht]
      exact Submodule.fg_span (Set.finite_range _)
    · simpa using finrank_le_of_span_eq_top ht

end KaehlerDifferential.FibreLocalization

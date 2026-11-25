/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Finite
public import WeilConjectures.RingTheory.DiscreteValuationRing.FiniteKummerLevel

/-!
# `𝒪_E / ϖ^n` is free over `ℤ/ℓ^N`

Let `R` be a discrete valuation ring which is a finite `ℤ_ℓ`-algebra (for instance the valuation
ring `𝒪_E` of a finite extension `E` of `ℚ_ℓ`), with uniformizer `ϖ` and ramification index `e`,
`ℓ = (unit) · ϖ^e`, and let `n = e N`. Then `A = R / ϖ^n` is a free `ℤ/ℓ^N`-module of rank
`[R : ℤ_ℓ] = e f`, `f` being the residue degree `[R/ϖ : 𝔽_ℓ]`
(`IsDiscreteValuationRing.free_quotient_span_pow`): `A ≅ (ℤ/ℓ^N)^{ef}`. This is the freeness
clause of blueprint `lem-pur-finite-kummer-level`.

Indeed `R` is a free `ℤ_ℓ`-module of finite rank (finitely generated and torsion free over a
principal ideal domain), `A = R / ℓ^N R ≅ ℤ/ℓ^N ⊗_{ℤ_ℓ} R` is free of the same rank over `ℤ/ℓ^N`,
and counting elements, `ℓ^{N · rank} = #A = #(R/ϖ)^{eN} = ℓ^{f e N}`.
-/

@[expose] public section

open TensorProduct

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  (hϖ : Irreducible ϖ) {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {e : ℕ} (he : 0 < e)
  (hℓe : Associated (ℓ : R) (ϖ ^ e)) [Algebra ℤ_[ℓ] R] (N : ℕ)

omit [IsDiscreteValuationRing R] hℓ [Algebra ℤ_[ℓ] R] in
include hϖ hℓe in
/-- `ℓ` is nonzero in `R`. -/
lemma natCast_ne_zero_of_associated : (ℓ : R) ≠ 0 := by
  obtain ⟨v, hv⟩ := hℓe
  intro h
  rw [h, zero_mul] at hv
  exact pow_ne_zero e hϖ.ne_zero hv.symm

omit [IsDiscreteValuationRing R] in
include hϖ hℓe in
/-- `R` is a torsion free `ℤ_ℓ`-module: a nonzero `a ∈ ℤ_ℓ` is a unit times a power of `ℓ`, and
`ℓ` is nonzero in the domain `R`. -/
lemma injective_algebraMap_padicInt : Function.Injective (algebraMap ℤ_[ℓ] R) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  by_contra ha0
  obtain ⟨u, k, rfl⟩ : ∃ (u : ℤ_[ℓ]ˣ) (k : ℕ), u * (ℓ : ℤ_[ℓ]) ^ k = a := by
    exact ⟨PadicInt.unitCoeff ha0, a.valuation, (PadicInt.unitCoeff_spec ha0).symm⟩
  rw [map_mul, map_pow, map_natCast] at ha
  exact pow_ne_zero k (natCast_ne_zero_of_associated hϖ hℓe)
    ((u.isUnit.map (algebraMap ℤ_[ℓ] R)).mul_right_eq_zero.1 ha)

/-- `ℤ/ℓ^N` as a `ℤ_ℓ`-algebra, through `PadicInt.toZModPow`. -/
noncomputable local instance algebraPadicIntZModPow : Algebra ℤ_[ℓ] (ZMod (ℓ ^ N)) :=
  (PadicInt.toZModPow N).toAlgebra

/-- `ℤ/ℓ^N ≅ ℤ_ℓ / ℓ^N` as `ℤ_ℓ`-modules. -/
noncomputable def zmodPowLinearEquiv :
    (ℤ_[ℓ] ⧸ Ideal.span {(ℓ : ℤ_[ℓ]) ^ N}) ≃ₗ[ℤ_[ℓ]] ZMod (ℓ ^ N) :=
  ((Ideal.quotientEquivAlgOfEq ℤ_[ℓ] (PadicInt.ker_toZModPow N).symm).toLinearEquiv ≪≫ₗ
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId ℤ_[ℓ] (ZMod (ℓ ^ N)))
      (ZMod.ringHom_surjective _)).toLinearEquiv)

include hℓe in
omit [IsDiscreteValuationRing R] in
/-- `ℓ^N R`, as a `ℤ_ℓ`-submodule, is `ϖ^{eN} R`. -/
lemma span_smul_top_eq_restrictScalars :
    Ideal.span {(ℓ : ℤ_[ℓ]) ^ N} • (⊤ : Submodule ℤ_[ℓ] R) =
      (Ideal.span {ϖ ^ (e * N)}).restrictScalars ℤ_[ℓ] := by
  rw [Submodule.ideal_span_singleton_smul, span_pow_mul_eq_span_natCast_pow hℓe]
  ext x
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]⟩

include hℓe in
omit [IsDiscreteValuationRing R] in
/-- `R / ϖ^{eN} ≅ ℤ/ℓ^N ⊗_{ℤ_ℓ} R` as `ℤ_ℓ`-modules. -/
noncomputable def quotientLinearEquivTensor :
    (R ⧸ Ideal.span {ϖ ^ (e * N)}) ≃ₗ[ℤ_[ℓ]] ZMod (ℓ ^ N) ⊗[ℤ_[ℓ]] R :=
  (Submodule.Quotient.restrictScalarsEquiv ℤ_[ℓ] (Ideal.span {ϖ ^ (e * N)})).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (span_smul_top_eq_restrictScalars hℓe N).symm ≪≫ₗ
    (quotTensorEquivQuotSMul R (Ideal.span {(ℓ : ℤ_[ℓ]) ^ N})).symm ≪≫ₗ
    TensorProduct.congr (zmodPowLinearEquiv N) (LinearEquiv.refl _ _)

variable [Module.Finite ℤ_[ℓ] R]

omit [Algebra ℤ_[ℓ] R] [Module.Finite ℤ_[ℓ] R] in
include hϖ he hℓe in
/-- The residue field `R/ϖ` has characteristic `ℓ`. -/
lemma charP_quotient_span : CharP (R ⧸ Ideal.span {ϖ}) ℓ := by
  have : (Ideal.span {ϖ}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have : Nontrivial (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.nontrivial_iff.2 this.ne_top
  refine (CharP.charP_iff_prime_eq_zero hℓ.out).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  obtain ⟨v, hv⟩ := hℓe
  have h : ϖ ∣ (ℓ : R) * v := hv ▸ dvd_pow_self ϖ he.ne'
  exact Units.dvd_mul_right.1 h

include hϖ he hℓe in
/-- Blueprint `lem-pur-finite-kummer-level`: Finite Kummer level of the Tate twist

The freeness clause: let `R` (for instance `𝒪_E`) be a discrete valuation ring which is a finite
`ℤ_ℓ`-algebra, with uniformizer `ϖ` and ramification index `e ≥ 1` (`ℓ = (unit) · ϖ^e`), and let
`n = e N` with `N ≥ 1`. Then `A = R / ϖ^n` is a free module of finite rank over `ℤ/ℓ^N` (with
the module structure of a ring of characteristic `ℓ^N`,
`IsDiscreteValuationRing.charP_quotient_span_pow`), of rank `e f`, where `f = [R/ϖ : 𝔽_ℓ]` is
the residue degree: `A ≅ (ℤ/ℓ^N)^{ef}`. Its rank is also the rank `[R : ℤ_ℓ]` of `R` over
`ℤ_ℓ`. -/
theorem free_quotient_span_pow (hN : 0 < N) :
    haveI := charP_quotient_span_pow hϖ hℓ.out he hℓe N
    letI := ZMod.algebra (R ⧸ Ideal.span {ϖ ^ (e * N)}) (ℓ ^ N)
    haveI := charP_quotient_span hϖ he hℓe
    letI := ZMod.algebra (R ⧸ Ideal.span {ϖ}) ℓ
    Module.Free (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)}) ∧
      Module.finrank (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)}) =
        Module.finrank ℤ_[ℓ] R ∧
      Module.finrank (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)}) =
        e * Module.finrank (ZMod ℓ) (R ⧸ Ideal.span {ϖ}) := by
  have := charP_quotient_span_pow hϖ hℓ.out he hℓe N
  let := ZMod.algebra (R ⧸ Ideal.span {ϖ ^ (e * N)}) (ℓ ^ N)
  have := charP_quotient_span hϖ he hℓe
  let := ZMod.algebra (R ⧸ Ideal.span {ϖ}) ℓ
  have hfree : Module.IsTorsionFree ℤ_[ℓ] R :=
    (Module.isTorsionFree_iff_algebraMap_injective).2 (injective_algebraMap_padicInt hϖ hℓe)
  have : Module.Free ℤ_[ℓ] R := Module.free_of_finite_type_torsion_free'
  -- `A ≅ ℤ/ℓ^N ⊗_{ℤ_ℓ} R` as `ℤ/ℓ^N`-modules
  let e₀ := (quotientLinearEquivTensor hℓe N).toAddEquiv
  let eZ : (R ⧸ Ideal.span {ϖ ^ (e * N)}) ≃ₗ[ZMod (ℓ ^ N)] ZMod (ℓ ^ N) ⊗[ℤ_[ℓ]] R :=
    { e₀.toAddMonoidHom.toZModLinearMap (ℓ ^ N) with
      invFun := e₀.symm
      left_inv := e₀.left_inv
      right_inv := e₀.right_inv }
  have hF : Module.Free (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)}) :=
    Module.Free.of_equiv eZ.symm
  have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN.ne' hℓ.out.one_lt⟩
  have hr : Module.finrank (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)}) =
      Module.finrank ℤ_[ℓ] R :=
    eZ.finrank_eq.trans Module.finrank_baseChange
  refine ⟨hF, hr, ?_⟩
  -- counting: `ℓ^{N r} = #A = #(R/ϖ)^{eN} = ℓ^{f e N}`
  have : Module.Finite (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)}) :=
    Module.Finite.equiv eZ.symm
  have : NeZero (ℓ ^ N) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  set r := Module.finrank (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)})
  have hcardA : Nat.card (R ⧸ Ideal.span {ϖ ^ (e * N)}) = (ℓ ^ N) ^ r := by
    rw [Nat.card_congr (Module.finBasis (ZMod (ℓ ^ N))
      (R ⧸ Ideal.span {ϖ ^ (e * N)})).equivFun.toEquiv, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
  have hfinA : Finite (R ⧸ Ideal.span {ϖ ^ (e * N)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcardA]; exact pow_ne_zero _ (NeZero.ne _))
  have hle : Ideal.span {ϖ ^ (e * N)} ≤ Ideal.span {ϖ} :=
    Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self ϖ (Nat.mul_pos he hN).ne')
  have hfinK : Finite (R ⧸ Ideal.span {ϖ}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have : (Ideal.span {ϖ}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible hϖ).isPrime
  have hcardA' : Nat.card (R ⧸ Ideal.span {ϖ ^ (e * N)}) =
      Nat.card (R ⧸ Ideal.span {ϖ}) ^ (e * N) := by
    rw [← Ideal.span_singleton_pow, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply,
      cardQuot_pow_of_prime (by simpa using hϖ.ne_zero)]
  have : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  have hcardK : Nat.card (R ⧸ Ideal.span {ϖ}) =
      ℓ ^ Module.finrank (ZMod ℓ) (R ⧸ Ideal.span {ϖ}) := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod ℓ), ZMod.card]
  rw [hcardA', hcardK, ← pow_mul, ← pow_mul] at hcardA
  have h := Nat.pow_right_injective hℓ.out.two_le hcardA
  have : N * r = N * (e * Module.finrank (ZMod ℓ) (R ⧸ Ideal.span {ϖ})) := by
    rw [← h]; ring
  exact Nat.eq_of_mul_eq_mul_left hN this

end IsDiscreteValuationRing

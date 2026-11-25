/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Module.AdicDualityTransport
public import WeilConjectures.Algebra.Module.RationalPerfectPairing
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantHCup

/-!
# Perfectness of the cup product pairing on `H^*(S_proét, ℚ̄_ℓ)` from the finite levels

Let `S` be a quasi-compact quasi-separated scheme with finite cohomology groups `Hᵏ(S, ℤ/ℓᵐ)`, and
`i + j = n`. Suppose that at every finite level `m` the cup product pairing
`Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ Hⁿ(S, ℤ/ℓᵐ)` is nondegenerate on both sides, and that
`Hⁿ(S, ℚ̄_ℓ)` is a line, `t : Hⁿ(S, ℚ̄_ℓ) ≅ ℚ̄_ℓ`. Then the pairing
`(v, w) ↦ t(v ⌣ w) : Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` is perfect
(`AlgebraicGeometry.ProEtale.isPerfPair_adicConstantHCup`).

The proof transports the finite-level nondegeneracy to the integral cohomology `Hᵏ(S, ℤ_ℓ)`: if
`a ⌣ b` is torsion for all `b`, then by the Bockstein sequences (`ℓᵉ` killing the torsion) the
reduction of `ℓ^{2e} a` modulo `ℓᵐ` pairs to zero with all of `Hʲ(S, ℤ/ℓᵐ)`, hence vanishes, so that
`ℓ^{2e} a ∈ ⋂ₘ ℓᵐ Hⁱ(S, ℤ_ℓ) = 0`. Since `Hⁿ(S, ℤ_ℓ)` has rank one, `t` restricts to an integral
pairing with torsion kernels, whose extension to `ℚ̄_ℓ` is perfect
(`LinearMap.isPerfPair_of_span_eq_top`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian Function

/-- Multiplying a perfect pairing over a field by a nonzero scalar gives a perfect pairing. -/
lemma LinearMap.IsPerfPair.smul_of_ne_zero {K M N : Type*} [Field K] [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N] {p : M →ₗ[K] N →ₗ[K] K} (hp : p.IsPerfPair)
    {c : K} (hc : c ≠ 0) : (c • p).IsPerfPair := by
  have hflip : (c • p).flip = c • p.flip := by
    ext x y
    rfl
  exact ⟨(LinearEquiv.smulOfNeZero K _ c hc).bijective.comp hp.bijective_left,
    hflip ▸ (LinearEquiv.smulOfNeZero K _ c hc).bijective.comp hp.bijective_right⟩

namespace AlgebraicGeometry.ProEtale

open Scheme PadicInt

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
  (hfin : ∀ m k, Finite (FiniteAdicH S l m k))

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- `ℓ` is a nonzero element of `ℤ_ℓ`. -/
lemma natCast_ne_zero_padicInt : (l : ℤ_[l]) ≠ 0 :=
  Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

/-- **Left kernel, integral level.** If `ℓᵉ` kills the `ℓ`-power torsion of `Hʲ⁺¹(S, ℤ_ℓ)` and
`ℓᵉ (a ⌣ b) = 0` for all `b ∈ Hʲ(S, ℤ_ℓ)`, then `ℓ^{2e} a ∈ ℓᵐ Hⁱ(S, ℤ_ℓ)` for every `m`. -/
theorem exists_pow_smul_eq_of_integralAdicHCup_left {i j n : ℕ} (h : i + j = n)
    (hl : ∀ m (x : FiniteAdicH S l m i), (∀ y, finiteAdicHCup l m S h x y = 0) → x = 0)
    {e : ℕ} (he : ∀ x : IntegralAdicH S l (j + 1), (∃ k, (l : ℤ_[l]) ^ k • x = 0) →
      (l : ℤ_[l]) ^ e • x = 0)
    (m : ℕ) {a : IntegralAdicH S l i}
    (ha : ∀ b, (l : ℤ_[l]) ^ e • integralAdicHCup l S hfin h a b = 0) :
    ∃ a', (l : ℤ_[l]) ^ (2 * e) • a = (l : ℤ_[l]) ^ m • a' := by
  refine exists_eq_pow_smul_of_reduction_eq_zero S l m i (hl m _ fun y ↦ ?_)
  obtain ⟨b, hb⟩ := pow_smul_mem_range_reduction S l m j e he y
  rw [two_mul, pow_add, mul_smul, LinearMap.map_smul (reduction S l m i),
    finiteAdicHCup_smul_left, ← finiteAdicHCup_smul_right, ← hb,
    ← reduction_integralAdicHCup l S hfin h, LinearMap.map_smul₂, ha, map_zero]

/-- **Right kernel, integral level.** If `ℓᵉ` kills the `ℓ`-power torsion of `Hⁱ⁺¹(S, ℤ_ℓ)` and
`ℓᵉ (a ⌣ b) = 0` for all `a ∈ Hⁱ(S, ℤ_ℓ)`, then `ℓ^{2e} b ∈ ℓᵐ Hʲ(S, ℤ_ℓ)` for every `m`. -/
theorem exists_pow_smul_eq_of_integralAdicHCup_right {i j n : ℕ} (h : i + j = n)
    (hr : ∀ m (y : FiniteAdicH S l m j), (∀ x, finiteAdicHCup l m S h x y = 0) → y = 0)
    {e : ℕ} (he : ∀ x : IntegralAdicH S l (i + 1), (∃ k, (l : ℤ_[l]) ^ k • x = 0) →
      (l : ℤ_[l]) ^ e • x = 0)
    (m : ℕ) {b : IntegralAdicH S l j}
    (hb : ∀ a, (l : ℤ_[l]) ^ e • integralAdicHCup l S hfin h a b = 0) :
    ∃ b', (l : ℤ_[l]) ^ (2 * e) • b = (l : ℤ_[l]) ^ m • b' := by
  refine exists_eq_pow_smul_of_reduction_eq_zero S l m j (hr m _ fun x ↦ ?_)
  obtain ⟨a, ha⟩ := pow_smul_mem_range_reduction S l m i e he x
  rw [two_mul, pow_add, mul_smul, LinearMap.map_smul (reduction S l m j),
    finiteAdicHCup_smul_right, ← finiteAdicHCup_smul_left, ← ha,
    ← reduction_integralAdicHCup l S hfin h, map_smul, hb, map_zero]

/-- **The integral trace.** If `t : Hⁿ(S, ℚ̄_ℓ) ≅ ℚ̄_ℓ` and `Hⁿ(S, ℤ_ℓ)` is finitely generated,
then `t ∘ ι = c₀ · t₀` for a nonzero `c₀ ∈ ℚ̄_ℓ` and a `ℤ_ℓ`-linear form `t₀` on `Hⁿ(S, ℤ_ℓ)`
whose kernel is torsion: `Hⁿ(S, ℤ_ℓ)` has rank one. -/
theorem exists_integral_trace {n : ℕ} [Module.Finite ℤ_[l] (IntegralAdicH S l n)]
    (t : AdicConstantH l S n ≃ₗ[PadicAlgCl l] PadicAlgCl l) :
    ∃ c₀ : PadicAlgCl l, c₀ ≠ 0 ∧ ∃ t₀ : IntegralAdicH S l n →ₗ[ℤ_[l]] ℤ_[l],
      (∀ z, t (integralToAdicConstantH l S n z) =
        c₀ * algebraMap ℤ_[l] (PadicAlgCl l) (t₀ z)) ∧
      ∀ z, t₀ z = 0 → z ∈ Submodule.torsion ℤ_[l] (IntegralAdicH S l n) := by
  classical
  set K := PadicAlgCl l
  set ι := integralToAdicConstantH l S n
  set T := Submodule.torsion ℤ_[l] (IntegralAdicH S l n)
  let bC := Module.Free.chooseBasis ℤ_[l] (IntegralAdicH S l n ⧸ T)
  let c (k) : IntegralAdicH S l n := (T.mkQ_surjective (bC k)).choose
  have hc (k) : T.mkQ (c k) = bC k := (T.mkQ_surjective (bC k)).choose_spec
  have hT (z : IntegralAdicH S l n) (hz : ∀ k, bC.repr (T.mkQ z) k = 0) : z ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    exact bC.ext_elem fun k ↦ by rw [hz, map_zero, Finsupp.zero_apply]
  let g : IntegralAdicH S l n →ₗ[ℤ_[l]] (Module.Free.ChooseBasisIndex ℤ_[l]
      (IntegralAdicH S l n ⧸ T) → K) :=
    LinearMap.pi fun k ↦ (Algebra.linearMap ℤ_[l] K) ∘ₗ (bC.coord k ∘ₗ T.mkQ)
  let Φ := (isBaseChange_integralToAdicConstantH l S n).lift g
  have hΦc (k) : Φ (ι (c k)) = Pi.single k 1 := by
    rw [IsBaseChange.lift_eq]
    ext k'
    simp only [g, LinearMap.pi_apply, LinearMap.comp_apply, hc, Module.Basis.coord_apply,
      Module.Basis.repr_self, Algebra.linearMap_apply, Finsupp.single_apply, Pi.single_apply,
      eq_comm (a := k')]
    split_ifs <;> simp
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex ℤ_[l] (IntegralAdicH S l n ⧸ T)) := by
    refine ⟨fun k k' ↦ by_contra fun hkk ↦ ?_⟩
    have he (k) : Pi.single k 1 = t (ι (c k)) • Φ (t.symm 1) := by
      rw [← map_smul, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply, hΦc]
    have h1 := congr_fun (he k) k'
    have h2 := congr_fun (he k') k'
    have h3 := congr_fun (he k) k
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne' hkk, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
    have hu : Φ (t.symm 1) k' ≠ 0 := right_ne_zero_of_mul (h2.symm ▸ one_ne_zero)
    rw [(mul_eq_zero.1 h1.symm).resolve_right hu, zero_mul] at h3
    exact one_ne_zero h3
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex ℤ_[l] (IntegralAdicH S l n ⧸ T))
    with hJ | hJ
  · refine ⟨1, one_ne_zero, 0, fun z ↦ ?_, fun z _ ↦ hT z fun k ↦ isEmptyElim k⟩
    rw [LinearMap.zero_apply, map_zero, mul_zero,
      LinearMap.map_eq_zero_of_mem_torsion K ι (hT z fun k ↦ isEmptyElim k), map_zero]
  · obtain ⟨k₀⟩ := hJ
    refine ⟨t (ι (c k₀)), fun h0 ↦ ?_, bC.coord k₀ ∘ₗ T.mkQ, fun z ↦ ?_, fun z hz ↦ hT z
      fun k ↦ (Subsingleton.elim k k₀) ▸ hz⟩
    · have h0' : ι (c k₀) = 0 := t.map_eq_zero_iff.1 h0
      have := congr_fun (hΦc k₀) k₀
      rw [h0', map_zero, Pi.single_eq_same] at this
      exact zero_ne_one this
    · set r := (bC.coord k₀ ∘ₗ T.mkQ) z
      have hdec : z - r • c k₀ ∈ T := by
        refine hT _ fun k ↦ ?_
        obtain rfl := Subsingleton.elim k k₀
        rw [map_sub, map_smul, hc, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
          Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]
        exact sub_self _
      have hz := LinearMap.map_eq_zero_of_mem_torsion K ι hdec
      rw [map_sub, sub_eq_zero] at hz
      rw [hz, map_smul, ← algebraMap_smul K, map_smul, smul_eq_mul, mul_comm]

/-- **Perfectness of the `ℚ̄_ℓ`-cup product pairing from the finite levels.** If at every level
`ℤ/ℓᵐ` the cup product pairing `Hⁱ × Hʲ ⟶ Hⁿ` is nondegenerate on both sides and `Hⁿ(S, ℚ̄_ℓ)` is
a line `t : Hⁿ(S, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, then `(v, w) ↦ t(v ⌣ w)` is a perfect pairing on
`Hⁱ(S, ℚ̄_ℓ) × Hʲ(S, ℚ̄_ℓ)`. -/
theorem isPerfPair_adicConstantHCup {i j n : ℕ} (h : i + j = n)
    (hl : ∀ m (x : FiniteAdicH S l m i), (∀ y, finiteAdicHCup l m S h x y = 0) → x = 0)
    (hr : ∀ m (y : FiniteAdicH S l m j), (∀ x, finiteAdicHCup l m S h x y = 0) → y = 0)
    (t : AdicConstantH l S n ≃ₗ[PadicAlgCl l] PadicAlgCl l) :
    ((adicConstantHCup l S hfin h).compr₂ t.toLinearMap).IsPerfPair := by
  classical
  have hfg (k : ℕ) : Module.Finite ℤ_[l] (IntegralAdicH S l k) := by
    have := hfin 1 k
    exact module_finite_integralAdicH S l k fun m k' _ ↦ hfin m k'
  obtain ⟨c₀, hc₀, t₀, ht, ht₀⟩ := exists_integral_trace l S t
  -- a single power `ℓᵉ` killing the torsion of `Hⁿ`, `Hʲ⁺¹` and `Hⁱ⁺¹`
  have hexp (k : ℕ) : ∃ e : ℕ, ∀ x : IntegralAdicH S l k, (∃ d, (l : ℤ_[l]) ^ d • x = 0) →
      (l : ℤ_[l]) ^ e • x = 0 :=
    Submodule.exists_pow_smul_eq_zero_of_isNoetherian _
  obtain ⟨e₁, he₁⟩ := hexp n
  obtain ⟨e₂, he₂⟩ := hexp (j + 1)
  obtain ⟨e₃, he₃⟩ := hexp (i + 1)
  set e := max e₁ (max e₂ e₃)
  have hle {k e' : ℕ} (hk : e' ≤ e) (he' : ∀ x : IntegralAdicH S l k,
      (∃ d, (l : ℤ_[l]) ^ d • x = 0) → (l : ℤ_[l]) ^ e' • x = 0) (x : IntegralAdicH S l k)
      (hx : ∃ d, (l : ℤ_[l]) ^ d • x = 0) : (l : ℤ_[l]) ^ e • x = 0 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    rw [hd, pow_add, mul_comm, mul_smul, he' x hx, smul_zero]
  have hcupT (a : IntegralAdicH S l i) (b : IntegralAdicH S l j)
      (hab : t₀ (integralAdicHCup l S hfin h a b) = 0) :
      (l : ℤ_[l]) ^ e • integralAdicHCup l S hfin h a b = 0 :=
    hle (le_max_left _ _) he₁ _ (LinearMap.exists_pow_smul_eq_zero_of_mem_torsion (ht₀ _ hab))
  set P := (integralAdicHCup l S hfin h).compr₂ t₀
  set Q := c₀⁻¹ • (adicConstantHCup l S hfin h).compr₂ t.toLinearMap
  have hl0 : ¬IsUnit (l : ℤ_[l]) := PadicInt.p_nonunit
  have hQ (a : IntegralAdicH S l i) (b : IntegralAdicH S l j) :
      Q (integralToAdicConstantH l S i a) (integralToAdicConstantH l S j b) =
        algebraMap ℤ_[l] (PadicAlgCl l) (P a b) := by
    simp only [Q, P, LinearMap.smul_apply, LinearMap.compr₂_apply,
      adicConstantHCup_integralToAdicConstantH, LinearEquiv.coe_coe, ht, smul_eq_mul,
      inv_mul_cancel_left₀ hc₀]
  have hspan (k : ℕ) :
      Submodule.span (PadicAlgCl l) (Set.range (integralToAdicConstantH l S k)) = ⊤ :=
    eq_top_iff.2 fun x _ ↦ (isBaseChange_integralToAdicConstantH l S k).inductionOn x
      (fun z ↦ Submodule.subset_span ⟨z, rfl⟩)
      (fun s _ hx ↦ Submodule.smul_mem _ s hx) (fun _ _ ↦ Submodule.add_mem _)
  have hperf := LinearMap.isPerfPair_of_span_eq_top _ _ (hspan i) (hspan j) P Q hQ
    (fun a ha ↦ LinearMap.mem_torsion_of_pow_smul_eq P hl0 (natCast_ne_zero_padicInt l)
      (Nat.lt_succ_self (2 * e)) (fun a ha ↦ exists_pow_smul_eq_of_integralAdicHCup_left l S
        hfin h hl (hle (le_max_of_le_right (le_max_left _ _)) he₂) _
        fun b ↦ hcupT a b (LinearMap.congr_fun ha b)) ha)
    (fun b hb ↦ LinearMap.mem_torsion_of_pow_smul_eq P.flip hl0 (natCast_ne_zero_padicInt l)
      (Nat.lt_succ_self (2 * e)) (fun b hb ↦ exists_pow_smul_eq_of_integralAdicHCup_right l S
        hfin h hr (hle (le_max_of_le_right (le_max_right _ _)) he₃) _
        fun a ↦ hcupT a b (LinearMap.congr_fun hb a)) hb)
  have hQ' : (adicConstantHCup l S hfin h).compr₂ t.toLinearMap = c₀ • Q := by
    rw [smul_inv_smul₀ hc₀]
  rw [hQ']
  exact hperf.smul_of_ne_zero hc₀

end AlgebraicGeometry.ProEtale

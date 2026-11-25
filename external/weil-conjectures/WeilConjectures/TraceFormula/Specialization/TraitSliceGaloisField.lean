/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Trunc
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisHensel
public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental

/-!

# Separable roots of `k'⟦t⟧`-polynomials in `K⟦t⟧`

Let `k'` be a separably closed field and `K` an algebraically closed extension of transcendence
degree `≤ 1` (for the generic slices, `K = k'(x)^alg`). We show that a simple root `α ∈ K⟦t⟧` of a
polynomial with coefficients in `k'⟦t⟧` is purely inseparable over `k'⟦t⟧`: some `p`-power `α^q`
lies in `k'⟦t⟧` (`PowerSeries.exists_pow_mem_range_map_of_isRoot`). This is the algebraic heart of
the surjectivity of inertia `I_{K((t))} ⟶ I_{k'((t))}` (SGA 4½, [Th. finitude], Lemme 3.3):
`k'((t))` is separably closed in `K((t))`.

The proof has three steps.

* **The coefficients of `α` are algebraic over `k'`**
  (`PowerSeries.isAlgebraic_coeff_of_isRoot`): if a coefficient `y` of `α` were transcendental,
  `K` would be an algebraic closure of `k'[y]` (transcendence degree `≤ 1`), so the automorphisms
  `y ↦ y + c` (`c ∈ k'`) of `k'[y]` would extend to automorphisms of `K` fixing `k'`, moving `α`
  to infinitely many distinct roots of the same polynomial.
* **Newton's lemma**: since `k'` is separably closed, finitely many coefficients of `α` lie in the
  purely inseparable extension `k'' = {a | a^q ∈ k'}` of `k'`; Newton's lemma over `k''⟦t⟧` and the
  uniqueness of simple roots show that `α ∈ k''⟦t⟧`.
* **Frobenius**: `α^q = Frob^q(expand_q α) ∈ k'⟦t⟧`.

-/

@[expose] public section

universe u

open Polynomial

namespace PowerSeries

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- A power series lies in the image of a coefficientwise map if and only if all its coefficients
lie in the image. -/
lemma mem_range_map_iff {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (φ : S⟦X⟧) :
    φ ∈ (map g).range ↔ ∀ n, coeff n φ ∈ g.range := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩ n
    exact ⟨coeff n ψ, (coeff_map g n ψ).symm⟩
  · choose c hc using h
    exact ⟨mk c, ext fun n ↦ by simp [hc]⟩

/-- A coefficientwise ring homomorphism fixing `k'` maps roots of polynomials over `k'⟦t⟧` to
roots. -/
lemma isRoot_map_map_of_comp_eq (τ : K →+* K) (hτ : τ.comp (algebraMap k' K) = algebraMap k' K)
    {f : (PowerSeries k')[X]} {α : K⟦X⟧} (hα : (f.map (map (algebraMap k' K))).IsRoot α) :
    (f.map (map (algebraMap k' K))).IsRoot (map τ α) := by
  have hc : (map τ).comp (map (algebraMap k' K)) = map (algebraMap k' K) := by
    rw [← map_comp, hτ]
  rw [IsRoot.def, eval_map] at hα ⊢
  rw [← hc, ← hom_eval₂, hα, map_zero]

variable [IsAlgClosed K]

/-- **The coefficients of a root are algebraic**: let `K` be algebraically closed of transcendence
degree `≤ 1` over an infinite field `k'`. Every coefficient of a root `α ∈ K⟦t⟧` of a nonzero
polynomial with coefficients in `k'⟦t⟧` is algebraic over `k'`. Otherwise the extensions to `K` of
the automorphisms `y ↦ y + c` of `k'[y]`, `y` the coefficient, would give infinitely many roots. -/
theorem isAlgebraic_coeff_of_isRoot [Infinite k'] (htr : Algebra.trdeg k' K ≤ 1)
    {f : (PowerSeries k')[X]} (hf : f.map (map (algebraMap k' K)) ≠ 0) {α : K⟦X⟧}
    (hα : (f.map (map (algebraMap k' K))).IsRoot α) (n : ℕ) :
    IsAlgebraic k' (coeff n α) := by
  by_contra hy
  set y := coeff n α with hy_def
  have hind : AlgebraicIndependent k' (fun _ : PUnit.{u + 1} ↦ y) :=
    (algebraicIndependent_unique_type_iff (x := fun _ : PUnit.{u + 1} ↦ y)).mpr hy
  have hB : IsTranscendenceBasis k' (fun _ : PUnit.{u + 1} ↦ y) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (htr.trans (Cardinal.mk_eq_one _).ge)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin k' {y}) K := by
    have := hB.isAlgebraic
    rwa [Set.range_const] at this
  have : IsAlgClosure (Algebra.adjoin k' {y}) K := ⟨inferInstance, halg⟩
  let e := Polynomial.algEquivOfTranscendental k' y hy
  let σ : k' → Algebra.adjoin k' {y} ≃ₐ[k'] Algebra.adjoin k' {y} := fun c ↦
    (e.symm.trans (algEquivAevalXAddC c)).trans e
  let τ : k' → K ≃+* K := fun c ↦
    IsAlgClosure.equivOfEquiv K K (σ c : Algebra.adjoin k' {y} ≃+* Algebra.adjoin k' {y})
  have hτk : ∀ c, (τ c : K →+* K).comp (algebraMap k' K) = algebraMap k' K := by
    intro c
    ext a
    have h1 : algebraMap k' K a = algebraMap (Algebra.adjoin k' {y}) K
        (algebraMap k' (Algebra.adjoin k' {y}) a) := rfl
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  have hτy : ∀ c, τ c y = y + algebraMap k' K c := by
    intro c
    have h1 : y = algebraMap (Algebra.adjoin k' {y}) K
        ⟨y, Algebra.self_mem_adjoin_singleton k' y⟩ := rfl
    conv_lhs => rw [h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    simp [σ, e]
  have hinj : Function.Injective fun c ↦ map (τ c : K →+* K) α := by
    intro c d hcd
    have := congr(coeff n $hcd)
    simp only [coeff_map, RingHom.coe_coe, ← hy_def, hτy, add_right_inj] at this
    exact (algebraMap k' K).injective this
  exact (Set.infinite_of_injective_forall_mem hinj fun c ↦
    isRoot_map_map_of_comp_eq _ (hτk c) hα) (finite_setOfPred_isRoot hf)


end PowerSeries

namespace PowerSeries

section Aux

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Evaluation of polynomials commutes with ring homomorphisms. -/
lemma map_eval_eq (g : R →+* S) (P : R[X]) (x : R) : g (P.eval x) = (P.map g).eval (g x) := by
  rw [eval_map, eval₂_at_apply]

/-- Divisibility by powers of `t` is detected after an injective coefficientwise map. -/
lemma X_pow_dvd_map_iff {g : R →+* S} (hg : Function.Injective g) {n : ℕ} {φ : R⟦X⟧} :
    X ^ n ∣ map g φ ↔ X ^ n ∣ φ := by
  simp only [X_pow_dvd_iff, coeff_map]
  exact forall₂_congr fun _ _ ↦ by rw [map_eq_zero_iff g hg]

/-- Over a field, a nonzero power series is `tᵉ` times a unit, `e` its order. -/
lemma exists_eq_X_pow_mul_isUnit {k : Type*} [Field k] {φ : k⟦X⟧} (hφ : φ ≠ 0) :
    ∃ u, IsUnit u ∧ φ = X ^ φ.order.toNat * u :=
  ⟨divXPowOrder φ, isUnit_iff_constantCoeff.mpr (by
    rw [constantCoeff_divXPowOrder]
    exact (coeff_order hφ).isUnit), X_pow_order_mul_divXPowOrder.symm⟩

/-- A unit plus a multiple of `t` is a unit. -/
lemma isUnit_add_X_mul {k : Type*} [Field k] {u : k⟦X⟧} (hu : IsUnit u) (w : k⟦X⟧) :
    IsUnit (u + X * w) := by
  rw [isUnit_iff_constantCoeff] at hu ⊢
  simpa using hu

/-- A unit is not divisible by `t`. -/
lemma not_X_dvd_of_isUnit {k : Type*} [Field k] {u : k⟦X⟧} (hu : IsUnit u) : ¬ X ∣ u := by
  rintro ⟨w, rfl⟩
  rw [isUnit_iff_constantCoeff] at hu
  simp at hu

/-- **Frobenius on power series**: in exponential characteristic `p`,
`φ^(p^m) = Frob^m(expand_{p^m} φ)`. -/
lemma pow_expChar_pow_eq_map_expand (p : ℕ) [ExpChar R p] (φ : R⟦X⟧) (m : ℕ) :
    φ ^ p ^ m = map (iterateFrobenius R p m)
      (expand (p ^ m) (pow_ne_zero m (expChar_ne_zero R p)) φ) :=
  (MvPowerSeries.map_iterateFrobenius_expand p (expChar_ne_zero R p) φ m).symm

end Aux

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] [IsAlgClosed K]
  [IsSepClosed k'] (p : ℕ) [ExpChar k' p]

/-- **Simple roots in `K⟦t⟧` are purely inseparable over `k'⟦t⟧`**: let `k'` be separably closed
of exponential characteristic `p` and `K` algebraically closed of transcendence degree `≤ 1` over
`k'`. If `α ∈ K⟦t⟧` is a simple root of a polynomial with coefficients in `k'⟦t⟧`, then
`α^(p^m) ∈ k'⟦t⟧` for some `m`. -/
theorem exists_pow_mem_range_map_of_isRoot (htr : Algebra.trdeg k' K ≤ 1)
    {f : (PowerSeries k')[X]} {α : K⟦X⟧} (hα : (f.map (map (algebraMap k' K))).IsRoot α)
    (hα' : (f.map (map (algebraMap k' K))).derivative.eval α ≠ 0) :
    ∃ m : ℕ, α ^ p ^ m ∈ (map (algebraMap k' K)).range := by
  have hK : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k' K).injective p
  set F := f.map (map (algebraMap k' K)) with hF_def
  have hF : F ≠ 0 := by
    rintro h
    simp [h] at hα'
  set D := F.derivative.eval α with hD_def
  set e := D.order.toNat
  obtain ⟨u, hu, hDu⟩ := exists_eq_X_pow_mul_isUnit hα'
  -- the coefficients of `α` are purely inseparable over `k'`
  have hpow : ∀ i, ∃ m, coeff i α ^ p ^ m ∈ (algebraMap k' K).range := by
    intro i
    have hmem : coeff i α ∈ algebraicClosure k' K :=
      mem_algebraicClosure_iff.mpr (isAlgebraic_coeff_of_isRoot htr hF hα i)
    obtain ⟨m, r, hr⟩ := IsPurelyInseparable.pow_mem k' p
      (⟨coeff i α, hmem⟩ : algebraicClosure k' K)
    exact ⟨m, r, congr_arg Subtype.val hr⟩
  choose mf hmf using hpow
  set N := 2 * e + 1 with hN
  set M := (Finset.range N).sup mf
  have hmono : ∀ {a : K} {m m' : ℕ}, m ≤ m' → a ^ p ^ m ∈ (algebraMap k' K).range →
      a ^ p ^ m' ∈ (algebraMap k' K).range := by
    intro a m m' hmm' ha
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmm'
    rw [pow_add, pow_mul]
    exact pow_mem ha _
  -- the purely inseparable extension `k'' = {a | a^(p^M) ∈ k'}`
  let k'' : Subfield K := ((algebraMap k' K).fieldRange).comap (iterateFrobenius K p M)
  have hk'' : ∀ a : K, a ∈ k'' ↔ a ^ p ^ M ∈ (algebraMap k' K).range := fun a ↦ Iff.rfl
  let ι₂ : k'' →+* K := k''.subtype
  have hι₂ : Function.Injective ι₂ := Subtype.val_injective
  let ι₁ : k' →+* k'' := (algebraMap k' K).codRestrict k'' fun a ↦ by
    rw [hk'']
    exact ⟨a ^ p ^ M, by simp⟩
  have hι : ι₂.comp ι₁ = algebraMap k' K := rfl
  -- the truncation `β` of `α` has coefficients in `k''`
  set β : K⟦X⟧ := ((trunc N α : K[X]) : K⟦X⟧) with hβ_def
  obtain ⟨β'', hβ''⟩ : β ∈ (map ι₂).range := by
    refine (mem_range_map_iff _ _).2 fun i ↦ ?_
    rw [hβ_def, Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hi
    · refine ⟨⟨coeff i α, (hk'' _).2 (hmono ?_ (hmf i))⟩, rfl⟩
      exact Finset.le_sup (Finset.mem_range.mpr hi)
    · exact zero_mem _
  set f'' := f.map (map ι₁)
  have hf'' : f''.map (map ι₂) = F := by
    rw [Polynomial.map_map, ← map_comp, hι]
  have hαβ : X ^ N ∣ α - β := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [map_sub, hβ_def, coeff_coe_trunc_of_lt hi, sub_self]
  -- `t^N ∣ F(β)` and `F'(β) = tᵉ u'` with `u'` a unit
  have hFβ : X ^ N ∣ F.eval β := by
    have h := sub_dvd_eval_sub α β F
    rw [hα.eq_zero, zero_sub, dvd_neg] at h
    exact hαβ.trans h
  set c := F.derivative.eval β with hc_def
  obtain ⟨u', hu', hcu⟩ : ∃ u', IsUnit u' ∧ c = X ^ e * u' := by
    have h := sub_dvd_eval_sub β α F.derivative
    rw [← hc_def, ← hD_def] at h
    obtain ⟨w, hw⟩ := (dvd_sub_comm.mp hαβ).trans h
    refine ⟨u + X ^ (e + 1) * w, ?_, ?_⟩
    · rw [pow_succ', mul_assoc]
      exact isUnit_add_X_mul hu _
    · rw [hN] at hw
      linear_combination hw + hDu
  -- transport to `k''⟦t⟧`
  have hmapc : map ι₂ (f''.derivative.eval β'') = c := by
    rw [map_eval_eq, ← derivative_map, hf'', hβ'']
  have hmapf : map ι₂ (f''.eval β'') = F.eval β := by
    rw [map_eval_eq, hf'', hβ'']
  obtain ⟨v, hv⟩ : X ^ e ∣ f''.derivative.eval β'' := by
    rw [← X_pow_dvd_map_iff hι₂ , hmapc, hcu]
    exact dvd_mul_right _ _
  have hvu : map ι₂ v = u' := by
    have h := congr(map ι₂ $hv)
    rw [hmapc, hcu, map_mul, map_pow, map_X] at h
    exact (mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) h).symm
  have hvunit : IsUnit v := by
    rw [isUnit_iff_constantCoeff] at hu' ⊢
    rw [← hvu] at hu'
    have : constantCoeff (map ι₂ v) = ι₂ (constantCoeff v) := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
    rw [this] at hu'
    exact isUnit_iff_ne_zero.mpr fun h ↦ by simp [h] at hu'
  have hnewton : (f''.derivative.eval β'') ^ 2 * X ∣ f''.eval β'' := by
    rw [hv, mul_pow, ← pow_mul, mul_right_comm, ← pow_succ]
    refine (IsUnit.mul_right_dvd (hvunit.pow 2)).mpr ?_
    rw [← X_pow_dvd_map_iff hι₂, hmapf]
    rwa [mul_comm e 2]
  obtain ⟨γ'', hγ'', hγβ''⟩ := Polynomial.exists_isRoot_powerSeries_of_sq_mul_X_dvd f'' β'' hnewton
  -- the root `γ` of `F` close to `β` is `α`
  set γ := map ι₂ γ''
  have hγ : F.IsRoot γ := by
    rw [IsRoot.def, ← hf'', ← map_eval_eq, hγ''.eq_zero, map_zero]
  have hγβ : X ^ (e + 1) ∣ γ - β := by
    have h := map_dvd (map ι₂) hγβ''
    rw [map_mul, hmapc, map_X, map_sub, hβ'', hcu, mul_right_comm, ← pow_succ] at h
    exact (dvd_mul_right _ _).trans h
  have hαγ : α = γ := by
    refine (Polynomial.eq_or_sub_dvd_derivative_eval_of_isRoot hα hγ).resolve_right fun h ↦ ?_
    have h1 : X ^ (e + 1) ∣ α - γ := by
      have : α - γ = (α - β) - (γ - β) := by ring
      rw [this]
      exact dvd_sub ((pow_dvd_pow X (by omega)).trans hαβ) hγβ
    rw [← hD_def, hDu] at h
    rw [pow_succ] at h1
    exact not_X_dvd_of_isUnit hu ((mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero)).mp
      (h1.trans h))
  -- Frobenius
  refine ⟨M, (mem_range_map_iff _ _).2 fun n ↦ ?_⟩
  rw [pow_expChar_pow_eq_map_expand p α M, coeff_map, coeff_expand]
  split_ifs
  · have : coeff (n / p ^ M) α ∈ k'' := by
      rw [hαγ, coeff_map]
      exact (coeff (n / p ^ M) γ'').2
    exact this
  · rw [map_zero]
    exact zero_mem _

end PowerSeries

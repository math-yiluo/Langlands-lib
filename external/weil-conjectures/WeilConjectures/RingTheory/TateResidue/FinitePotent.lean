/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.PID

/-!
# Finite-potent endomorphisms and their trace

Following J. Tate, *Residues of differentials on curves* (Ann. Sci. ENS 1968), §1, an
endomorphism `φ` of a vector space `V` over a field `k` is *finite-potent* if `φ ^ n (V)` is
finite-dimensional for some `n`. Its trace `Tr_V φ` is the trace of `φ` on any finite-dimensional
`φ`-stable subspace `W` containing some `φ ^ n (V)`; this does not depend on `W`.

## Main definitions

- `Module.End.IsFinitePotent φ`: some power of `φ` has finite-dimensional range.
- `Module.End.tateTrace φ`: Tate's trace of a finite-potent endomorphism (`0` otherwise).

## Main results

- `Module.End.tateTrace_eq_trace_restrict`: `Tr_V φ` is the trace of `φ` on any
  finite-dimensional `φ`-stable subspace containing `φ ^ n (V)`.
- `Module.End.tateTrace_eq_add_of_exact`: additivity in short exact sequences (Tate's (T1)).
- `Module.End.tateTrace_eq_zero_of_pow_eq_zero`: the trace of a nilpotent map vanishes (T2).
- `Module.End.tateTrace_sum`: additivity on families whose pairwise products have
  finite-dimensional range (T3).
- `Module.End.tateTrace_comp_comm`: `Tr (b ∘ a) = Tr (a ∘ b)` when `b ∘ a` is finite-potent.
-/

@[expose] public section

open LinearMap Submodule

/-- Additivity of the trace in a short exact sequence of finite-dimensional spaces. -/
theorem LinearMap.trace_eq_add_of_exact {k M₁ M₂ M₃ : Type*} [Field k]
    [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃]
    [Module k M₃] [FiniteDimensional k M₁] [FiniteDimensional k M₂] [FiniteDimensional k M₃]
    (i : M₁ →ₗ[k] M₂) (q : M₂ →ₗ[k] M₃) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : Function.Exact i q) (g₁ : Module.End k M₁)
    (g₂ : Module.End k M₂) (g₃ : Module.End k M₃) (h₁ : g₂ ∘ₗ i = i ∘ₗ g₁)
    (h₃ : q ∘ₗ g₂ = g₃ ∘ₗ q) :
    trace k M₂ g₂ = trace k M₁ g₁ + trace k M₃ g₃ := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (range_eq_top.2 hq)
  obtain ⟨r₀, hr₀⟩ := i.exists_leftInverse_of_injective (ker_eq_bot.2 hi)
  have hqs : ∀ y, q (s y) = y := fun y ↦ congr($hs y)
  have hr₀i : ∀ x, r₀ (i x) = x := fun x ↦ congr($hr₀ x)
  let r : M₂ →ₗ[k] M₁ := r₀ ∘ₗ (LinearMap.id - s ∘ₗ q)
  have hri : r ∘ₗ i = LinearMap.id := by
    ext x
    simp [r, hex.apply_apply_eq_zero, hr₀i]
  have hsplit : i ∘ₗ r + s ∘ₗ q = LinearMap.id := by
    ext x
    obtain ⟨y, hy⟩ := (hex (x - s (q x))).1 (by simp [hqs])
    have : r x = y := by simp only [r, comp_apply, sub_apply, id_apply]; rw [← hy, hr₀i]
    simp [this, hy]
  calc trace k M₂ g₂ = trace k M₂ (g₂ ∘ₗ (i ∘ₗ r + s ∘ₗ q)) := by rw [hsplit, comp_id]
    _ = trace k M₂ ((g₂ ∘ₗ i) ∘ₗ r) + trace k M₂ ((g₂ ∘ₗ s) ∘ₗ q) := by
        rw [comp_add, map_add, comp_assoc, comp_assoc]
    _ = trace k M₁ (r ∘ₗ (g₂ ∘ₗ i)) + trace k M₃ (q ∘ₗ (g₂ ∘ₗ s)) := by
        rw [trace_comp_comm' r (g₂ ∘ₗ i), trace_comp_comm' q (g₂ ∘ₗ s)]
    _ = trace k M₁ g₁ + trace k M₃ g₃ := by
        rw [h₁, ← comp_assoc, hri, id_comp, ← comp_assoc, h₃, comp_assoc, hs, comp_id]

namespace Module.End

variable {k V V₂ : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup V₂]
  [Module k V₂]

/-- An endomorphism is *finite-potent* if some power of it has finite-dimensional range
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
def IsFinitePotent (φ : Module.End k V) : Prop :=
  ∃ n : ℕ, (range (φ ^ n)).FG

lemma pow_apply_comm (φ : Module.End k V) (n : ℕ) (x : V) :
    (φ ^ n) (φ x) = φ ((φ ^ n) x) := by
  rw [← mul_apply, ← mul_apply, ← pow_succ, ← pow_succ']

lemma range_pow_le_of_le (φ : Module.End k V) {m n : ℕ} (h : n ≤ m) :
    range (φ ^ m) ≤ range (φ ^ n) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨(φ ^ (m - n)) y, ?_⟩
  rw [← mul_apply, ← pow_add, Nat.add_sub_cancel' h]

lemma mapsTo_range_pow (φ : Module.End k V) (n : ℕ) :
    ∀ x ∈ range (φ ^ n), φ x ∈ range (φ ^ n) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨φ y, pow_apply_comm φ n y⟩

lemma coe_restrict_pow (φ : Module.End k V) {U : Submodule k V} (h : ∀ x ∈ U, φ x ∈ U)
    (n : ℕ) (x : U) : (((φ.restrict h) ^ n) x : V) = (φ ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply, coe_restrict_apply, ih, pow_succ', mul_apply]

open Classical in
/-- Tate's trace of a finite-potent endomorphism: the trace of `φ` on `φ ^ n (V)` for the least
`n` making this finite-dimensional; `0` if `φ` is not finite-potent
(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
noncomputable def tateTrace (φ : Module.End k V) : k :=
  if h : φ.IsFinitePotent then trace k _ (φ.restrict (mapsTo_range_pow φ (Nat.find h))) else 0

/-- If `R ≤ U` are `φ`-stable, `U` is finite-dimensional and `φ ^ m (U) ⊆ R`, then the traces of
`φ` on `U` and on `R` agree. -/
lemma trace_restrict_eq_of_le {φ : Module.End k V} {R U : Submodule k V} (hRU : R ≤ U)
    (hU : U.FG) (hφR : ∀ x ∈ R, φ x ∈ R) (hφU : ∀ x ∈ U, φ x ∈ U) {m : ℕ}
    (hm : ∀ x ∈ U, (φ ^ m) x ∈ R) :
    trace k U (φ.restrict hφU) = trace k R (φ.restrict hφR) := by
  have : FiniteDimensional k U := (fg_iff_finiteDimensional U).1 hU
  have : FiniteDimensional k R := (fg_iff_finiteDimensional R).1 (hU.of_le hRU)
  set R' : Submodule k U := R.comap U.subtype
  set g := φ.restrict hφU
  have hR' : R' ≤ R'.comap g := fun x hx ↦ hφR _ hx
  have hex : Function.Exact (inclusion hRU) R'.mkQ := by
    intro y
    rw [mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨z, rfl⟩; exact z.2⟩
  have hinj : Function.Injective (inclusion hRU) := inclusion_injective hRU
  rw [trace_eq_add_of_exact (inclusion hRU) R'.mkQ hinj R'.mkQ_surjective hex
    (φ.restrict hφR) g (R'.mapQ R' g hR') (by ext; rfl) (by ext; rfl)]
  have hpow : ∀ n (y : U), ((R'.mapQ R' g hR') ^ n) (R'.mkQ y) = R'.mkQ ((g ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', mul_apply, ih, mkQ_apply, mapQ_apply, ← mkQ_apply, pow_succ', mul_apply]
  have hnil : IsNilpotent (R'.mapQ R' g hR') := by
    refine ⟨m, ?_⟩
    ext y
    rw [comp_apply, hpow, LinearMap.zero_comp, LinearMap.zero_apply, mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    change ((g ^ m) y : V) ∈ R
    rw [coe_restrict_pow]
    exact hm _ y.2
  rw [(isNilpotent_trace_of_isNilpotent hnil).eq_zero, add_zero]

/-- **Tate's trace via any stable subspace**: if `U` is a finite-dimensional `φ`-stable subspace
containing `φ ^ n (V)`, then `Tr_V φ` is the trace of `φ` on `U`. -/
theorem tateTrace_eq_trace_restrict {φ : Module.End k V} {U : Submodule k V} (hU : U.FG)
    (hφU : ∀ x ∈ U, φ x ∈ U) {n : ℕ} (hn : range (φ ^ n) ≤ U) :
    φ.tateTrace = trace k U (φ.restrict hφU) := by
  classical
  have hfp : φ.IsFinitePotent := ⟨n, hU.of_le hn⟩
  rw [tateTrace, dite_eq_left hfp]
  set N := Nat.find hfp
  have hN : (range (φ ^ N)).FG := Nat.find_spec hfp
  set m := max n N
  have hm : ∀ (W : Submodule k V), ∀ x ∈ W, (φ ^ m) x ∈ range (φ ^ m) := fun _ x _ ↦ ⟨x, rfl⟩
  rw [trace_restrict_eq_of_le (φ.range_pow_le_of_le (le_max_right n N)) hN
      (φ.mapsTo_range_pow m) _ (hm _),
    trace_restrict_eq_of_le ((φ.range_pow_le_of_le (le_max_left n N)).trans hn) hU
      (φ.mapsTo_range_pow m) _ (hm _)]

lemma IsFinitePotent.of_range_le {φ : Module.End k V} {U : Submodule k V} (hU : U.FG) {n : ℕ}
    (hn : range (φ ^ n) ≤ U) : φ.IsFinitePotent :=
  ⟨n, hU.of_le hn⟩

/-- On a finite-dimensional space, Tate's trace is the usual trace. -/
theorem tateTrace_eq_trace [FiniteDimensional k V] (φ : Module.End k V) :
    φ.tateTrace = trace k V φ := by
  rw [tateTrace_eq_trace_restrict (U := ⊤) (Module.finite_def.1 inferInstance)
    (fun _ _ ↦ trivial) (n := 0) le_top, trace_restrict_eq_of_forall_mem]

lemma trace_restrict_bot (φ : Module.End k V) (h : ∀ x ∈ (⊥ : Submodule k V), φ x ∈ ⊥) :
    trace k (⊥ : Submodule k V) (φ.restrict h) = 0 := by
  have : φ.restrict h = 0 := LinearMap.ext fun x ↦ Subsingleton.elim _ _
  rw [this, map_zero]

/-- **(T2)** The trace of a nilpotent endomorphism vanishes. -/
theorem tateTrace_eq_zero_of_pow_eq_zero {φ : Module.End k V} {n : ℕ} (h : φ ^ n = 0) :
    φ.tateTrace = 0 := by
  have hφ : ∀ x ∈ (⊥ : Submodule k V), φ x ∈ ⊥ := fun x hx ↦ by
    rw [(Submodule.mem_bot k).1 hx, map_zero]; exact (⊥ : Submodule k V).zero_mem
  rw [tateTrace_eq_trace_restrict fg_bot hφ (n := n) (by simp [h]), trace_restrict_bot]

@[simp]
theorem tateTrace_zero : (0 : Module.End k V).tateTrace = 0 :=
  tateTrace_eq_zero_of_pow_eq_zero (n := 1) (by simp)

theorem tateTrace_smul (c : k) (φ : Module.End k V) :
    (c • φ).tateTrace = c * φ.tateTrace := by
  by_cases hφ : φ.IsFinitePotent
  · obtain ⟨n, hn⟩ := hφ
    have hst := φ.mapsTo_range_pow n
    have hst' : ∀ x ∈ range (φ ^ n), (c • φ) x ∈ range (φ ^ n) := fun x hx ↦
      smul_mem _ c (hst x hx)
    have hle : range ((c • φ) ^ n) ≤ range (φ ^ n) := by
      rintro _ ⟨y, rfl⟩
      exact ⟨c ^ n • y, by rw [smul_pow, LinearMap.smul_apply, map_smul]⟩
    rw [tateTrace_eq_trace_restrict hn hst' hle, tateTrace_eq_trace_restrict hn hst le_rfl,
      ← smul_eq_mul, ← map_smul]
    rfl
  · by_cases hc : c = 0
    · simp [hc]
    have : ¬ (c • φ).IsFinitePotent := by
      rintro ⟨n, hn⟩
      refine hφ ⟨n, hn.of_le ?_⟩
      rintro _ ⟨y, rfl⟩
      refine ⟨(c⁻¹) ^ n • y, ?_⟩
      rw [smul_pow, LinearMap.smul_apply, map_smul, smul_smul, ← mul_pow, mul_inv_cancel₀ hc,
        one_pow, one_smul]
    rw [tateTrace, dite_eq_right this, tateTrace, dite_eq_right hφ, mul_zero]

theorem tateTrace_neg (φ : Module.End k V) : (-φ).tateTrace = -φ.tateTrace := by
  rw [← neg_one_smul k φ, tateTrace_smul, neg_one_mul]

/-- **(T3)** Tate's trace is additive on a finite family of endomorphisms whose pairwise products
have finite-dimensional range. -/
theorem tateTrace_sum {ι : Type*} (s : Finset ι) (φ : ι → Module.End k V)
    (h : ∀ i ∈ s, ∀ j ∈ s, (range (φ i * φ j)).FG) :
    (∑ i ∈ s, φ i).tateTrace = ∑ i ∈ s, (φ i).tateTrace := by
  set W : Submodule k V := ⨆ i ∈ s, ⨆ j ∈ s, range (φ i * φ j)
  have hW : W.FG := fg_biSup s _ fun i hi ↦ fg_biSup s _ fun j hj ↦ h i hi j hj
  have hle : ∀ i ∈ s, ∀ j ∈ s, range (φ i * φ j) ≤ W := fun i hi j hj ↦
    le_iSup₂_of_le i hi (le_iSup₂_of_le j hj le_rfl)
  have hst : ∀ l ∈ s, ∀ x ∈ W, φ l x ∈ W := by
    intro l hl
    suffices W ≤ W.comap (φ l) from fun x hx ↦ this hx
    refine iSup₂_le fun i hi ↦ iSup₂_le fun j hj ↦ ?_
    rintro _ ⟨y, rfl⟩
    exact hle l hl i hi ⟨φ j y, rfl⟩
  have hsum : ∀ x ∈ W, (∑ i ∈ s, φ i) x ∈ W := fun x hx ↦ by
    rw [LinearMap.sum_apply]
    exact sum_mem fun i hi ↦ hst i hi x hx
  obtain ⟨ρ, hρ⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  have hres : ∀ (ψ : Module.End k V) (hψ : ∀ x ∈ W, ψ x ∈ W),
      ψ.restrict hψ = ρ ∘ₗ ψ ∘ₗ W.subtype := by
    intro ψ hψ
    ext x
    have := congr($hρ ⟨ψ x, hψ x x.2⟩)
    simp only [comp_apply, subtype_apply, id_apply] at this
    simp [this]
  have hsq : range ((∑ i ∈ s, φ i) ^ 2) ≤ W := by
    rintro _ ⟨y, rfl⟩
    rw [sq, Finset.sum_mul_sum, LinearMap.sum_apply]
    refine sum_mem fun i hi ↦ ?_
    rw [LinearMap.sum_apply]
    exact sum_mem fun j hj ↦ hle i hi j hj ⟨y, rfl⟩
  have hsplit : ρ ∘ₗ (∑ i ∈ s, φ i) ∘ₗ W.subtype = ∑ i ∈ s, ρ ∘ₗ φ i ∘ₗ W.subtype := by
    ext x
    simp [LinearMap.sum_apply]
  rw [tateTrace_eq_trace_restrict hW hsum hsq, hres, hsplit, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [tateTrace_eq_trace_restrict hW (hst i hi) (n := 2) (by rw [sq]; exact hle i hi i hi),
    hres]

/-- Additivity of Tate's trace for two endomorphisms whose products have finite-dimensional
range. -/
theorem tateTrace_add {φ ψ : Module.End k V} (h₁ : (range (φ * φ)).FG)
    (h₂ : (range (φ * ψ)).FG) (h₃ : (range (ψ * φ)).FG) (h₄ : (range (ψ * ψ)).FG) :
    (φ + ψ).tateTrace = φ.tateTrace + ψ.tateTrace := by
  have := tateTrace_sum Finset.univ (fun b : Bool ↦ if b then φ else ψ)
    (by intro i _ j _; cases i <;> cases j <;> simpa)
  simpa [add_comm] using this

lemma pow_succ_comp (a : V →ₗ[k] V₂) (b : V₂ →ₗ[k] V) (n : ℕ) (x : V₂) :
    (((a ∘ₗ b : Module.End k V₂)) ^ (n + 1)) x = a (((b ∘ₗ a : Module.End k V) ^ n) (b x)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply, ih, pow_succ' (b ∘ₗ a), mul_apply]; rfl

/-- `Tr (b ∘ a) = Tr (a ∘ b)` when `b ∘ a` is finite-potent. -/
theorem tateTrace_comp_comm (a : V →ₗ[k] V₂) (b : V₂ →ₗ[k] V)
    (h : IsFinitePotent (b ∘ₗ a : Module.End k V)) :
    tateTrace (b ∘ₗ a : Module.End k V) = tateTrace (a ∘ₗ b : Module.End k V₂) := by
  obtain ⟨n, hn⟩ := h
  set W := range ((b ∘ₗ a : Module.End k V) ^ n)
  have hst := Module.End.mapsTo_range_pow (b ∘ₗ a) n
  set W₂ := W.map a
  have ha : ∀ x ∈ W, a x ∈ W₂ := fun x hx ↦ mem_map_of_mem hx
  have hb : ∀ y ∈ W₂, b y ∈ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hst x hx
  have hst₂ : ∀ y ∈ W₂, (a ∘ₗ b) y ∈ W₂ := fun y hy ↦ ha _ (hb y hy)
  have hle : range ((a ∘ₗ b : Module.End k V₂) ^ (n + 1)) ≤ W₂ := by
    rintro _ ⟨y, rfl⟩
    rw [pow_succ_comp]
    exact ha _ ⟨b y, rfl⟩
  have : FiniteDimensional k W := (fg_iff_finiteDimensional W).1 hn
  have : FiniteDimensional k W₂ := (fg_iff_finiteDimensional W₂).1 (hn.map a)
  rw [tateTrace_eq_trace_restrict hn hst le_rfl, tateTrace_eq_trace_restrict (hn.map a) hst₂ hle]
  have e₁ : (b ∘ₗ a).restrict hst = b.restrict hb ∘ₗ a.restrict ha := by ext; rfl
  have e₂ : (a ∘ₗ b).restrict hst₂ = a.restrict ha ∘ₗ b.restrict hb := by ext; rfl
  rw [e₁, e₂, trace_comp_comm']

lemma pow_comp_eq_comp_pow {V₁ : Type*} [AddCommGroup V₁] [Module k V₁] {i : V₁ →ₗ[k] V}
    {φ₁ : Module.End k V₁} {φ : Module.End k V} (h : φ ∘ₗ i = i ∘ₗ φ₁) (n : ℕ) (x : V₁) :
    (φ ^ n) (i x) = i ((φ₁ ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply, ih, pow_succ', mul_apply, ← comp_apply, h, comp_apply]

/-- **(T1)** Additivity of Tate's trace in a short exact sequence `0 → V₁ → V → V₃ → 0` of
spaces with compatible endomorphisms, `φ` finite-potent. -/
theorem tateTrace_eq_add_of_exact {V₁ V₃ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₃] [Module k V₃] (i : V₁ →ₗ[k] V) (q : V →ₗ[k] V₃)
    (hi : Function.Injective i) (hq : Function.Surjective q) (hex : Function.Exact i q)
    (φ₁ : Module.End k V₁) (φ : Module.End k V) (φ₃ : Module.End k V₃)
    (h₁ : φ ∘ₗ i = i ∘ₗ φ₁) (h₃ : q ∘ₗ φ = φ₃ ∘ₗ q) (hφ : φ.IsFinitePotent) :
    φ.tateTrace = φ₁.tateTrace + φ₃.tateTrace := by
  obtain ⟨n, hn⟩ := hφ
  set W := range (φ ^ n)
  have hst := φ.mapsTo_range_pow n
  set W₁ := W.comap i
  set W₃ := W.map q
  have hW₁ : W₁.FG := fg_of_fg_map_injective i hi (hn.of_le (map_comap_le _ _))
  have hW₃ : W₃.FG := hn.map q
  have hst₁ : ∀ x ∈ W₁, φ₁ x ∈ W₁ := fun x hx ↦ by
    change i (φ₁ x) ∈ W
    rw [← comp_apply, ← h₁, comp_apply]
    exact hst _ hx
  have hq₃ : ∀ x, q (φ x) = φ₃ (q x) := fun x ↦ congr($h₃ x)
  have hst₃ : ∀ y ∈ W₃, φ₃ y ∈ W₃ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨φ x, hst x hx, hq₃ x⟩
  have hle₁ : range (φ₁ ^ n) ≤ W₁ := by
    rintro _ ⟨x, rfl⟩
    change i _ ∈ W
    rw [← pow_comp_eq_comp_pow h₁]
    exact ⟨_, rfl⟩
  have hq₃n : ∀ x, q ((φ ^ n) x) = (φ₃ ^ n) (q x) := fun x ↦
    (pow_comp_eq_comp_pow h₃.symm n x).symm
  have hle₃ : range (φ₃ ^ n) ≤ W₃ := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨(φ ^ n) x, ⟨x, rfl⟩, hq₃n x⟩
  have : FiniteDimensional k W := (fg_iff_finiteDimensional W).1 hn
  have : FiniteDimensional k W₁ := (fg_iff_finiteDimensional W₁).1 hW₁
  have : FiniteDimensional k W₃ := (fg_iff_finiteDimensional W₃).1 hW₃
  have hi' : ∀ x ∈ W₁, i x ∈ W := fun x hx ↦ hx
  have hq' : ∀ x ∈ W, q x ∈ W₃ := fun x hx ↦ mem_map_of_mem hx
  rw [tateTrace_eq_trace_restrict hn hst le_rfl, tateTrace_eq_trace_restrict hW₁ hst₁ hle₁,
    tateTrace_eq_trace_restrict hW₃ hst₃ hle₃]
  refine trace_eq_add_of_exact (i.restrict hi') (q.restrict hq') ?_ ?_ ?_ _ _ _ ?_ ?_
  · intro x y hxy
    exact Subtype.ext (hi congr(($hxy : V)))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (hex x).1 congr(($hx : V₃))
      exact ⟨⟨y, show i y ∈ W from hy ▸ x.2⟩, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext (hex.apply_apply_eq_zero (y : V₁))
  · ext x
    exact congr($h₁ x)
  · ext x
    exact hq₃ x

end Module.End

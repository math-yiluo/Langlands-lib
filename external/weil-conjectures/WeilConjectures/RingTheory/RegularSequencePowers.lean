/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Data.List.OfFn

/-!
# Positive powers of a regular sequence

Source: Stacks Project, Algebra, Lemma 10.68.9, Tag 07DV
(blueprint: lem-weil-pbc-regular-sequence-powers).
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence

open scoped Pointwise in
private theorem smul_top_pow_eq_top_iff {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (a : R) {n : ℕ} (hn : 0 < n) :
    (a ^ n) • (⊤ : Submodule R M) = ⊤ ↔ a • (⊤ : Submodule R M) = ⊤ := by
  have surj (b : R) : b • (⊤ : Submodule R M) = ⊤ ↔
      Function.Surjective (fun x : M ↦ b • x) := by
    constructor
    · intro h x
      have hx : x ∈ b • (⊤ : Submodule R M) := by rw [h]; trivial
      obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists x b ⊤).mp hx
      exact ⟨y, hy⟩
    · intro h
      apply top_unique
      intro x _
      obtain ⟨y, hy⟩ := h x
      exact (Submodule.mem_smul_pointwise_iff_exists x b ⊤).mpr ⟨y, trivial, hy⟩
  rw [surj, surj]
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h x
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact ⟨a ^ k • y, by simpa [pow_succ', mul_smul] using hy⟩
  · intro h
    have hpow : ∀ k : ℕ, Function.Surjective (fun x : M ↦ a ^ k • x) := by
      intro k
      induction k with
      | zero => intro x; exact ⟨x, by simp⟩
      | succ k ih =>
        intro x
        obtain ⟨y, hy⟩ := h x
        obtain ⟨z, hz⟩ := ih y
        exact ⟨z, by simp [pow_succ', mul_smul, hz, hy]⟩
    exact hpow n

open scoped Pointwise in
private theorem top_eq_cons_pow_smul_iff {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (a : R) (rs : List R)
    {n : ℕ} (hn : 0 < n) :
    (⊤ : Submodule R M) = Ideal.ofList (a :: rs) • ⊤ ↔
      (⊤ : Submodule R M) = Ideal.ofList (a ^ n :: rs) • ⊤ := by
  rw [eq_comm, ← Submodule.Quotient.subsingleton_iff,
    eq_comm (a := (⊤ : Submodule R M)), ← Submodule.Quotient.subsingleton_iff]
  let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter M a rs
  let e' := Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter M (a ^ n) rs
  rw [e.toEquiv.subsingleton_congr, e'.toEquiv.subsingleton_congr]
  change Subsingleton (QuotSMulTop a (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))) ↔ _
  rw [Submodule.Quotient.subsingleton_iff, Submodule.Quotient.subsingleton_iff]
  exact (smul_top_pow_eq_top_iff _ a hn).symm

open scoped Pointwise in
private theorem top_eq_ofFn_pow_smul_iff {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ}
    (f : Fin r → R) (e : Fin r → ℕ) (he : ∀ i, 0 < e i) :
    (⊤ : Submodule R M) = Ideal.ofList (List.ofFn f) • ⊤ ↔
      (⊤ : Submodule R M) = Ideal.ofList (List.ofFn (fun i ↦ f i ^ e i)) • ⊤ := by
  induction r generalizing M with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    calc
      _ ↔ (⊤ : Submodule R (QuotSMulTop (f 0) M)) =
          Ideal.ofList (List.ofFn (fun i ↦ f i.succ)) • ⊤ :=
        Submodule.top_eq_ofList_cons_smul_iff (M := M) _ _
      _ ↔ (⊤ : Submodule R (QuotSMulTop (f 0) M)) =
          Ideal.ofList (List.ofFn (fun i ↦ f i.succ ^ e i.succ)) • ⊤ :=
        ih _ _ _ (fun i ↦ he i.succ)
      _ ↔ (⊤ : Submodule R M) =
          Ideal.ofList (f 0 :: List.ofFn (fun i ↦ f i.succ ^ e i.succ)) • ⊤ :=
        (Submodule.top_eq_ofList_cons_smul_iff (M := M) _ _).symm
      _ ↔ _ := top_eq_cons_pow_smul_iff M _ _ (he 0)

open scoped Pointwise in
private theorem power_shortExact {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (a : R)
    (ha : IsSMulRegular M a) (k : ℕ) :
    ∃ (α : QuotSMulTop a M →ₗ[R] QuotSMulTop (a ^ (k + 1)) M)
      (β : QuotSMulTop (a ^ (k + 1)) M →ₗ[R] QuotSMulTop (a ^ k) M),
      Function.Injective α ∧ Function.Surjective β ∧ Function.Exact α β := by
  let P : Submodule R M := a • ⊤
  let Q : Submodule R M := a ^ (k + 1) • ⊤
  let T : Submodule R M := a ^ k • ⊤
  have hPQ : P ≤ Submodule.comap (LinearMap.lsmul R M (a ^ k)) Q := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x a ⊤).mp hx
    change a ^ k • (a • y) ∈ Q
    rw [← mul_smul, ← pow_succ]
    exact Submodule.smul_mem_pointwise_smul y _ ⊤ (Submodule.mem_top)
  have hQT : Q ≤ T := by
    intro x hx
    obtain ⟨y, _, rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists x (a ^ (k + 1)) ⊤).mp hx
    exact (Submodule.mem_smul_pointwise_iff_exists _ (a ^ k) ⊤).mpr
      ⟨a • y, trivial, by rw [← mul_smul, ← pow_succ]⟩
  let α : M ⧸ P →ₗ[R] M ⧸ Q := P.mapQ Q (LinearMap.lsmul R M (a ^ k)) hPQ
  let β : M ⧸ Q →ₗ[R] M ⧸ T := Submodule.factor hQT
  have hα : Function.Injective α := by
    apply (LinearMap.ker_eq_bot).mp
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    change Q.mkQ (a ^ k • x) = 0 at hx
    have hx' : a ^ k • x ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp hx
    obtain ⟨y, _, hy⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ (a ^ (k + 1)) ⊤).mp hx'
    have hxy : a • y = x := (ha.pow k) (by simpa [pow_succ, mul_smul] using hy)
    change P.mkQ x = 0
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    exact (Submodule.mem_smul_pointwise_iff_exists _ a ⊤).mpr ⟨y, trivial, hxy⟩
  refine ⟨α, β, hα, Submodule.factor_surjective hQT, ?_⟩
  intro x
  obtain ⟨x, rfl⟩ := Q.mkQ_surjective x
  change T.mkQ x = 0 ↔ ∃ y, α y = Q.mkQ x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists x (a ^ k) ⊤).mp hx
    exact ⟨P.mkQ y, congrArg Q.mkQ hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := P.mkQ_surjective y
    have heq : Q.mkQ (a ^ k • y) = Q.mkQ x := hy
    have hmem : a ^ k • y - x ∈ Q := (Submodule.Quotient.eq Q).mp heq
    have hmem' : a ^ k • y ∈ T :=
      Submodule.smul_mem_pointwise_smul y _ ⊤ (Submodule.mem_top)
    have := T.sub_mem hmem' (hQT hmem)
    simpa using this

open scoped Pointwise in
private theorem quotient_map_injective {R : Type u} [CommRing R]
    {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (α : A →ₗ[R] B) (β : B →ₗ[R] C)
    (hα : Function.Injective α) (hβ : Function.Surjective β)
    (hex : Function.Exact α β) (rs : List R) (hC : IsWeaklyRegular C rs) :
    Function.Injective
      (Submodule.mapQ (Ideal.ofList rs • ⊤) (Ideal.ofList rs • ⊤) α
        (Submodule.smul_top_le_comap_smul_top (Ideal.ofList rs) α)) := by
  have hzero : Function.Exact (0 : A →ₗ[R] A) α :=
    (LinearMap.exact_zero_iff_injective A α).mpr hα
  have h := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    hzero hex hβ hC
  simpa only [Submodule.mapQ_zero, LinearMap.exact_zero_iff_injective] using h

open scoped Pointwise in
private theorem weak_of_shortExact {R : Type u} [CommRing R]
    {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (α : A →ₗ[R] B) (β : B →ₗ[R] C)
    (hα : Function.Injective α) (hβ : Function.Surjective β)
    (hex : Function.Exact α β) (rs : List R)
    (hA : IsWeaklyRegular A rs) (hC : IsWeaklyRegular C rs) :
    IsWeaklyRegular B rs := by
  induction rs generalizing A B C with
  | nil => exact IsWeaklyRegular.nil R B
  | cons a rs ih =>
    rw [isWeaklyRegular_cons_iff] at hA hC ⊢
    refine ⟨isSMulRegular_of_range_eq_ker hα hex.linearMap_ker_eq.symm hA.1 hC.1, ?_⟩
    have hα' : Function.Injective (QuotSMulTop.map a α) := by
      have hzero : Function.Exact (0 : A →ₗ[R] A) α :=
        (LinearMap.exact_zero_iff_injective A α).mpr hα
      have h := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
        hzero hex hC.1
      simpa only [map_zero, LinearMap.exact_zero_iff_injective] using h
    exact ih (QuotSMulTop.map a α) (QuotSMulTop.map a β) hα'
      (QuotSMulTop.map_surjective a hβ) (QuotSMulTop.map_exact a hex hβ) hA.2 hC.2

open scoped Pointwise in
private theorem weak_quot_pow {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (a : R)
    (ha : IsSMulRegular M a) (rs : List R) {n : ℕ} (hn : 0 < n)
    (h : IsWeaklyRegular (QuotSMulTop a M) rs) :
    IsWeaklyRegular (QuotSMulTop (a ^ n) M) rs := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  clear hn
  induction k with
  | zero =>
    change IsWeaklyRegular (QuotSMulTop (a ^ 1) M) rs
    rw [pow_one]
    exact h
  | succ k ih =>
    obtain ⟨α, β, hα, hβ, hex⟩ := power_shortExact M a ha (k + 1)
    exact weak_of_shortExact α β hα hβ hex rs h ih

open scoped Pointwise in
private theorem weak_quot_of_pow {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (a : R)
    (ha : IsSMulRegular M a) (rs : List R) {n : ℕ} (hn : 0 < n)
    (h : IsWeaklyRegular (QuotSMulTop (a ^ n) M) rs) :
    IsWeaklyRegular (QuotSMulTop a M) rs := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  cases k with
  | zero =>
    change IsWeaklyRegular (QuotSMulTop (a ^ 1) M) rs at h
    rw [pow_one] at h
    exact h
  | succ k =>
    let A := QuotSMulTop a M
    let B := QuotSMulTop (a ^ (k + 1 + 1)) M
    let C := QuotSMulTop (a ^ (k + 1)) M
    obtain ⟨α, β, hα, hβ, hex⟩ := power_shortExact M a ha (k + 1)
    apply (isWeaklyRegular_iff A rs).mpr
    intro i hi
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have hA : IsWeaklyRegular A (rs.take i) := by
        constructor
        intro j hj
        have hji : j < i := lt_of_lt_of_le hj (List.length_take_le i rs)
        have hjrs : j < rs.length := lt_trans hji hi
        rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hji)]
        simpa only [List.getElem_take] using ih j hji hjrs
      have hC : IsWeaklyRegular C (rs.take i) :=
        weak_quot_pow M a ha (rs.take i) (Nat.succ_pos k) hA
      let αi := Submodule.mapQ (Ideal.ofList (rs.take i) • ⊤)
        (Ideal.ofList (rs.take i) • ⊤) α
        (Submodule.smul_top_le_comap_smul_top (Ideal.ofList (rs.take i)) α)
      have hαi : Function.Injective αi :=
        quotient_map_injective α β hα hβ hex (rs.take i) hC
      exact (h.regular_mod_prev i hi).of_injective αi hαi

open scoped Pointwise in
private theorem weak_ofFn_pow_iff {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ}
    (f : Fin r → R) (e : Fin r → ℕ) (he : ∀ i, 0 < e i) :
    IsWeaklyRegular M (List.ofFn f) ↔
      IsWeaklyRegular M (List.ofFn (fun i ↦ f i ^ e i)) := by
  induction r generalizing M with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.ofFn_succ, isWeaklyRegular_cons_iff,
      isWeaklyRegular_cons_iff]
    constructor
    · rintro ⟨hf, ht⟩
      refine ⟨hf.pow _, ?_⟩
      exact weak_quot_pow M (f 0) hf _ (he 0)
        ((ih _ _ _ (fun i ↦ he i.succ)).mp ht)
    · rintro ⟨hf, ht⟩
      have hf' := (IsSMulRegular.pow_iff (he 0)).mp hf
      refine ⟨hf', ?_⟩
      exact (ih _ _ _ (fun i ↦ he i.succ)).mpr
        (weak_quot_of_pow M (f 0) hf' _ (he 0) ht)

/-- Taking a positive power of each term preserves and reflects regularity on any module.
Source: Stacks Project, Algebra, Lemma 10.68.9, Tag 07DV
(blueprint: lem-weil-pbc-regular-sequence-powers).

Proof (following Stacks Tag 07DV, with the omitted details made explicit).
1. Separate weak regularity from nonvanishing using `isRegular_iff`, and use
`isWeaklyRegular_cons_iff` to pass to the tail on the quotient by the first term.
2. `IsSMulRegular.pow_iff` identifies injectivity of a term with that of its positive
power. Construct the maps in `0 -> N/fN -> N/f^(k+1)N -> N/f^kN -> 0` using `mapQ`
and `factor`. The first map multiplies by `f^k`; cancel this power to prove injectivity.
A representative computation identifies its image with the projection's kernel.
3. For nonvanishing, quotient first by the ideal of the tail. The final quotient is
zero iff multiplication by the first term on this module is surjective. A map is
surjective iff its positive iterate is surjective. Induct on the sequence length,
using the two orders of iterated quotients, to power every term.
4. Weak regularity ascends a short exact sequence: induct on the list, using
`isSMulRegular_of_range_eq_ker` for the head. The right head is regular, so
`QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last` preserves
injectivity of the left map; `map_exact` and `map_surjective` give the remaining
properties of the quotient row. Apply the list induction to that row. Then induct
on the exponent in the row from step 2 to transport a weakly regular tail from
`N/fN` to `N/f^eN`.
5. For reflection, strongly induct on the position in the tail. The preceding
positions are weakly regular on `A = N/fN` and hence, by step 4, on `C = N/f^(e-1)N`.
Mathlib's `map_first_exact_on_four_term_right_exact_of_isSMulRegular_last`, applied
to `0 -> A -> B -> C -> 0`, makes `A/K_iA -> B/K_iB` injective. Transfer injectivity
of the next tail term on `B/K_iB` to `A/K_iA`. The case `e = 1` is immediate.
6. Induct on sequence length to power the tail on `M/f_1M`, and then apply steps
4 and 5 to power the first term. Combine weak regularity with step 3. -/
theorem isRegular_ofFn_pow_iff {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ}
    (f : Fin r → R) (e : Fin r → ℕ) (he : ∀ i : Fin r, 0 < e i) :
    IsRegular M (List.ofFn f) ↔ IsRegular M (List.ofFn (fun i ↦ f i ^ e i)) := by
  rw [isRegular_iff, isRegular_iff]
  exact and_congr (weak_ofFn_pow_iff M f e he)
    (not_congr (top_eq_ofFn_pow_smul_iff M f e he))

end RingTheory.Sequence

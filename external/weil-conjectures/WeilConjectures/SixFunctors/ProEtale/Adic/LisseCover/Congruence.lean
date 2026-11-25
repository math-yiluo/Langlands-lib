/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Congruence subgroups of `GL_n(E)` for a finite extension `E` of `ℚ_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`, with the restriction of the (ultrametric)
norm of `ℚ̄_ℓ`. For `k : ℕ` the *congruence subgroup*
`PadicAlgCl.congruenceSubgroup E n k ⊆ GL_n(E)` consists of the matrices `A` such that all
entries of `A - 1` and of `A⁻¹ - 1` have norm at most `ℓ⁻ᵏ`; for `k = 0` this is `GL_n(𝒪_E)`.
These subgroups have the properties used to trivialise a continuous `GL_n(E)`-valued cocycle as a
limit of finite-level trivialisations
(`CocycleTrivialization.exists_cocycle_trivialization`):

* only finitely many cosets of the `k`-th congruence subgroup meet `GL_n(𝒪_E)`, `𝒪_E` being
  compact (`PadicAlgCl.finite_image_congruenceSubgroup_zero`);
* `GL_n(E)` is complete and separated for them, `E` being complete
  (`PadicAlgCl.exists_limit_congruenceSubgroup`,
  `PadicAlgCl.eq_one_of_forall_mem_congruenceSubgroup`);
* for a function `γ : Z → GL_n(E)` with continuous entries, `z ↦ γ z • q` is locally constant on
  every coset space `GL_n(E) ⧸ K_k` (`PadicAlgCl.isLocallyConstant_smul_mk`), and conversely a
  function `σ : X → GL_n(E)` all of whose reductions are locally constant has continuous entries
  (`PadicAlgCl.continuous_apply_of_isLocallyConstant_mk`).
-/

@[expose] public section

open Filter Topology

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l)) {n : ℕ}

section Bounds

variable {E}

/-- All entries of the matrix `M` have norm at most `r`. -/
def EntryBound (M : Matrix (Fin n) (Fin n) E) (r : ℝ) : Prop :=
  ∀ i j, ‖M i j‖ ≤ r

lemma EntryBound.mono {M : Matrix (Fin n) (Fin n) E} {r s : ℝ} (h : EntryBound M r)
    (hrs : r ≤ s) : EntryBound M s :=
  fun i j ↦ (h i j).trans hrs

lemma EntryBound.add {M N : Matrix (Fin n) (Fin n) E} {r : ℝ} (hM : EntryBound M r)
    (hN : EntryBound N r) : EntryBound (M + N) r :=
  fun i j ↦ (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (hN i j))

lemma EntryBound.neg {M : Matrix (Fin n) (Fin n) E} {r : ℝ} (hM : EntryBound M r) :
    EntryBound (-M) r :=
  fun i j ↦ by simpa using hM i j

lemma EntryBound.sub {M N : Matrix (Fin n) (Fin n) E} {r : ℝ} (hM : EntryBound M r)
    (hN : EntryBound N r) : EntryBound (M - N) r := by
  rw [sub_eq_add_neg]
  exact hM.add hN.neg

lemma EntryBound.mul {M N : Matrix (Fin n) (Fin n) E} {r s : ℝ} (hM : EntryBound M r)
    (hN : EntryBound N s) (hr : 0 ≤ r) (hs : 0 ≤ s) : EntryBound (M * N) (r * s) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun m _ ↦ ?_
  rw [norm_mul]
  exact mul_le_mul (hM i m) (hN m j) (norm_nonneg _) hr

lemma entryBound_one : EntryBound (1 : Matrix (Fin n) (Fin n) E) 1 := by
  intro i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

/-- A bound for all entries of a matrix: the sum of the norms of the entries. -/
noncomputable def entrySum (M : Matrix (Fin n) (Fin n) E) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖

lemma entrySum_nonneg (M : Matrix (Fin n) (Fin n) E) : 0 ≤ entrySum M :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

lemma entryBound_entrySum (M : Matrix (Fin n) (Fin n) E) : EntryBound M (entrySum M) := by
  intro i j
  refine le_trans ?_ (Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    norm_nonneg (M i j)) (Finset.mem_univ i))
  exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (M i j)) (Finset.mem_univ j)

end Bounds

variable (l) in
/-- The radius `ℓ⁻ᵏ` of the `k`-th congruence subgroup. -/
noncomputable def congruenceRadius (k : ℕ) : ℝ := ((l : ℝ)⁻¹) ^ k

omit [Fact l.Prime] in
lemma congruenceRadius_nonneg (k : ℕ) : 0 ≤ congruenceRadius l k :=
  pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _

lemma congruenceRadius_pos (k : ℕ) : 0 < congruenceRadius l k :=
  pow_pos (inv_pos.2 (Nat.cast_pos.2 (Fact.out : l.Prime).pos)) _

lemma inv_l_lt_one : ((l : ℝ)⁻¹) < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

lemma congruenceRadius_le_one (k : ℕ) : congruenceRadius l k ≤ 1 :=
  pow_le_one₀ (inv_nonneg.2 (Nat.cast_nonneg _)) inv_l_lt_one.le

lemma congruenceRadius_antitone {k k' : ℕ} (h : k ≤ k') :
    congruenceRadius l k' ≤ congruenceRadius l k :=
  pow_le_pow_of_le_one (inv_nonneg.2 (Nat.cast_nonneg _)) inv_l_lt_one.le h

lemma exists_congruenceRadius_lt {ε : ℝ} (hε : 0 < ε) : ∃ k, congruenceRadius l k < ε :=
  exists_pow_lt_of_lt_one hε inv_l_lt_one

variable (n) in
/-- The `k`-th congruence subgroup of `GL_n(E)`: the matrices `A` all of whose entries of
`A - 1` and of `A⁻¹ - 1` have norm at most `ℓ⁻ᵏ`. For `k = 0` it is `GL_n(𝒪_E)`. -/
noncomputable def congruenceSubgroup (k : ℕ) : Subgroup (GL (Fin n) E) where
  carrier := {A | EntryBound ((A : Matrix (Fin n) (Fin n) E) - 1) (congruenceRadius l k) ∧
    EntryBound (((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) (congruenceRadius l k)}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inv_one, Units.val_one, sub_self, and_self]
    exact fun _ _ ↦ by simpa using congruenceRadius_nonneg k
  mul_mem' {A B} hA hB := by
    have key {M N : Matrix (Fin n) (Fin n) E} (hM : EntryBound (M - 1) (congruenceRadius l k))
        (hN : EntryBound (N - 1) (congruenceRadius l k)) :
        EntryBound (M * N - 1) (congruenceRadius l k) := by
      have : M * N - 1 = (M - 1) * (N - 1) + (M - 1) + (N - 1) := by noncomm_ring
      rw [this]
      refine (((hM.mul hN (congruenceRadius_nonneg k) (congruenceRadius_nonneg k)).mono ?_).add
        hM).add hN
      exact mul_le_of_le_one_left (congruenceRadius_nonneg k) (congruenceRadius_le_one k)
    refine ⟨key hA.1 hB.1, ?_⟩
    rw [mul_inv_rev, Units.val_mul]
    exact key hB.2 hA.2
  inv_mem' {A} hA := ⟨hA.2, by simpa using hA.1⟩

variable {E}

lemma mem_congruenceSubgroup {k : ℕ} {A : GL (Fin n) E} :
    A ∈ congruenceSubgroup E n k ↔
      EntryBound ((A : Matrix (Fin n) (Fin n) E) - 1) (congruenceRadius l k) ∧
      EntryBound (((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1)
        (congruenceRadius l k) :=
  Iff.rfl

lemma congruenceSubgroup_antitone {k k' : ℕ} (h : k ≤ k') :
    congruenceSubgroup E n k' ≤ congruenceSubgroup E n k :=
  fun _ hA ↦ ⟨hA.1.mono (congruenceRadius_antitone h), hA.2.mono (congruenceRadius_antitone h)⟩

lemma entryBound_of_mem_congruenceSubgroup_zero {A : GL (Fin n) E}
    (hA : A ∈ congruenceSubgroup E n 0) : EntryBound (A : Matrix (Fin n) (Fin n) E) 1 := by
  have h := hA.1.add (entryBound_one (E := E) (n := n))
  simpa [congruenceRadius] using h

lemma entryBound_inv_of_mem_congruenceSubgroup_zero {A : GL (Fin n) E}
    (hA : A ∈ congruenceSubgroup E n 0) :
    EntryBound ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) 1 :=
  entryBound_of_mem_congruenceSubgroup_zero ((congruenceSubgroup E n 0).inv_mem hA)

/-- If `A, B ∈ GL_n(𝒪_E)` have entries at distance at most `ℓ⁻ᵏ`, then `A⁻¹ B` lies in the
`k`-th congruence subgroup. -/
lemma inv_mul_mem_congruenceSubgroup {k : ℕ} {A B : GL (Fin n) E}
    (hA : A ∈ congruenceSubgroup E n 0) (hB : B ∈ congruenceSubgroup E n 0)
    (h : EntryBound ((B : Matrix (Fin n) (Fin n) E) - (A : Matrix (Fin n) (Fin n) E))
      (congruenceRadius l k)) :
    A⁻¹ * B ∈ congruenceSubgroup E n k := by
  have e₁ : ((A⁻¹ * B : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
      ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((B : Matrix _ _ E) - (A : Matrix _ _ E)) := by
    rw [mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e₂ : (((A⁻¹ * B)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
      ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((A : Matrix _ _ E) - (B : Matrix _ _ E)) := by
    rw [mul_inv_rev, inv_inv, mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [e₁]
    simpa using (entryBound_inv_of_mem_congruenceSubgroup_zero hA).mul h zero_le_one
      (congruenceRadius_nonneg k)
  · rw [e₂]
    have h' : EntryBound ((A : Matrix (Fin n) (Fin n) E) - (B : Matrix (Fin n) (Fin n) E))
        (congruenceRadius l k) := by
      simpa [neg_sub] using h.neg
    simpa using (entryBound_inv_of_mem_congruenceSubgroup_zero hB).mul h' zero_le_one
      (congruenceRadius_nonneg k)

/-- **Separation.** The congruence subgroups intersect in the identity. -/
lemma eq_one_of_forall_mem_congruenceSubgroup {A : GL (Fin n) E}
    (h : ∀ k, A ∈ congruenceSubgroup E n k) : A = 1 := by
  refine Units.ext (Matrix.ext fun i j ↦ ?_)
  by_contra hne
  have hε : 0 < ‖(A : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := exists_congruenceRadius_lt (l := l) hε
  exact absurd ((h k).1 i j) (not_le.2 (by simpa using hk))

variable [FiniteDimensional ℚ_[l] E]

/-- **Finiteness.** Only finitely many cosets of the `k`-th congruence subgroup meet
`GL_n(𝒪_E)`: the closed unit ball of `E` is compact, hence covered by finitely many balls of
radius `ℓ⁻ᵏ`, and matrices in `GL_n(𝒪_E)` whose entries lie in the same balls are congruent. -/
lemma finite_image_congruenceSubgroup_zero (k : ℕ) :
    (QuotientGroup.mk '' (congruenceSubgroup E n 0 : Set (GL (Fin n) E)) :
      Set (GL (Fin n) E ⧸ congruenceSubgroup E n k)).Finite := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : E) 1)
    (congruenceRadius_pos (l := l) k)
  have : Finite t := ht.to_subtype
  -- a choice of centres of balls containing the entries
  have hc (x : E) (hx : ‖x‖ ≤ 1) : ∃ c : t, ‖x - c‖ < congruenceRadius l k := by
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (hcov (mem_closedBall_zero_iff.2 hx))
    exact ⟨⟨c, hc⟩, by simpa [dist_eq_norm] using hxc⟩
  have hne : Nonempty t := by
    obtain ⟨c, hc', -⟩ := Set.mem_iUnion₂.1 (hcov (Metric.mem_closedBall_self zero_le_one))
    exact ⟨⟨c, hc'⟩⟩
  let pat (A : GL (Fin n) E) : Fin n → Fin n → t := fun i j ↦
    if h : ‖(A : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 then (hc _ h).choose else
      Classical.arbitrary t
  let rep (p : Fin n → Fin n → t) : GL (Fin n) E ⧸ congruenceSubgroup E n k :=
    if h : ∃ A ∈ congruenceSubgroup E n 0, pat A = p then ((h.choose : GL (Fin n) E) : _)
    else (1 : GL (Fin n) E)
  refine (Set.finite_range rep).subset ?_
  rintro _ ⟨A, hA, rfl⟩
  refine ⟨pat A, ?_⟩
  have h : ∃ B ∈ congruenceSubgroup E n 0, pat B = pat A := ⟨A, hA, rfl⟩
  simp only [rep, dite_eq_left h]
  obtain ⟨hB, hpat⟩ := h.choose_spec
  set B := h.choose
  refine (QuotientGroup.eq.2 (inv_mul_mem_congruenceSubgroup hB hA fun i j ↦ ?_))
  have hAij := entryBound_of_mem_congruenceSubgroup_zero hA i j
  have hBij := entryBound_of_mem_congruenceSubgroup_zero hB i j
  have e : pat B i j = pat A i j := by rw [hpat]
  simp only [pat, dite_eq_left hAij, dite_eq_left hBij] at e
  have h₁ := (hc _ hAij).choose_spec
  have h₂ := (hc _ hBij).choose_spec
  rw [e] at h₂
  have : (A : Matrix (Fin n) (Fin n) E) i j - (B : Matrix (Fin n) (Fin n) E) i j =
      ((A : Matrix (Fin n) (Fin n) E) i j - (hc _ hAij).choose) -
        ((B : Matrix (Fin n) (Fin n) E) i j - (hc _ hAij).choose) := by ring
  rw [Matrix.sub_apply, this, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h₁.le (by rw [norm_neg]; exact h₂.le))

omit [FiniteDimensional ℚ_[l] E] in
/-- A limit of matrices with entries bounded by `r` has entries bounded by `r`. -/
lemma EntryBound.of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    {M : ι → Matrix (Fin n) (Fin n) E} {N : Matrix (Fin n) (Fin n) E}
    (hM : ∀ i j, Tendsto (fun m ↦ M m i j) F (𝓝 (N i j))) {r : ℝ}
    (hr : ∀ᶠ m in F, EntryBound (M m) r) : EntryBound N r := fun i j ↦
  le_of_tendsto ((continuous_norm.tendsto _).comp (hM i j)) (hr.mono fun _ h ↦ h i j)

omit [FiniteDimensional ℚ_[l] E] in
/-- Entrywise limits of matrices are compatible with multiplication. -/
lemma tendsto_mul_apply {ι : Type*} {F : Filter ι} {M M' : ι → Matrix (Fin n) (Fin n) E}
    {N N' : Matrix (Fin n) (Fin n) E} (hM : ∀ i j, Tendsto (fun m ↦ M m i j) F (𝓝 (N i j)))
    (hM' : ∀ i j, Tendsto (fun m ↦ M' m i j) F (𝓝 (N' i j))) (i j : Fin n) :
    Tendsto (fun m ↦ (M m * M' m) i j) F (𝓝 ((N * N') i j)) := by
  simp only [Matrix.mul_apply]
  exact tendsto_finsetSum _ fun k _ ↦ (hM i k).mul (hM' k j)

/-- **Completeness.** A sequence `bₖ` in `GL_n(E)` with `bₖ⁻¹ bₖ₊₁` in the `k`-th congruence
subgroup has a limit `c` with `bₖ⁻¹ c` in the `k`-th congruence subgroup for all `k`. -/
lemma exists_limit_congruenceSubgroup (b : ℕ → GL (Fin n) E)
    (hb : ∀ k, (b k)⁻¹ * b (k + 1) ∈ congruenceSubgroup E n k) :
    ∃ c, ∀ k, (b k)⁻¹ * c ∈ congruenceSubgroup E n k := by
  have : CompleteSpace E := FiniteDimensional.complete ℚ_[l] E
  -- the partial products
  have hmem {k m : ℕ} (h : k ≤ m) : (b k)⁻¹ * b m ∈ congruenceSubgroup E n k := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have := (congruenceSubgroup E n k).mul_mem ih (congruenceSubgroup_antitone hkm (hb m))
      simpa [mul_assoc] using this
  let B (k : ℕ) : Matrix (Fin n) (Fin n) E := b k
  let B' (k : ℕ) : Matrix (Fin n) (Fin n) E := ((b k)⁻¹ : GL (Fin n) E)
  have hB (k : ℕ) : EntryBound (B k) (entrySum (B 0)) := by
    have e : B k = B 0 * (((b 0)⁻¹ * b k : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
      simp [B]
    rw [e]
    simpa using (entryBound_entrySum (B 0)).mul
      (entryBound_of_mem_congruenceSubgroup_zero (hmem (Nat.zero_le k)))
      (entrySum_nonneg _) zero_le_one
  have hB' (k : ℕ) : EntryBound (B' k) (entrySum (B' 0)) := by
    have e : B' k = ((((b 0)⁻¹ * b k)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * B' 0 := by
      simp [B']
    rw [e]
    simpa using (entryBound_inv_of_mem_congruenceSubgroup_zero
      (hmem (Nat.zero_le k))).mul (entryBound_entrySum (B' 0)) zero_le_one (entrySum_nonneg _)
  -- the successive differences are geometrically small
  have hd (k : ℕ) : EntryBound (B (k + 1) - B k) (entrySum (B 0) * congruenceRadius l k) := by
    have e : B (k + 1) - B k =
        B k * ((((b k)⁻¹ * b (k + 1) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) := by
      simp [B, mul_sub]
    rw [e]
    exact (hB k).mul (hb k).1 (entrySum_nonneg _) (congruenceRadius_nonneg k)
  have hd' (k : ℕ) : EntryBound (B' (k + 1) - B' k) (congruenceRadius l k * entrySum (B' 0)) := by
    have e : B' (k + 1) - B' k =
        (((((b k)⁻¹ * b (k + 1))⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) * B' k := by
      simp [B', sub_mul]
    rw [e]
    exact (hb k).2.mul (hB' k) (congruenceRadius_nonneg k) (entrySum_nonneg _)
  have hcauchy (M : ℕ → Matrix (Fin n) (Fin n) E) (C : ℝ)
      (hM : ∀ k, EntryBound (M (k + 1) - M k) (C * congruenceRadius l k)) (i j : Fin n) :
      ∃ a, Tendsto (fun k ↦ M k i j) atTop (𝓝 a) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ C inv_l_lt_one fun k ↦ by
      rw [dist_comm, dist_eq_norm]
      exact hM k i j)
  choose c hc using hcauchy B _ hd
  choose c' hc' using hcauchy B' _ fun k ↦ by rw [mul_comm]; exact hd' k
  let C : Matrix (Fin n) (Fin n) E := Matrix.of c
  let C' : Matrix (Fin n) (Fin n) E := Matrix.of c'
  have hBB' (k : ℕ) : B k * B' k = 1 := by simp [B, B']
  have hB'B (k : ℕ) : B' k * B k = 1 := by simp [B, B']
  have h₁ : C * C' = 1 := Matrix.ext fun i j ↦ tendsto_nhds_unique
    (tendsto_mul_apply (N := C) (N' := C') hc hc' i j) (by simp only [hBB']; exact
      tendsto_const_nhds)
  have h₂ : C' * C = 1 := Matrix.ext fun i j ↦ tendsto_nhds_unique
    (tendsto_mul_apply (N := C') (N' := C) hc' hc i j) (by simp only [hB'B]; exact
      tendsto_const_nhds)
  refine ⟨⟨C, C', h₁, h₂⟩, fun k ↦ ⟨?_, ?_⟩⟩
  · -- `bₖ⁻¹ c - 1` is the limit of `bₖ⁻¹ bₘ - 1`
    have e : (((b k)⁻¹ * ⟨C, C', h₁, h₂⟩ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        B' k * C := rfl
    rw [e]
    refine EntryBound.of_tendsto (F := atTop) (M := fun m ↦ B' k * B m - 1) (fun i j ↦ ?_)
      ((eventually_ge_atTop k).mono fun m hm ↦ by simpa [B, B'] using (hmem hm).1)
    have := tendsto_mul_apply (M := fun _ ↦ B' k) (N := B' k) (N' := C)
      (fun _ _ ↦ tendsto_const_nhds) hc i j
    simpa using this.sub (tendsto_const_nhds (x := (1 : Matrix (Fin n) (Fin n) E) i j))
  · have e : ((((b k)⁻¹ * ⟨C, C', h₁, h₂⟩)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        C' * B k := by
      rw [mul_inv_rev, inv_inv]
      rfl
    rw [e]
    refine EntryBound.of_tendsto (F := atTop) (M := fun m ↦ B' m * B k - 1) (fun i j ↦ ?_)
      ((eventually_ge_atTop k).mono fun m hm ↦ by
        have := (hmem hm).2
        simpa [B, B'] using this)
    have := tendsto_mul_apply (M' := fun _ ↦ B k) (N := C') (N' := B k) hc'
      (fun _ _ ↦ tendsto_const_nhds) i j
    simpa using this.sub (tendsto_const_nhds (x := (1 : Matrix (Fin n) (Fin n) E) i j))

omit [FiniteDimensional ℚ_[l] E] in
/-- A bound for a product `P * D * Q` with `D` small. -/
lemma EntryBound.mul_mul (P Q : Matrix (Fin n) (Fin n) E) {D : Matrix (Fin n) (Fin n) E} {ε : ℝ}
    (hD : EntryBound D ε) (hε : 0 ≤ ε) :
    EntryBound (P * D * Q) (entrySum P * ε * entrySum Q) :=
  ((entryBound_entrySum P).mul hD (entrySum_nonneg _) hε).mul (entryBound_entrySum Q)
    (mul_nonneg (entrySum_nonneg _) hε) (entrySum_nonneg _)

omit [FiniteDimensional ℚ_[l] E] in
/-- A positive radius `ε` with `p * ε * q ≤ r`. -/
lemma exists_pos_mul_mul_le {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 < r) :
    ∃ ε > 0, p * ε * q ≤ r := by
  refine ⟨r / ((p + 1) * (q + 1)), by positivity, ?_⟩
  calc p * (r / ((p + 1) * (q + 1))) * q ≤ (p + 1) * (r / ((p + 1) * (q + 1))) * (q + 1) := by
        gcongr <;> linarith
    _ = r := by field_simp

omit [FiniteDimensional ℚ_[l] E] in
/-- Matrices with continuous entries are eventually entrywise close. -/
lemma eventually_entryBound_sub {Z : Type*} [TopologicalSpace Z]
    (M : Z → Matrix (Fin n) (Fin n) E) (hM : ∀ i j, Continuous fun z ↦ M z i j) (z₀ : Z)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ z in 𝓝 z₀, EntryBound (M z - M z₀) ε := by
  simp only [EntryBound, eventually_all]
  intro i j
  filter_upwards [Metric.tendsto_nhds.1 ((hM i j).tendsto z₀) ε hε] with z hz
  rw [Matrix.sub_apply, ← dist_eq_norm]
  exact hz.le

omit [FiniteDimensional ℚ_[l] E] in
/-- For `γ : Z → GL_n(E)` whose entries and whose inverse's entries are continuous, the action
`z ↦ γ z • q` on every coset `q` of every congruence subgroup is locally constant. -/
lemma isLocallyConstant_smul_mk {Z : Type*} [TopologicalSpace Z] (γ : Z → GL (Fin n) E)
    (hγ : ∀ i j, Continuous fun z ↦ (γ z : Matrix (Fin n) (Fin n) E) i j)
    (hγ' : ∀ i j, Continuous fun z ↦ ((γ z)⁻¹ : GL (Fin n) E) i j) (k : ℕ)
    (q : GL (Fin n) E ⧸ congruenceSubgroup E n k) :
    IsLocallyConstant fun z ↦ γ z • q := by
  induction q using QuotientGroup.induction_on with | H a => ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z₀
  let A : Matrix (Fin n) (Fin n) E := a
  let A' : Matrix (Fin n) (Fin n) E := (a⁻¹ : GL (Fin n) E)
  let G (z : Z) : Matrix (Fin n) (Fin n) E := γ z
  let G' (z : Z) : Matrix (Fin n) (Fin n) E := ((γ z)⁻¹ : GL (Fin n) E)
  obtain ⟨ε, hε, hεr⟩ := exists_pos_mul_mul_le (entrySum_nonneg (A' * G' z₀))
    (entrySum_nonneg A) (congruenceRadius_pos (l := l) k)
  obtain ⟨ε', hε', hεr'⟩ := exists_pos_mul_mul_le (entrySum_nonneg A')
    (entrySum_nonneg (G z₀ * A)) (congruenceRadius_pos (l := l) k)
  filter_upwards [eventually_entryBound_sub G hγ z₀ hε,
    eventually_entryBound_sub G' hγ' z₀ hε'] with z hz hz'
  change ((γ z * a : GL (Fin n) E) : GL (Fin n) E ⧸ congruenceSubgroup E n k) =
    ((γ z₀ * a : GL (Fin n) E) : GL (Fin n) E ⧸ congruenceSubgroup E n k)
  rw [QuotientGroup.eq]
  have h1 : A' * G' z₀ * (G z₀ * A) = 1 := by
    simp only [A, A', G, G', ← Units.val_mul]
    rw [show a⁻¹ * (γ z₀)⁻¹ * (γ z₀ * a) = 1 by group, Units.val_one]
  refine ⟨?_, ?_⟩
  · have e : ((((γ z * a)⁻¹ * (γ z₀ * a)) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
        A' * (G' z - G' z₀) * (G z₀ * A) := by
      rw [← h1]
      simp only [A, A', G, G', mul_inv_rev, Units.val_mul]
      noncomm_ring
    rw [e]
    exact (EntryBound.mul_mul A' (G z₀ * A) hz' hε'.le).mono hεr'
  · have e : ((((γ z * a)⁻¹ * (γ z₀ * a))⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
        (A' * G' z₀) * (G z - G z₀) * A := by
      rw [← h1]
      simp only [A, A', G, G', mul_inv_rev, inv_inv, Units.val_mul]
      noncomm_ring
    rw [e]
    exact (EntryBound.mul_mul (A' * G' z₀) A hz hε.le).mono hεr

omit [FiniteDimensional ℚ_[l] E] in
/-- A function `σ : X → GL_n(E)` whose reductions modulo all congruence subgroups are locally
constant has continuous entries, and its inverse has continuous entries. -/
lemma continuous_apply_of_isLocallyConstant_mk {X : Type*} [TopologicalSpace X]
    (σ : X → GL (Fin n) E)
    (hσ : ∀ k, IsLocallyConstant fun x ↦ ((σ x : GL (Fin n) E) :
      GL (Fin n) E ⧸ congruenceSubgroup E n k)) (i j : Fin n) :
    (Continuous fun x ↦ (σ x : Matrix (Fin n) (Fin n) E) i j) ∧
      Continuous fun x ↦ ((σ x)⁻¹ : GL (Fin n) E) i j := by
  refine ⟨continuous_iff_continuousAt.2 fun x₀ ↦ ?_, continuous_iff_continuousAt.2 fun x₀ ↦ ?_⟩ <;>
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  · obtain ⟨k, hk⟩ := exists_congruenceRadius_lt (l := l)
      (div_pos hε (by linarith [entrySum_nonneg ((σ x₀ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E)] : 0 < entrySum ((σ x₀ : GL (Fin n) E) :
          Matrix (Fin n) (Fin n) E) + 1))
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hσ k) x₀] with x hx
    have hκ := QuotientGroup.eq.1 hx.symm
    have e : (σ x : Matrix (Fin n) (Fin n) E) - σ x₀ =
        (σ x₀ : Matrix (Fin n) (Fin n) E) *
          ((((σ x₀)⁻¹ * σ x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) := by
      simp [mul_sub]
    have hb := ((entryBound_entrySum ((σ x₀ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).mul
      hκ.1 (entrySum_nonneg _) (congruenceRadius_nonneg k)) i j
    rw [← e, Matrix.sub_apply] at hb
    rw [dist_eq_norm]
    refine hb.trans_lt ?_
    rw [lt_div_iff₀ (by linarith [entrySum_nonneg ((σ x₀ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E)])] at hk
    nlinarith [entrySum_nonneg ((σ x₀ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E),
      congruenceRadius_nonneg (l := l) k]
  · obtain ⟨k, hk⟩ := exists_congruenceRadius_lt (l := l)
      (div_pos hε (by linarith [entrySum_nonneg (((σ x₀)⁻¹ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E)] : 0 < entrySum (((σ x₀)⁻¹ : GL (Fin n) E) :
          Matrix (Fin n) (Fin n) E) + 1))
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hσ k) x₀] with x hx
    have hκ := QuotientGroup.eq.1 hx.symm
    have e : (((σ x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - ((σ x₀)⁻¹ : GL (Fin n) E) =
        (((((σ x₀)⁻¹ * σ x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) *
          ((σ x₀)⁻¹ : GL (Fin n) E) := by
      simp [sub_mul]
    have hb := (hκ.2.mul (entryBound_entrySum (((σ x₀)⁻¹ : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E)) (congruenceRadius_nonneg k) (entrySum_nonneg _)) i j
    rw [← e, Matrix.sub_apply] at hb
    rw [dist_eq_norm]
    refine hb.trans_lt ?_
    rw [lt_div_iff₀ (by linarith [entrySum_nonneg (((σ x₀)⁻¹ : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E)])] at hk
    nlinarith [entrySum_nonneg (((σ x₀)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E),
      congruenceRadius_nonneg (l := l) k]

end PadicAlgCl

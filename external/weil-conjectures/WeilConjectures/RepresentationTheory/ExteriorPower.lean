/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.RepresentationTheory.Filtration

/-!
# The exterior powers of a filtered representation

Let `U ⊆ V` be a subspace. The `n`-th exterior power `⋀ⁿ V` is filtered by the subspaces
`F_j = span {v₁ ∧ ⋯ ∧ vₙ | at least j of the vᵢ lie in U}`
(`exteriorPower.countSpan`), with `F_0 = ⋀ⁿ V` and `F_{n+1} = 0`, and the graded pieces are

$$
F_j / F_{j+1} \cong \textstyle\bigwedge^j U \otimes \bigwedge^{n-j} (V / U),
$$

via `u₁ ∧ ⋯ ∧ u_j ⊗ x̄₁ ∧ ⋯ ∧ x̄_l ↦ u₁ ∧ ⋯ ∧ u_j ∧ s(x̄₁) ∧ ⋯ ∧ s(x̄_l)` for a linear
section `s` of `V → V / U`. When `U` is a subrepresentation, the `F_j` are
subrepresentations and these isomorphisms are equivariant: changing the section changes the
image by an element of `F_{j+1}`.

As a consequence, the exterior powers of a representation and of its semisimplification have the
same constituents: the graded pieces of a filtration of `V` determine the constituents of `⋀ⁿ V`.

## Main definitions

- `exteriorPower.countSpan`: the filtration `F_j` of `⋀ⁿ V`.
- `exteriorPower.wedgeMul`: the product `⋀ʲ V × ⋀ˡ V → ⋀ʲ⁺ˡ V`.
- `Subrepresentation.exteriorPowerFiltration`: the filtration `F_j` for a subrepresentation.

## Main results

- `exteriorPower.toGraded_bijective`: `⋀ʲ U ⊗ ⋀ⁿ⁻ʲ (V / U) ≃ F_j / F_{j+1}`.
- `Subrepresentation.exteriorPowerGradedEquiv`: the same, equivariantly.
- `Representation.ConstituentsLE.exteriorPower_of_chain`: the constituents of `⋀ⁿ` of a filtered
  representation only depend on the graded pieces.
- `Representation.CompositionSeries.constituentsLE_exteriorPower_semisimplification` and its primed
  version: `⋀ⁿ V` and `⋀ⁿ V^ss` have the same constituents.

## Blueprint

- `lemma-tensor-exterior-powers-filtered-representations--2`,
`lemma-tensor-exterior-powers-filtered-representations--3`: the exterior power of a
  filtered representation, through its constituents. The full filtration with graded pieces
  `⨂ᵢ ⋀^{nᵢ} A_i` is in `WeilConjectures.RepresentationTheory.ExteriorPowerFiltration`.
-/

@[expose] public section

open TensorProduct

namespace exteriorPower

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

open Classical in
/-- The subspace of `⋀ⁿ V` spanned by the wedges `v₁ ∧ ⋯ ∧ vₙ` with at least `j` of the `vᵢ` in
the subspace `P`. -/
noncomputable def countSpan (P : Submodule k V) (n j : ℕ) : Submodule k (⋀[k]^n V) :=
  Submodule.span k {x | ∃ v : Fin n → V,
    j ≤ (Finset.univ.filter fun i ↦ v i ∈ P).card ∧ ιMulti k n v = x}

variable (P : Submodule k V) (n : ℕ)

open Classical in
theorem ιMulti_mem_countSpan {j : ℕ} (v : Fin n → V)
    (hv : j ≤ (Finset.univ.filter fun i ↦ v i ∈ P).card) : ιMulti k n v ∈ countSpan P n j :=
  Submodule.subset_span ⟨v, hv, rfl⟩

theorem countSpan_succ_le (j : ℕ) : countSpan P n (j + 1) ≤ countSpan P n j :=
  Submodule.span_mono fun _ ⟨v, hv, hx⟩ ↦ ⟨v, (Nat.le_succ j).trans hv, hx⟩

theorem countSpan_anti {i j : ℕ} (h : i ≤ j) : countSpan P n j ≤ countSpan P n i :=
  Submodule.span_mono fun _ ⟨v, hv, hx⟩ ↦ ⟨v, h.trans hv, hx⟩

theorem countSpan_zero : countSpan P n 0 = ⊤ := by
  refine eq_top_iff.2 ((ιMulti_span (R := k) (n := n) (M := V)).symm.le.trans ?_)
  exact Submodule.span_le.2 fun _ ⟨v, hv⟩ ↦ Submodule.subset_span ⟨v, Nat.zero_le _, hv⟩

theorem countSpan_eq_bot {j : ℕ} (h : n < j) : countSpan P n j = ⊥ := by
  classical
  refine (Submodule.span_eq_bot).2 fun _ ⟨v, hv, _⟩ ↦ ?_
  have := (Finset.card_filter_le Finset.univ fun i ↦ v i ∈ P).trans_eq (Finset.card_fin n)
  omega

/-- A linear map preserving `P` preserves the filtration. -/
theorem map_mem_countSpan {f : V →ₗ[k] V} (hf : ∀ x ∈ P, f x ∈ P) {j : ℕ} {x : ⋀[k]^n V}
    (hx : x ∈ countSpan P n j) : map n f x ∈ countSpan P n j := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [map_apply_ιMulti]
    refine ιMulti_mem_countSpan P n _ (hv.trans (Finset.card_le_card fun i hi ↦ ?_))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hf _ hi
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx

/-- **Perturbing a wedge by vectors of `P`.** If `a` has at least `j` entries in `P` on a set `J`
of indices, and `y` is a family of vectors of `P` vanishing on `J`, then
`ι(a + y) - ι(a)` lies in the next filtration step `F_{j+1}`: expanding multilinearly, every other
term has an extra entry in `P`, or a zero entry. -/
theorem ιMulti_add_sub_ιMulti_mem_countSpan {j : ℕ} (a y : Fin n → V) (J : Finset (Fin n))
    (hJ : j ≤ J.card) (haJ : ∀ i ∈ J, a i ∈ P) (hyJ : ∀ i ∈ J, y i = 0) (hy : ∀ i, y i ∈ P) :
    ιMulti k n (a + y) - ιMulti k n a ∈ countSpan P n (j + 1) := by
  classical
  have h : ιMulti k n (a + y) = ∑ s : Finset (Fin n), ιMulti k n (s.piecewise a y) :=
    (ιMulti k n).toMultilinearMap.map_add_univ a y
  rw [h, ← Finset.add_sum_erase _ _ (Finset.mem_univ Finset.univ), Finset.piecewise_univ,
    add_sub_cancel_left]
  refine Submodule.sum_mem _ fun s hs ↦ ?_
  have hs' : s ≠ Finset.univ := Finset.ne_of_mem_erase hs
  by_cases hJs : J ⊆ s
  · -- an extra entry in `P` outside `s`
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.2 hs')
    refine ιMulti_mem_countSpan P n _ ?_
    have hi₀J : i₀ ∉ J := fun h ↦ hi₀ (hJs h)
    calc j + 1 ≤ (insert i₀ J).card := by rw [Finset.card_insert_of_notMem hi₀J]; omega
      _ ≤ _ := Finset.card_le_card fun i hi ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases Finset.mem_insert.1 hi with rfl | hi
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hi₀]
          exact hy _
        · rw [Finset.piecewise_eq_of_mem _ _ _ (hJs hi)]
          exact haJ i hi
  · -- a zero entry
    obtain ⟨i, hiJ, his⟩ := Finset.not_subset.1 hJs
    rw [(ιMulti k n).map_coord_zero i (by rw [Finset.piecewise_eq_of_notMem _ _ _ his, hyJ i hiJ])]
    exact zero_mem _

/-- The wedge product `⋀ʲ V × ⋀ˡ V → ⋀ⁿ V`, for `j + l = n`, as a bilinear map: the product in the
exterior algebra. -/
noncomputable def wedgeMul {j l : ℕ} (h : j + l = n) :
    ⋀[k]^j V →ₗ[k] ⋀[k]^l V →ₗ[k] ⋀[k]^n V :=
  LinearMap.mk₂ k (fun x y ↦ ⟨(x : ExteriorAlgebra k V) * y,
    h ▸ SetLike.mul_mem_graded x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

@[simp]
theorem coe_wedge_apply {j l : ℕ} (h : j + l = n) (x : ⋀[k]^j V) (y : ⋀[k]^l V) :
    (wedgeMul n h x y : ExteriorAlgebra k V) = x * y :=
  rfl

theorem wedge_ιMulti_ιMulti {j l : ℕ} (a : Fin j → V) (b : Fin l → V) :
    wedgeMul (j + l) rfl (ιMulti k j a) (ιMulti k l b) = ιMulti k (j + l) (Fin.append a b) :=
  Subtype.ext (by simp [ExteriorAlgebra.ιMulti_mul_ιMulti])

/-! ### The graded pieces -/

section Graded

variable {P} (s : V ⧸ P →ₗ[k] V)

/-- The map `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → ⋀ⁿ V`, `u ⊗ x̄ ↦ u ∧ s(x̄)`, for a linear section `s` of the
quotient map and `j + l = n`. -/
noncomputable def wedgeSection {j l : ℕ} (h : j + l = n) :
    ⋀[k]^j P ⊗[k] ⋀[k]^l (V ⧸ P) →ₗ[k] ⋀[k]^n V :=
  TensorProduct.lift ((wedgeMul n h).compl₁₂ (map j P.subtype) (map l s))

theorem wedgeSection_tmul_ιMulti {j l : ℕ} (u : Fin j → P) (x : Fin l → V ⧸ P) :
    wedgeSection (j + l) s rfl (ιMulti k j u ⊗ₜ ιMulti k l x) =
      ιMulti k (j + l) (Fin.append (P.subtype ∘ u) (s ∘ x)) := by
  rw [wedgeSection, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, map_apply_ιMulti,
    map_apply_ιMulti, wedge_ιMulti_ιMulti]

open Classical in
theorem card_le_filter_append {j l : ℕ} (u : Fin j → P) (x : Fin l → V) :
    j ≤ (Finset.univ.filter fun i ↦ Fin.append (P.subtype ∘ u) x i ∈ P).card := by
  calc j = (Finset.univ.map (Fin.castAddEmb l)).card := by simp
    _ ≤ _ := Finset.card_le_card fun i hi ↦ by
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hi
      simp

theorem wedgeSection_mem_countSpan {j l : ℕ} (h : j + l = n)
    (t : ⋀[k]^j P ⊗[k] ⋀[k]^l (V ⧸ P)) : wedgeSection n s h t ∈ countSpan P n j := by
  subst h
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simpa using add_mem hx hy
  | tmul x y =>
    have hx : x ∈ Submodule.span k (Set.range (ιMulti k j)) := by
      rw [ιMulti_span]; exact Submodule.mem_top
    have hy : y ∈ Submodule.span k (Set.range (ιMulti k l)) := by
      rw [ιMulti_span]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        rw [wedgeSection_tmul_ιMulti]
        exact ιMulti_mem_countSpan P _ _ (card_le_filter_append u _)
      | zero => simp
      | add y y' _ _ hy hy' => simpa [TensorProduct.tmul_add] using add_mem hy hy'
      | smul a y _ hy => simpa [TensorProduct.tmul_smul] using Submodule.smul_mem _ a hy
    | zero => simp
    | add x x' _ _ hx hx' => simpa [TensorProduct.add_tmul] using add_mem hx hx'
    | smul a x _ hx =>
      rw [← TensorProduct.smul_tmul', map_smul]
      exact Submodule.smul_mem _ a hx

/-- The graded piece `F_j ⧸ F_{j+1}` of the filtration of `⋀ⁿ V`. -/
abbrev Graded (n j : ℕ) : Type _ :=
  countSpan P n j ⧸ (countSpan P n (j + 1)).comap (countSpan P n j).subtype

/-- The map `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → F_j ⧸ F_{j+1}`. -/
noncomputable def toGraded {j l : ℕ} (h : j + l = n) :
    ⋀[k]^j P ⊗[k] ⋀[k]^l (V ⧸ P) →ₗ[k] Graded (P := P) n j :=
  Submodule.mkQ _ ∘ₗ (wedgeSection n s h).codRestrict _ (wedgeSection_mem_countSpan n s h)

variable {s} in
/-- `u ∧ s(x̄)` exhausts the graded piece `F_j ⧸ F_{j+1}`: a wedge with exactly `j` entries in `P`
is, modulo `F_{j+1}`, the wedge of these entries with the sections of the classes of the others,
up to a sign. -/
theorem toGraded_surjective (hs : ∀ x, P.mkQ (s x) = x) {j l : ℕ} (h : j + l = n) :
    Function.Surjective (toGraded n s h) := by
  classical
  subst h
  intro q
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, hv, rfl⟩ := hz
    set J := Finset.univ.filter fun i ↦ v i ∈ P
    rcases hv.lt_or_eq with hlt | heq
    · refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, Submodule.Quotient.mk_eq_zero]
      exact ιMulti_mem_countSpan P _ v hlt
    -- the wedge `v'` with the entries outside `J` replaced by the sections of their classes
    set v' : Fin (j + l) → V := fun i ↦ if i ∈ J then v i else s (P.mkQ (v i))
    have hv'J (i) (hi : i ∈ J) : v' i = v i := ite_eq_left hi
    have hv'Jc (i) (hi : i ∉ J) : v' i = s (P.mkQ (v i)) := ite_eq_right hi
    have hJmem (i) (hi : i ∈ J) : v i ∈ P := (Finset.mem_filter.1 hi).2
    have hdiff : ιMulti k (j + l) (v' + (v - v')) - ιMulti k (j + l) v' ∈
        countSpan P (j + l) (j + 1) := by
      refine ιMulti_add_sub_ιMulti_mem_countSpan P _ v' (v - v') J heq.le
        (fun i hi ↦ by rw [hv'J i hi]; exact hJmem i hi)
        (fun i hi ↦ by rw [Pi.sub_apply, hv'J i hi, sub_self]) fun i ↦ ?_
      by_cases hi : i ∈ J
      · simp [hv'J i hi]
      · rw [Pi.sub_apply, hv'Jc i hi, ← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub,
          ← Submodule.mkQ_apply P (s _), hs, Submodule.mkQ_apply, sub_self]
    rw [add_sub_cancel] at hdiff
    have hv'mem : ιMulti k (j + l) v' ∈ countSpan P (j + l) j :=
      ιMulti_mem_countSpan P _ _ (heq.le.trans (Finset.card_le_card fun i hi ↦
        Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hv'J i hi]; exact hJmem i hi⟩))
    -- reorder `v'` with the entries of `J` first
    have hcardJ : Fintype.card {i // i ∈ J} = j := by
      rw [Fintype.card_coe, ← heq]
    have hcardJc : Fintype.card {i // i ∉ J} = l := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, ← heq, Fintype.card_fin]
      omega
    let e₁ : Fin j ≃ {i // i ∈ J} := (Fintype.equivFinOfCardEq hcardJ).symm
    let e₂ : Fin l ≃ {i // i ∉ J} := (Fintype.equivFinOfCardEq hcardJc).symm
    let σ : Equiv.Perm (Fin (j + l)) :=
      finSumFinEquiv.symm.trans ((e₁.sumCongr e₂).trans (Equiv.sumCompl fun i ↦ i ∈ J))
    let u : Fin j → P := fun a ↦ ⟨v (e₁ a), hJmem _ (e₁ a).2⟩
    let x : Fin l → V ⧸ P := fun b ↦ P.mkQ (v (e₂ b))
    have hσ : v' ∘ σ = Fin.append (P.subtype ∘ u) (s ∘ x) := by
      funext i
      refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
      · simp [σ, u, hv'J _ (e₁ a).2]
      · simp [σ, x, hv'Jc _ (e₂ b).2]
    have hperm := (ιMulti k (j + l)).map_perm v' σ
    rw [hσ, ← wedgeSection_tmul_ιMulti] at hperm
    have h1 : toGraded (j + l) s rfl (ιMulti k j u ⊗ₜ ιMulti k l x) =
        Submodule.Quotient.mk ⟨Equiv.Perm.sign σ • ιMulti k (j + l) v',
          Submodule.smul_mem _ _ hv'mem⟩ :=
      congrArg _ (Subtype.ext hperm)
    refine ⟨(Equiv.Perm.sign σ) • (ιMulti k j u ⊗ₜ ιMulti k l x), ?_⟩
    rw [map_zsmul_unit, h1, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      Submodule.mem_comap]
    convert neg_mem hdiff using 1
    simp [smul_smul]
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
  | smul c x hx ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨c • a, by rw [map_smul, ha]; rfl⟩

variable (P) in
/-- The graded pieces telescope: `∑_{i < m} dim F_i ⧸ F_{i+1} + dim F_m = dim ⋀ⁿ V`. -/
theorem sum_finrank_graded_add [FiniteDimensional k V] (m : ℕ) :
    ∑ i ∈ Finset.range m, Module.finrank k (Graded (P := P) n i) +
      Module.finrank k (countSpan P n m) = Module.finrank k (⋀[k]^n V) := by
  induction m with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, zero_add, countSpan_zero P n, finrank_top]
  | succ m ih =>
    rw [Finset.sum_range_succ, add_assoc, ← ih]
    congr 1
    rw [← Submodule.finrank_quotient_add_finrank
      ((countSpan P n (m + 1)).comap (countSpan P n m).subtype),
      (Submodule.comapSubtypeEquivOfLe (countSpan_succ_le P n m)).finrank_eq]

/-- **The graded pieces of the filtration of `⋀ⁿ V`**: for a finite-dimensional `V`, the map
`⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → F_j ⧸ F_{j+1}` is bijective. It is surjective, and the dimensions agree:
`∑ⱼ (dim P choose j) (dim V/P choose n - j) = (dim V choose n)` (Vandermonde). -/
theorem toGraded_bijective [FiniteDimensional k V] (hs : ∀ x, P.mkQ (s x) = x) {j l : ℕ}
    (h : j + l = n) : Function.Bijective (toGraded n s h) := by
  set p := Module.finrank k P
  set q := Module.finrank k (V ⧸ P)
  have hdim (i : ℕ) (hi : i ≤ n) : Module.finrank k (⋀[k]^i P ⊗[k] ⋀[k]^(n - i) (V ⧸ P)) =
      p.choose i * q.choose (n - i) := by
    rw [Module.finrank_tensorProduct, finrank_eq, finrank_eq]
  have hle (i : ℕ) (hi : i ≤ n) :
      Module.finrank k (Graded (P := P) n i) ≤ p.choose i * q.choose (n - i) :=
    (hdim i hi) ▸ by
      have hr := LinearMap.finrank_range_le (toGraded n s (Nat.add_sub_cancel' hi))
      rwa [LinearMap.range_eq_top.2 (toGraded_surjective n hs (Nat.add_sub_cancel' hi)),
        finrank_top] at hr
  have hsum : ∑ i ∈ Finset.range (n + 1), Module.finrank k (Graded (P := P) n i) =
      ∑ i ∈ Finset.range (n + 1), p.choose i * q.choose (n - i) := by
    have := sum_finrank_graded_add P n (n + 1)
    rw [countSpan_eq_bot P n (Nat.lt_succ_self n), finrank_bot, add_zero, finrank_eq,
      ← Submodule.finrank_quotient_add_finrank P, Nat.add_comm (Module.finrank k (V ⧸ P)),
      Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    exact this
  have heq := (Finset.sum_eq_sum_iff_of_le fun i hi ↦
    hle i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).1 hsum j
    (Finset.mem_range.2 (by omega))
  have hl : l = n - j := by omega
  subst hl
  refine ⟨?_, toGraded_surjective n hs h⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2
    (toGraded_surjective n hs h)
  rw [hdim j (by omega), heq]

end Graded

end exteriorPower

/-! ### The filtration of the exterior power of a representation -/

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

/-- The filtration `F_j = span {v₁ ∧ ⋯ ∧ vₙ | at least j of the vᵢ lie in P}` of `⋀ⁿ V` by
subrepresentations, for a subrepresentation `P` of `ρ`. -/
noncomputable def exteriorPowerFiltration (P : Subrepresentation ρ) (n j : ℕ) :
    Subrepresentation (ρ.exteriorPower n) where
  toSubmodule := exteriorPower.countSpan P.toSubmodule n j
  apply_mem_toSubmodule w _ hx :=
    exteriorPower.map_mem_countSpan _ n (fun _ hy ↦ P.apply_mem_toSubmodule w hy) hx

variable (P : Subrepresentation ρ) (n : ℕ)

theorem exteriorPowerFiltration_succ_le (j : ℕ) :
    P.exteriorPowerFiltration n (j + 1) ≤ P.exteriorPowerFiltration n j :=
  exteriorPower.countSpan_succ_le _ n j

theorem exteriorPowerFiltration_zero : P.exteriorPowerFiltration n 0 = ⊤ :=
  toSubmodule_injective (exteriorPower.countSpan_zero _ n)

theorem exteriorPowerFiltration_eq_bot {j : ℕ} (h : n < j) : P.exteriorPowerFiltration n j = ⊥ :=
  toSubmodule_injective (exteriorPower.countSpan_eq_bot _ n h)

/-- The quotient map `V → V ⧸ P` intertwines `ρ` with the quotient representation. -/
theorem quotient_apply_mkQ (w : W) (x : V) :
    P.quotient w (P.toSubmodule.mkQ x) = P.toSubmodule.mkQ (ρ w x) :=
  rfl

/-- The map `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → F_j ⧸ F_{j+1}` is equivariant: changing `ρ(w) s(x̄)` into
`s(ρ(w) x̄)` changes the wedge by an element of `F_{j+1}`. -/
theorem toGraded_comp_map (s : V ⧸ P.toSubmodule →ₗ[k] V) (hs : ∀ x, P.toSubmodule.mkQ (s x) = x)
    {j l : ℕ} (h : j + l = n) (w : W) :
    exteriorPower.toGraded n s h ∘ₗ ((P.toRepresentation.exteriorPower j).tprod
      (P.quotient.exteriorPower l) w) =
      (P.exteriorPowerFiltration n j).subquotient (P.exteriorPowerFiltration n (j + 1)) w ∘ₗ
        exteriorPower.toGraded n s h := by
  subst h
  refine TensorProduct.ext (exteriorPower.linearMap_ext (AlternatingMap.ext fun u ↦
    exteriorPower.linearMap_ext (AlternatingMap.ext fun x ↦ ?_)))
  simp only [LinearMap.compAlternatingMap_apply, Representation.tprod_apply]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  change exteriorPower.wedgeSection (j + l) s rfl
      (exteriorPower.map j (P.toRepresentation w) (exteriorPower.ιMulti k j u) ⊗ₜ
        exteriorPower.map l (P.quotient w) (exteriorPower.ιMulti k l x)) -
      exteriorPower.map (j + l) (ρ w) (exteriorPower.wedgeSection (j + l) s rfl
        (exteriorPower.ιMulti k j u ⊗ₜ exteriorPower.ιMulti k l x)) ∈ _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.wedgeSection_tmul_ιMulti, exteriorPower.wedgeSection_tmul_ιMulti,
    exteriorPower.map_apply_ιMulti]
  -- the two wedges differ by vectors of `P` in the last `l` entries
  set a : Fin (j + l) → V := ρ w ∘ Fin.append (P.toSubmodule.subtype ∘ u) (s ∘ x)
  set y : Fin (j + l) → V := Fin.append (0 : Fin j → V)
    (fun b ↦ s (P.quotient w (x b)) - ρ w (s (x b)))
  have hay : Fin.append (P.toSubmodule.subtype ∘ (P.toRepresentation w ∘ u))
      (s ∘ (P.quotient w ∘ x)) = a + y := by
    funext i
    refine Fin.addCases (fun c ↦ ?_) (fun b ↦ ?_) i
    · simp [a, y]
      rfl
    · simp [a, y]
  rw [hay]
  refine exteriorPower.ιMulti_add_sub_ιMulti_mem_countSpan _ _ a y
    (Finset.univ.map (Fin.castAddEmb l)) (by simp) (fun i hi ↦ ?_) (fun i hi ↦ ?_) fun i ↦ ?_
  · obtain ⟨c, -, rfl⟩ := Finset.mem_map.1 hi
    simpa [a] using P.apply_mem_toSubmodule w (u c).2
  · obtain ⟨c, -, rfl⟩ := Finset.mem_map.1 hi
    simp [y]
  · refine Fin.addCases (fun c ↦ ?_) (fun b ↦ ?_) i
    · simp [y]
    · simp only [y, Fin.append_right]
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hs, ← quotient_apply_mkQ, hs, sub_self]

/-- **The graded pieces of the exterior power of a representation.** For a subrepresentation `P`
of a finite-dimensional representation `ρ`, the `j`-th graded piece `F_j ⧸ F_{j+1}` of the
filtration of `⋀ⁿ V` is equivalent to `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P)`, `j + l = n`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--2`) -/
noncomputable def exteriorPowerGradedEquiv [FiniteDimensional k V] {j l : ℕ} (h : j + l = n) :
    ((P.toRepresentation.exteriorPower j).tprod (P.quotient.exteriorPower l)).Equiv
      ((P.exteriorPowerFiltration n j).subquotient (P.exteriorPowerFiltration n (j + 1))) :=
  have hs := P.toSubmodule.mkQ.exists_rightInverse_of_surjective P.toSubmodule.range_mkQ
  .mk (.ofBijective _ (exteriorPower.toGraded_bijective n (s := hs.choose)
      (fun x ↦ LinearMap.congr_fun hs.choose_spec x) h))
    (P.toGraded_comp_map n hs.choose (fun x ↦ LinearMap.congr_fun hs.choose_spec x) h)

end Subrepresentation

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}


end Subrepresentation

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]

/-- The exterior power `⋀⁰ V` of a representation is the trivial representation on
`⋀⁰ V ≃ k`. -/
noncomputable def exteriorPowerZeroEquiv (ρ : Representation k W V) :
    (ρ.exteriorPower 0).Equiv (Representation.trivial k W k) :=
  .mk (_root_.exteriorPower.zeroEquiv k V) fun w ↦ LinearMap.ext fun x ↦
    LinearMap.congr_fun (_root_.exteriorPower.zeroEquiv_naturality (ρ w)) x

/-- The positive exterior powers of the zero representation have no constituents. -/
theorem ConstituentsLE.exteriorPower_succ_of_subsingleton [Subsingleton V]
    {V' : Type*} [AddCommGroup V'] [Module k V'] (ρ : Representation k W V)
    (σ : Representation k W V') (n : ℕ) : ConstituentsLE (ρ.exteriorPower (n + 1)) σ := by
  have : Subsingleton (⋀[k]^(n + 1) V) := by
    rw [← Module.finrank_zero_iff (R := k), _root_.exteriorPower.finrank_eq,
      Module.finrank_zero_of_subsingleton, Nat.choose_zero_succ]
  exact ConstituentsLE.of_subsingleton _ σ

end Representation

/-! ### The constituents of the exterior powers of a filtered representation -/

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
  {V V' V₁ V₂ : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  {ρ : Representation k W V} {σ : Representation k W V'}
  {ρ₁ : Representation k W V₁} {σ₁ : Representation k W V₂}

/-- Equivalent representations have equivalent exterior powers. -/
noncomputable def Equiv.exteriorPower (e : ρ.Equiv σ) (n : ℕ) :
    (ρ.exteriorPower n).Equiv (σ.exteriorPower n) :=
  .mk (.ofLinearMap (_root_.exteriorPower.map n (e.toLinearEquiv : V →ₗ[k] V'))
      (_root_.exteriorPower.map n (e.toLinearEquiv.symm : V' →ₗ[k] V))
      (by rw [← _root_.exteriorPower.map_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, _root_.exteriorPower.map_id])
      (by rw [← _root_.exteriorPower.map_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, _root_.exteriorPower.map_id])) fun w ↦ by
    change _root_.exteriorPower.map n _ ∘ₗ _root_.exteriorPower.map n (ρ w) =
      _root_.exteriorPower.map n (σ w) ∘ₗ _root_.exteriorPower.map n _
    rw [← _root_.exteriorPower.map_comp, ← _root_.exteriorPower.map_comp]
    congr 1
    exact e.isIntertwining' w

namespace ConstituentsLE

variable {V'' : Type*} [AddCommGroup V''] [Module k V''] {τ : Representation k W V''}

/-- The constituents of `⋀ⁿ V` are constituents of the pieces `⋀ʲ P ⊗ ⋀ⁿ⁻ʲ (V ⧸ P)`, for a
subrepresentation `P`. (blueprint: `lemma-tensor-exterior-powers-filtered-representations--2`) -/
theorem exteriorPower_of_tprod [FiniteDimensional k V] (P : Subrepresentation ρ) (n : ℕ)
    (h : ∀ j ≤ n, ConstituentsLE
      ((P.toRepresentation.exteriorPower j).tprod (P.quotient.exteriorPower (n - j))) τ) :
    ConstituentsLE (ρ.exteriorPower n) τ :=
  of_chain (P.exteriorPowerFiltration n) (P.exteriorPowerFiltration_succ_le n)
    (P.exteriorPowerFiltration_zero n) (P.exteriorPowerFiltration_eq_bot n (Nat.lt_succ_self n))
    fun j hj ↦ (of_equiv (P.exteriorPowerGradedEquiv n (Nat.add_sub_cancel' (by omega))).symm).trans
      (h j (by omega))

/-- The pieces `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P)`, `j + l = n`, are subquotients of `⋀ⁿ V`, so their constituents
are constituents of `⋀ⁿ V`. -/
theorem tprod_exteriorPower [FiniteDimensional k V] (P : Subrepresentation ρ) {n j l : ℕ}
    (h : j + l = n) : ConstituentsLE
      ((P.toRepresentation.exteriorPower j).tprod (P.quotient.exteriorPower l))
      (ρ.exteriorPower n) :=
  (of_equiv (P.exteriorPowerGradedEquiv n h)).trans (subquotient _ _)

/-- **Comparing exterior powers along an extension.** Let `P ⊆ V` and `P' ⊆ V'` be
subrepresentations such that every constituent of `⋀ʲ P` is one of `⋀ʲ P'` for all `j`, and with
equivalent quotients `V ⧸ P ≃ V' ⧸ P'`. Then every constituent of `⋀ⁿ V` is a constituent of
`⋀ⁿ V'`. -/
theorem exteriorPower_of_subrepresentation [FiniteDimensional k V] [FiniteDimensional k V']
    (P : Subrepresentation ρ) (P' : Subrepresentation σ)
    (hP : ∀ j, ConstituentsLE (P.toRepresentation.exteriorPower j)
      (P'.toRepresentation.exteriorPower j))
    (e : P.quotient.Equiv P'.quotient) (n : ℕ) :
    ConstituentsLE (ρ.exteriorPower n) (σ.exteriorPower n) :=
  exteriorPower_of_tprod P n fun j hj ↦ ((hP j).tprod_left _).trans
    ((of_equiv ((Equiv.refl _).tprodCongr (e.exteriorPower _))).trans
      (tprod_exteriorPower P' (Nat.add_sub_cancel' hj)))


/-- The constituents of the exterior powers of a representation with a finite filtration
`0 = c₀ ≤ c₁ ≤ ⋯ ≤ c_t = A` only depend on the graded pieces: if `d` is another such filtration
of `B ⊆ V'` with equivalent graded pieces, every constituent of `⋀ⁿ A` is one of `⋀ⁿ B`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--2`,
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem exteriorPower_of_chain [FiniteDimensional k V] [FiniteDimensional k V'] {t : ℕ}
    (c : Fin (t + 1) → Subrepresentation ρ) (d : Fin (t + 1) → Subrepresentation σ)
    (hc : ∀ i : Fin t, c i.castSucc ≤ c i.succ) (hd : ∀ i : Fin t, d i.castSucc ≤ d i.succ)
    (hc0 : c 0 = ⊥) (hd0 : d 0 = ⊥)
    (e : ∀ i : Fin t, Nonempty
      (((c i.succ).subquotient (c i.castSucc)).Equiv ((d i.succ).subquotient (d i.castSucc))))
    (n : ℕ) : ConstituentsLE ((c (Fin.last t)).toRepresentation.exteriorPower n)
      ((d (Fin.last t)).toRepresentation.exteriorPower n) := by
  induction t generalizing n with
  | zero =>
    have hc' : c (Fin.last 0) = ⊥ := hc0
    have hd' : d (Fin.last 0) = ⊥ := hd0
    rw [hc', hd']
    rcases n with _ | n
    · exact of_equiv ((exteriorPowerZeroEquiv _).trans (exteriorPowerZeroEquiv _).symm)
    · have : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
        Submodule.subsingleton_iff_eq_bot.2 rfl
      exact exteriorPower_succ_of_subsingleton _ _ n
  | succ t ih =>
    let A := c (Fin.last (t + 1))
    let B := d (Fin.last (t + 1))
    let P := c (Fin.last t).castSucc
    let Q := d (Fin.last t).castSucc
    have hPA : P ≤ A := hc (Fin.last t)
    have hQB : Q ≤ B := hd (Fin.last t)
    have ih' := ih (fun i ↦ c i.castSucc) (fun i ↦ d i.castSucc) (fun i ↦ hc i.castSucc)
      (fun i ↦ hd i.castSucc) hc0 hd0 (fun i ↦ e i.castSucc)
    refine exteriorPower_of_subrepresentation (Subrepresentation.comap A.subtype P)
      (Subrepresentation.comap B.subtype Q) (fun j ↦ ?_) ?_ n
    · exact ((of_equiv ((Subrepresentation.comapSubtypeEquiv hPA).exteriorPower j)).trans
        (ih' j)).trans (of_equiv ((Subrepresentation.comapSubtypeEquiv hQB).exteriorPower j).symm)
    · exact ((Subrepresentation.quotientComapSubtypeEquiv P A).trans
        (e (Fin.last t)).some).trans (Subrepresentation.quotientComapSubtypeEquiv Q B).symm
end ConstituentsLE

end Representation

namespace Representation

open DirectSum

variable {k : Type*} [Field k] {W : Type*} [Group W] {t : ℕ} {V : Fin t → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] (ρs : ∀ i, Representation k W (V i))

/-- The filtration of a direct sum `⨁_{j < t} V j` by the partial sums `⨁_{j < i} V j`. -/
noncomputable def directSumFiltration (i : ℕ) : Subrepresentation (directSum ρs) :=
  (Finset.univ.filter fun j : Fin t ↦ (j : ℕ) < i).sup (directSumSummand ρs)

theorem directSumFiltration_zero : directSumFiltration ρs 0 = ⊥ := by
  simp [directSumFiltration]

theorem directSumFiltration_succ (i : Fin t) :
    directSumFiltration ρs (i + 1) = directSumSummand ρs i ⊔ directSumFiltration ρs i := by
  rw [directSumFiltration, directSumFiltration, ← Finset.sup_insert]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

theorem directSumFiltration_le_succ (i : ℕ) :
    directSumFiltration ρs i ≤ directSumFiltration ρs (i + 1) :=
  Finset.sup_mono fun j hj ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega

theorem directSumFiltration_eq_top : directSumFiltration ρs t = ⊤ := by
  have h : (Finset.univ.filter fun j : Fin t ↦ (j : ℕ) < t) = Finset.univ :=
    Finset.filter_true_of_mem fun j _ ↦ j.2
  rw [directSumFiltration, h, Finset.sup_univ_eq_iSup]
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_iSup, Subrepresentation.toSubmodule_top]
  exact (isInternal_directSumSummand ρs).submodule_iSup_eq_top

theorem disjoint_directSumFiltration (i : Fin t) :
    Disjoint (directSumSummand ρs i) (directSumFiltration ρs i) := by
  have hind := Subrepresentation.iSupIndep_toSubmodule_iff.1
    (isInternal_directSumSummand ρs).submodule_iSupIndep
  refine (hind i).mono_right (Finset.sup_le fun j hj ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact le_iSup₂_of_le j (fun h ↦ by subst h; omega) le_rfl

/-- The graded pieces of the partial-sum filtration of a direct sum are its summands. -/
noncomputable def directSumFiltrationEquiv (i : Fin t) :
    (ρs i).Equiv ((directSumFiltration ρs (i + 1)).subquotient (directSumFiltration ρs i)) :=
  ((directSumSummandEquiv ρs i).trans (Subrepresentation.subquotientBotEquiv _).symm).trans
    (Subrepresentation.subquotientEquivOfIntertwiningMap (.id _)
      (fun x hx ↦ by
        rw [directSumFiltration_succ]; exact le_sup_left (a := directSumSummand ρs i) hx)
      (fun x _ hx ↦ by
        rw [(Submodule.mem_bot k).1 hx]
        exact Submodule.zero_mem _)
      (fun x hx hx' ↦ by
        have := (disjoint_directSumFiltration ρs i).le_bot
          (Subrepresentation.mem_inf.2 ⟨hx, hx'⟩)
        exact this)
      fun y hy ↦ by
        rw [directSumFiltration_succ] at hy
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
        refine ⟨a, ha, ?_⟩
        rw [IntertwiningMap.id_apply, sub_add_cancel_left]
        exact Submodule.neg_mem _ hb)

end Representation

namespace Representation.CompositionSeries

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] {ρ : Representation k W V} (s : ρ.CompositionSeries)

omit [FiniteDimensional k V] in
private theorem series_zero : s.series 0 = ⊥ :=
  s.head_eq

omit [FiniteDimensional k V] in
private theorem exteriorPower_le_of_eq_top {V' : Type*} [AddCommGroup V'] [Module k V']
    {σ : Representation k W V'} {A : Subrepresentation σ} (hA : A = ⊤) (n : ℕ) :
    ConstituentsLE (σ.exteriorPower n) (A.toRepresentation.exteriorPower n) := by
  subst hA
  exact ConstituentsLE.of_equiv (Subrepresentation.topEquiv.symm.exteriorPower n)

omit [FiniteDimensional k V] in
private theorem exteriorPower_ge_of_eq_top {V' : Type*} [AddCommGroup V'] [Module k V']
    {σ : Representation k W V'} {A : Subrepresentation σ} (hA : A = ⊤) (n : ℕ) :
    ConstituentsLE (A.toRepresentation.exteriorPower n) (σ.exteriorPower n) := by
  subst hA
  exact ConstituentsLE.of_equiv (Subrepresentation.topEquiv.exteriorPower n)

/-- **The exterior powers of a representation and of its semisimplification have the same
constituents**, one direction: every constituent of `⋀ⁿ V` is a constituent of `⋀ⁿ V^ss`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--2`,
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem constituentsLE_exteriorPower_semisimplification (n : ℕ) :
    ConstituentsLE (ρ.exteriorPower n) (s.semisimplification.exteriorPower n) := by
  have h := ConstituentsLE.exteriorPower_of_chain s.series
    (fun i : Fin (s.length + 1) ↦ directSumFiltration (fun i ↦ s.factor i) i)
    (fun i ↦ (s.covBy i).le) (fun i ↦ directSumFiltration_le_succ _ _) s.series_zero
    (directSumFiltration_zero _) (fun i ↦ ⟨directSumFiltrationEquiv (fun i ↦ s.factor i) i⟩) n
  exact (exteriorPower_le_of_eq_top s.last_eq n).trans (h.trans
    (exteriorPower_ge_of_eq_top (directSumFiltration_eq_top _) n))

/-- **The exterior powers of a representation and of its semisimplification have the same
constituents**, the other direction: every constituent of `⋀ⁿ V^ss` is a constituent of `⋀ⁿ V`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--2`,
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
theorem constituentsLE_exteriorPower_semisimplification' (n : ℕ) :
    ConstituentsLE (s.semisimplification.exteriorPower n) (ρ.exteriorPower n) := by
  have h := ConstituentsLE.exteriorPower_of_chain
    (fun i : Fin (s.length + 1) ↦ directSumFiltration (fun i ↦ s.factor i) i) s.series
    (fun i ↦ directSumFiltration_le_succ _ _) (fun i ↦ (s.covBy i).le)
    (directSumFiltration_zero _) s.series_zero
    (fun i ↦ ⟨(directSumFiltrationEquiv (fun i ↦ s.factor i) i).symm⟩) n
  exact (exteriorPower_le_of_eq_top (directSumFiltration_eq_top _) n).trans (h.trans
    (exteriorPower_ge_of_eq_top s.last_eq n))

end Representation.CompositionSeries

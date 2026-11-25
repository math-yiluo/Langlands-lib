/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.ExteriorPowerFiltration

/-!
# The exterior powers of a direct sum of representations

For representations `V₁, …, V_s`, the exterior power of the direct sum decomposes canonically and
equivariantly as

$$
\textstyle\bigwedge^N \left(\bigoplus_i V_i\right) \cong
  \bigoplus_{n_1 + \cdots + n_s = N} \bigotimes_i \bigwedge^{n_i} V_i .
$$

The case of two summands comes from the filtration of `⋀^N (V ⊕ W)` by the number of entries in
`V` (`exteriorPower.countSpan`): the summand `W` gives an equivariant section of the quotient map,
so that the filtration splits. The general case follows by induction on `s`.

## Main results

- `LinearMap.bijective_toModule_of_antitone`: maps into the steps of a finite filtration which
  are bijective onto the graded pieces add up to a bijection from the direct sum.
- `Representation.exteriorPowerProdEquiv`: `⋀^N (V ⊕ W) ≃ ⨁_{j ≤ N} ⋀^j V ⊗ ⋀^{N-j} W`.
-/

@[expose] public section

open TensorProduct DirectSum

universe u v w

namespace LinearMap

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Let `F 0 = ⊤ ⊇ F 1 ⊇ ⋯ ⊇ F (N + 1) = 0` be a finite filtration, and `ψ j : M j → F j` linear
maps inducing bijections `M j ≃ F j / F (j + 1)`. Then `⨁ⱼ ψ j : ⨁ⱼ M j → V` is bijective. -/
theorem bijective_toModule_of_antitone {N : ℕ} (F : ℕ → Submodule k V) (hF : Antitone F)
    (h0 : F 0 = ⊤) (hN : F (N + 1) = ⊥) {M : Fin (N + 1) → Type*} [∀ j, AddCommGroup (M j)]
    [∀ j, Module k (M j)] (ψ : ∀ j, M j →ₗ[k] V) (hψ : ∀ (j : Fin (N + 1)) m, ψ j m ∈ F j)
    (hinj : ∀ (j : Fin (N + 1)) m, ψ j m ∈ F (j + 1) → m = 0)
    (hsurj : ∀ (j : Fin (N + 1)), ∀ x ∈ F j, ∃ m, x - ψ j m ∈ F (j + 1)) :
    Function.Bijective (toModule k (Fin (N + 1)) V ψ) := by
  classical
  have hΨ (m : ⨁ j, M j) : toModule k (Fin (N + 1)) V ψ m = ∑ j, ψ j (m j) := by
    conv_lhs => rw [← DirectSum.sum_univ_of m]
    simp only [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ toModule_lof k j (m j)
  refine ⟨(injective_iff_map_eq_zero _).2 fun m hm ↦ ?_, fun x ↦ ?_⟩
  · -- the components of `m` vanish, by induction
    have key (j : ℕ) : ∀ i : Fin (N + 1), (i : ℕ) < j → m i = 0 := by
      induction j with
      | zero => intro i hi; omega
      | succ j ih =>
        intro i hi
        rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | rfl
        · exact ih i hi
        · refine hinj i _ ?_
          have hsum : ψ i (m i) = -∑ i' ∈ Finset.univ.filter (fun i' ↦ i < i'), ψ i' (m i') := by
            rw [hΨ] at hm
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_eq_zero_iff_eq_neg] at hm
            rw [hm]
            congr 1
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (fun i' ↦ i < i')]
            rw [Finset.sum_eq_zero (s := (Finset.univ.erase i).filter fun i' ↦ ¬ i < i')
              fun i' hi' ↦ ?_, add_zero]
            · congr 1
              ext i'
              simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
              exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.ne', h⟩⟩
            · simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
                not_lt] at hi'
              rw [ih i' (lt_of_le_of_ne (Fin.le_iff_val_le_val.1 hi'.2)
                (Fin.val_ne_of_ne hi'.1)), map_zero]
          rw [hsum]
          refine neg_mem (Submodule.sum_mem _ fun i' hi' ↦ ?_)
          exact hF (Nat.succ_le_of_lt (Finset.mem_filter.1 hi').2) (hψ i' _)
    exact DFinsupp.ext fun i ↦ key (N + 1) i i.2
  · -- the steps of the filtration lie in the range, by downward induction
    have key (d : ℕ) : ∀ y ∈ F (N + 1 - d), y ∈ LinearMap.range (toModule k (Fin (N + 1)) V ψ) := by
      induction d with
      | zero =>
        intro y hy
        rw [Nat.sub_zero, hN, Submodule.mem_bot] at hy
        rw [hy]
        exact zero_mem _
      | succ d ih =>
        intro y hy
        by_cases hd : N + 1 ≤ d
        · exact ih y (by rw [show N + 1 - d = 0 by omega, h0]; exact Submodule.mem_top)
        let j : Fin (N + 1) := ⟨N + 1 - (d + 1), by omega⟩
        obtain ⟨m, hm⟩ := hsurj j y hy
        obtain ⟨m', hm'⟩ := ih _ (by
          have : (j : ℕ) + 1 = N + 1 - d := by simp only [j]; omega
          rw [← this]
          exact hm)
        refine ⟨m' + lof k _ M j m, ?_⟩
        rw [map_add, hm', toModule_lof, sub_add_cancel]
    obtain ⟨m, hm⟩ := key (N + 1) x (by rw [Nat.sub_self, h0]; exact Submodule.mem_top)
    exact ⟨m, hm⟩

end LinearMap

namespace Subrepresentation

variable {k : Type u} [Field k] {W : Type w} [Group W] {V : Type v} [AddCommGroup V]
  [Module k V] {ρ : Representation k W V} (P : Subrepresentation ρ)
  (s : V ⧸ P.toSubmodule →ₗ[k] V)

/-- For an equivariant section `s` of `V → V ⧸ P`, the map `⋀ʲ P ⊗ ⋀ˡ (V ⧸ P) → ⋀ⁿ V`,
`u ⊗ x̄ ↦ u ∧ s(x̄)`, is equivariant. -/
theorem wedgeSection_comp (hs : ∀ w x, s (P.quotient w x) = ρ w (s x)) {j l n : ℕ}
    (h : j + l = n) (w : W) :
    exteriorPower.wedgeSection n s h ∘ₗ ((P.toRepresentation.exteriorPower j).tprod
      (P.quotient.exteriorPower l) w) =
      ρ.exteriorPower n w ∘ₗ exteriorPower.wedgeSection n s h := by
  subst h
  refine TensorProduct.ext (exteriorPower.linearMap_ext (AlternatingMap.ext fun u ↦
    exteriorPower.linearMap_ext (AlternatingMap.ext fun x ↦ ?_)))
  simp only [LinearMap.compAlternatingMap_apply, Representation.tprod_apply]
  change exteriorPower.wedgeSection (j + l) s rfl
      (exteriorPower.map j (P.toRepresentation w) (exteriorPower.ιMulti k j u) ⊗ₜ
        exteriorPower.map l (P.quotient w) (exteriorPower.ιMulti k l x)) =
      exteriorPower.map (j + l) (ρ w) (exteriorPower.wedgeSection (j + l) s rfl
        (exteriorPower.ιMulti k j u ⊗ₜ exteriorPower.ιMulti k l x))
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
    exteriorPower.wedgeSection_tmul_ιMulti, exteriorPower.wedgeSection_tmul_ιMulti,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  refine Fin.addCases (fun c ↦ ?_) (fun b ↦ ?_) i
  · simp
    rfl
  · simp only [Fin.append_right, Function.comp_apply]
    exact hs w (x b)

variable [FiniteDimensional k V] (hsec : ∀ x, P.toSubmodule.mkQ (s x) = x)
  (hs : ∀ w x, s (P.quotient w x) = ρ w (s x))

/-- **An equivariant splitting of the exterior powers.** If the quotient map `V → V ⧸ P` has an
equivariant section `s`, then `⋀ᴺ V ≃ ⨁_{j ≤ N} ⋀ʲ P ⊗ ⋀ᴺ⁻ʲ (V ⧸ P)`, through
`u ⊗ x̄ ↦ u ∧ s(x̄)`. -/
noncomputable def exteriorPowerSplitEquiv (N : ℕ) :
    (Representation.directSum fun j : Fin (N + 1) ↦
      (P.toRepresentation.exteriorPower j).tprod (P.quotient.exteriorPower (N - j))).Equiv
      (ρ.exteriorPower N) :=
  .mk (.ofBijective (toModule k (Fin (N + 1)) _ fun j ↦
      exteriorPower.wedgeSection N s (Nat.add_sub_cancel' (Nat.lt_succ_iff.1 j.2)))
    (LinearMap.bijective_toModule_of_antitone (fun j ↦ exteriorPower.countSpan P.toSubmodule N j)
      (fun _ _ h ↦ exteriorPower.countSpan_anti _ N h) (exteriorPower.countSpan_zero _ N)
      (exteriorPower.countSpan_eq_bot _ N (Nat.lt_succ_self N)) _
      (fun j m ↦ exteriorPower.wedgeSection_mem_countSpan N s _ m)
      (fun j m hm ↦ (exteriorPower.toGraded_bijective N s hsec
        (Nat.add_sub_cancel' (Nat.lt_succ_iff.1 j.2))).1 (by
          rw [map_zero]
          exact (Submodule.Quotient.mk_eq_zero _).2 hm))
      fun j x hx ↦ by
        obtain ⟨m, hm⟩ := exteriorPower.toGraded_surjective N hsec
          (Nat.add_sub_cancel' (Nat.lt_succ_iff.1 j.2)) (Submodule.Quotient.mk ⟨x, hx⟩)
        refine ⟨m, ?_⟩
        have := (Submodule.Quotient.eq _).1 hm
        rw [← neg_sub]
        exact neg_mem this)) fun w ↦ by
    refine DirectSum.linearMap_ext k fun j ↦ LinearMap.ext fun y ↦ ?_
    have h1 : Representation.directSum (fun j : Fin (N + 1) ↦
        (P.toRepresentation.exteriorPower j).tprod (P.quotient.exteriorPower (N - j))) w
          (lof k _ _ j y) = lof k _ _ j (((P.toRepresentation.exteriorPower j).tprod
            (P.quotient.exteriorPower (N - j))) w y) := by
      simp [Representation.directSum]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.ofBijective_apply]
    rw [h1, toModule_lof, toModule_lof]
    exact LinearMap.congr_fun (wedgeSection_comp P s hs _ w) y

end Subrepresentation

namespace Representation

variable {k : Type u} [Field k] {W : Type w} [Group W] {X Y : Type v} [AddCommGroup X]
  [Module k X] [AddCommGroup Y] [Module k Y] (ρ : Representation k W X)
  (σ : Representation k W Y)

/-- The summand `X` of `X × Y`, as a subrepresentation of `ρ.prod σ`. -/
noncomputable abbrev prodFst : Subrepresentation (ρ.prod σ) :=
  (IntertwiningMap.inl k ρ σ).range

/-- The summand `X` of `X × Y` is equivalent to `ρ`. -/
noncomputable def prodFstEquiv : (prodFst ρ σ).toRepresentation.Equiv ρ :=
  (Equiv.mk (LinearEquiv.ofInjective (LinearMap.inl k X Y) LinearMap.inl_injective) fun w ↦
    LinearMap.ext fun x ↦ Subtype.ext (by
      change LinearMap.inl k X Y (ρ w x) = (ρ.prod σ) w (LinearMap.inl k X Y x)
      simp)).symm

/-- The quotient of `X × Y` by `X` is equivalent to `σ`. -/
noncomputable def prodFstQuotientEquiv : (prodFst ρ σ).quotient.Equiv σ :=
  .mk ((Submodule.quotEquivOfEq _ _ (LinearMap.range_inl k X Y)).trans
    (LinearMap.quotKerEquivOfSurjective _ LinearMap.snd_surjective)) fun _ ↦
    Submodule.linearMap_qext _ (LinearMap.ext fun _ ↦ rfl)

/-- The section `x̄ ↦ (0, snd x)` of the quotient map `X × Y → (X × Y) ⧸ X`. -/
noncomputable def prodFstSection : (X × Y) ⧸ (prodFst ρ σ).toSubmodule →ₗ[k] X × Y :=
  LinearMap.inr k X Y ∘ₗ (prodFstQuotientEquiv ρ σ).toLinearEquiv.toLinearMap

theorem mkQ_prodFstSection (x : (X × Y) ⧸ (prodFst ρ σ).toSubmodule) :
    (prodFst ρ σ).toSubmodule.mkQ (prodFstSection ρ σ x) = x := by
  induction x using Submodule.Quotient.induction_on with | _ z
  rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-z.1, ?_⟩
  have h2 : prodFstQuotientEquiv ρ σ (Submodule.Quotient.mk z) = z.2 := rfl
  ext
  · simp [prodFstSection]
    rfl
  · simp [prodFstSection, h2]
    rfl

theorem prodFstSection_apply (w : W) (x : (X × Y) ⧸ (prodFst ρ σ).toSubmodule) :
    prodFstSection ρ σ ((prodFst ρ σ).quotient w x) = (ρ.prod σ) w (prodFstSection ρ σ x) := by
  induction x using Submodule.Quotient.induction_on with | _ z
  simp [prodFstSection, prodFstQuotientEquiv, Prod.ext_iff]
  rfl

variable [FiniteDimensional k X] [FiniteDimensional k Y]

/-- **The exterior powers of a direct sum of two representations**:
`⋀ᴺ (X ⊕ Y) ≃ ⨁_{j ≤ N} ⋀ʲ X ⊗ ⋀ᴺ⁻ʲ Y`, through `u ⊗ y ↦ u ∧ y`.
(blueprint: `lemma-tensor-exterior-powers-filtered-representations--3`) -/
noncomputable def exteriorPowerProdEquiv (N : ℕ) :
    ((ρ.prod σ).exteriorPower N).Equiv
      (directSum fun j : Fin (N + 1) ↦ (ρ.exteriorPower j).tprod (σ.exteriorPower (N - j))) :=
  ((prodFst ρ σ).exteriorPowerSplitEquiv (prodFstSection ρ σ) (mkQ_prodFstSection ρ σ)
    (prodFstSection_apply ρ σ) N).symm.trans
    (Equiv.directSumCongr (.refl _) fun j ↦ (((prodFstEquiv ρ σ).exteriorPower j).tprodCongr
      ((prodFstQuotientEquiv ρ σ).exteriorPower (N - j))).symm)

end Representation

namespace Representation

section DirectSumEquiv

variable {k : Type*} [Field k] {W : Type*} [Group W]

/-- Tensor products distribute over direct sums of representations. -/
noncomputable def directSumTprodEquiv {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] {N : Type*} [AddCommGroup N] [Module k N]
    (τs : ∀ i, Representation k W (M i)) (σ : Representation k W N) :
    ((directSum τs).tprod σ).Equiv (directSum fun i ↦ (τs i).tprod σ) :=
  .mk (TensorProduct.directSumLeft k k M N) fun w ↦ by
    refine TensorProduct.ext' fun x y ↦ ?_
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, tprod_apply,
        TensorProduct.map_tmul, directSum_apply]
      rw [← DirectSum.lof_eq_of k, DirectSum.lmap_lof, TensorProduct.directSumLeft_tmul_lof,
        TensorProduct.directSumLeft_tmul_lof, DirectSum.lmap_lof]
      rfl
    | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']

/-- A direct sum over a sigma type is an iterated direct sum. -/
noncomputable def directSumSigmaEquiv {ι : Type*} [DecidableEq ι] {κ : ι → Type*}
    [∀ i, DecidableEq (κ i)] {M : ∀ i, κ i → Type*} [∀ i j, AddCommGroup (M i j)]
    [∀ i j, Module k (M i j)] (τ : ∀ i j, Representation k W (M i j)) :
    (directSum fun x : Σ i, κ i ↦ τ x.1 x.2).Equiv (directSum fun i ↦ directSum (τ i)) :=
  .mk (DirectSum.sigmaLcurryEquiv k) fun _ ↦ LinearMap.ext fun _ ↦
    DFinsupp.ext fun _ ↦ DFinsupp.ext fun _ ↦ rfl

/-- A direct sum over `Fin (s + 1)` splits off its last summand. -/
noncomputable def directSumFinSuccEquiv {s : ℕ} {V : Fin (s + 1) → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] (ρs : ∀ i, Representation k W (V i)) :
    (directSum ρs).Equiv ((directSum fun i : Fin s ↦ ρs i.castSucc).prod (ρs (Fin.last s))) := by
  let f : (⨁ i, V i) →ₗ[k] (⨁ i : Fin s, V i.castSucc) × V (Fin.last s) :=
    toModule k _ _ fun i ↦ Fin.lastCases (motive := fun i ↦ V i →ₗ[k] _) (LinearMap.inr k _ _)
      (fun j ↦ LinearMap.inl k _ _ ∘ₗ lof k _ (fun j : Fin s ↦ V j.castSucc) j) i
  let g : ((⨁ i : Fin s, V i.castSucc) × V (Fin.last s)) →ₗ[k] ⨁ i, V i :=
    LinearMap.coprod (toModule k _ _ fun j ↦ lof k _ V j.castSucc) (lof k _ V (Fin.last s))
  have hfc (j : Fin s) (x : V j.castSucc) : f (lof k _ V j.castSucc x) =
      (lof k _ (fun j : Fin s ↦ V j.castSucc) j x, 0) := by
    simp [f, toModule_lof]
  have hfl (y : V (Fin.last s)) : f (lof k _ V (Fin.last s) y) = (0, y) := by
    simp [f, toModule_lof]
  refine .mk (.ofLinearMap f g ?_ ?_) fun w ↦ ?_
  · refine LinearMap.prod_ext (DirectSum.linearMap_ext k fun j ↦ LinearMap.ext fun x ↦ ?_)
      (LinearMap.ext fun y ↦ ?_)
    · simp [g, toModule_lof, hfc]
    · simp [g, hfl]
  · refine DirectSum.linearMap_ext k fun i ↦ LinearMap.ext fun x ↦ ?_
    induction i using Fin.lastCases with
    | last => simp [g, hfl]
    | cast j => simp [g, hfc, toModule_lof]
  · refine DirectSum.linearMap_ext k fun i ↦ LinearMap.ext fun x ↦ ?_
    induction i using Fin.lastCases with
    | last =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_ofLinearMap, directSum_apply, DirectSum.lmap_lof, hfl]
      simp
    | cast j =>
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_ofLinearMap, directSum_apply, DirectSum.lmap_lof, hfc]
      simp

/-- A direct sum over a type with a unique element is its summand. -/
noncomputable def directSumUniqueEquiv {ι : Type*} [Unique ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] (τs : ∀ i, Representation k W (M i)) :
    (directSum τs).Equiv (τs default) :=
  .mk (.ofLinearMap (component k ι M default) (lof k ι M default)
    (LinearMap.ext fun x ↦ by simp)
    (DirectSum.linearMap_ext k fun i ↦ LinearMap.ext fun x ↦ by
      obtain rfl := Subsingleton.elim i default
      simp)) fun w ↦ LinearMap.ext fun x ↦ rfl

end DirectSumEquiv

/-- The tuples `(n₁, …, n_{s+1})` with sum `N` are the pairs of `j ≤ N` and a tuple
`(n₁, …, n_s)` with sum `j`, the last entry being `N - j`. -/
def finSuccSumEquiv (s N : ℕ) :
    {n : Fin (s + 1) → ℕ // ∑ i, n i = N} ≃ Σ j : Fin (N + 1), {n : Fin s → ℕ // ∑ i, n i = j} where
  toFun n := ⟨⟨∑ i : Fin s, n.1 i.castSucc, by
    have := n.2
    rw [Fin.sum_univ_castSucc] at this
    omega⟩, ⟨fun i ↦ n.1 i.castSucc, rfl⟩⟩
  invFun x := ⟨Fin.snoc (α := fun _ ↦ ℕ) x.2.1 (N - x.1), by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, x.2.2]
    have := x.1.2
    omega⟩
  left_inv n := by
    refine Subtype.ext (funext fun i ↦ ?_)
    induction i using Fin.lastCases with
    | last =>
      have := n.2
      rw [Fin.sum_univ_castSucc] at this
      simp only [Fin.snoc_last]
      omega
    | cast j => simp
  right_inv x := by
    refine Sigma.subtype_ext (Fin.ext ?_) ?_
    · simp [x.2.2]
    · simp

variable {k : Type u} [Field k] {W : Type w} [Group W]

/-- **The exterior powers of a direct sum.** For finite-dimensional representations
`V₁, …, V_s`, there is a canonical equivariant decomposition
`⋀ᴺ (⨁ᵢ Vᵢ) ≃ ⨁_{n₁ + ⋯ + n_s = N} ⨂ᵢ ⋀^{nᵢ} Vᵢ`; the terms with `nᵢ > dim Vᵢ` are zero
(`nontrivial_piTensorProduct_exteriorPower_iff`). (blueprint:
`lemma-tensor-exterior-powers-filtered-representations--3`) -/
noncomputable def exteriorPowerDirectSumEquiv : ∀ {s : ℕ} {V : Fin s → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (ρs : ∀ i, Representation k W (V i)) (N : ℕ),
    ((directSum ρs).exteriorPower N).Equiv
      (directSum fun n : {n : Fin s → ℕ // ∑ i, n i = N} ↦ piTprodExteriorPower ρs n.1)
  | 0, V, _, _, _, ρs, 0 => by
    let : Unique {n : Fin 0 → ℕ // ∑ i, n i = 0} :=
      { default := ⟨Fin.elim0, rfl⟩, uniq := fun a ↦ Subtype.ext (funext fun i ↦ i.elim0) }
    exact ((exteriorPowerZeroEquiv _).trans (piTprodIsEmptyEquiv
      (fun i ↦ (ρs i).exteriorPower ((default : {n : Fin 0 → ℕ // ∑ i, n i = 0}).1 i))).symm).trans
      (directSumUniqueEquiv (fun n : {n : Fin 0 → ℕ // ∑ i, n i = 0} ↦
        piTprodExteriorPower ρs n.1)).symm
  | 0, V, _, _, _, ρs, N + 1 => by
    have : Subsingleton (⨁ i : Fin 0, V i) := inferInstance
    have : Subsingleton (⋀[k]^(N + 1) (⨁ i : Fin 0, V i)) := by
      rw [← Module.finrank_zero_iff (R := k), exteriorPower.finrank_eq,
        Module.finrank_zero_of_subsingleton, Nat.choose_zero_succ]
    have : IsEmpty {n : Fin 0 → ℕ // ∑ i, n i = N + 1} := ⟨fun n ↦ by simpa using n.2⟩
    exact .mk (LinearEquiv.ofSubsingleton _ _) fun _ ↦ LinearMap.ext fun _ ↦
      Subsingleton.elim _ _
  | s + 1, V, _, _, _, ρs, N => by
    let A := directSum fun i : Fin s ↦ ρs i.castSucc
    let B := ρs (Fin.last s)
    exact ((((directSumFinSuccEquiv ρs).exteriorPower N).trans
      (exteriorPowerProdEquiv A B N)).trans
      (((Equiv.directSumCongr (_root_.Equiv.refl (Fin (N + 1))) fun j ↦
        ((exteriorPowerDirectSumEquiv (fun i : Fin s ↦ ρs i.castSucc) j).tprodCongr
          (.refl _)).symm).trans (Equiv.directSumCongr (_root_.Equiv.refl (Fin (N + 1))) fun j ↦
            (directSumTprodEquiv _ _).symm)).trans
        (directSumSigmaEquiv fun (j : Fin (N + 1)) (n : {n : Fin s → ℕ // ∑ i, n i = j}) ↦
          (piTprodExteriorPower (fun i : Fin s ↦ ρs i.castSucc) n.1).tprod
            (B.exteriorPower (N - j))).symm)).trans
      (Equiv.directSumCongr (σs := fun x : Σ j : Fin (N + 1), {n : Fin s → ℕ // ∑ i, n i = j} ↦
        (piTprodExteriorPower (fun i : Fin s ↦ ρs i.castSucc) x.2.1).tprod
          (B.exteriorPower (N - x.1))) (finSuccSumEquiv s N) fun n ↦
        (piTprodExteriorPowerSuccEquiv ρs n.1).trans (Equiv.tprodCongr (.refl _)
          (exteriorPowerCongr _ (by
            have := n.2
            rw [Fin.sum_univ_castSucc] at this
            change n.1 (Fin.last s) = N - ∑ i : Fin s, n.1 i.castSucc
            omega))))

end Representation

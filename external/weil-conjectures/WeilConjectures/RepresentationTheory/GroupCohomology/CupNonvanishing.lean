/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Nonvanishing of group cohomology of free abelian groups

Let `G` be a commutative group, `k` a nontrivial commutative ring, and suppose there are
homomorphisms `a₁, …, aₙ : G → k` and elements `e₁, …, eₙ ∈ G` with `aᵢ(eⱼ) = δᵢⱼ`. Then
`Hⁿ(G, k) ≠ 0` for the trivial representation `k`
(`groupCohomology.not_isZero_of_dualFamily`). This applies to `G ≅ ℤⁿ` and to `G ≅ ⊕_ℕ ℤ` in
every degree, which is the group-cohomological input `Hⁿ(⊕_ℕ ℤ, Λ) ≠ 0` of blueprint
`sk-rem-sf-fullcd-scope`.

The proof avoids the Künneth formula. The cup product `a₁ ∪ ⋯ ∪ aₙ`, `(g₁, …, gₙ) ↦ ∏ aᵢ(gᵢ)`,
is a cocycle (a telescoping sum). The alternating pairing
`c ↦ ∑_σ sign σ · c(e_{σ 1}, …, e_{σ n})` with the "fundamental cycle" of the `eᵢ` kills
coboundaries: the inner faces cancel in pairs `σ, σ ∘ (j j+1)` because `G` is commutative,
and the two outer faces cancel after a cyclic rotation. It takes the value `1` on the cup
product.
-/

@[expose] public section

universe u

open CategoryTheory groupCohomology

namespace groupCohomology

variable {k G : Type u} [CommRing k] [CommGroup G]

/-- The alternating pairing of an `n`-cochain with the "fundamental cycle"
`∑_σ sign σ [e_{σ 0} | ⋯ | e_{σ (n-1)}]` of a family `e` of elements of `G`. -/
def altPairing {n : ℕ} (e : Fin n → G) (f : (Fin n → G) → k) : k :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) * f (e ∘ σ)

/-- A signed sum over permutations of a function invariant under right multiplication by a
transposition vanishes. -/
lemma sum_sign_mul_eq_zero {n : ℕ} (F : Equiv.Perm (Fin n) → k) {a b : Fin n} (hab : a ≠ b)
    (hF : ∀ σ, F (σ * Equiv.swap a b) = F σ) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : k) * F σ = 0 := by
  refine Finset.sum_involution (fun σ _ ↦ σ * Equiv.swap a b) (fun σ _ ↦ ?_) (fun σ _ _ ↦ ?_)
    (fun _ _ ↦ Finset.mem_univ _) (fun σ _ ↦ by simp [mul_assoc])
  · rw [hF, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
    push_cast
    ring
  · intro h
    have := congrArg (fun τ ↦ σ⁻¹ * τ) h
    simp only [inv_mul_cancel_left, inv_mul_cancel] at this
    exact hab (Equiv.swap_eq_one_iff.1 this)

lemma d_trivial_apply {n : ℕ} (b : (Fin n → G) → k) (g : Fin (n + 1) → G) :
    (inhomogeneousCochains.d (Rep.trivial k G k) n).hom b g =
      b (fun i ↦ g i.succ) + ∑ j : Fin (n + 1),
        (-1 : k) ^ ((j : ℕ) + 1) * b (Fin.contractNth j (· * ·) g) := by
  simp [inhomogeneousCochains.d_hom_apply]

/-- Contracting the positions `j, j + 1` of a tuple does not change under swapping them, in a
commutative group. -/
lemma contractNth_comp_swap {n : ℕ} (j : Fin n) (g : Fin (n + 1) → G) :
    Fin.contractNth j.castSucc (· * ·) (g ∘ Equiv.swap j.castSucc j.succ) =
      Fin.contractNth j.castSucc (· * ·) g := by
  funext i
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h),
      Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h), Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne]
    · exact fun h' ↦ by simp [Fin.ext_iff] at h'; omega
    · exact fun h' ↦ by simp [Fin.ext_iff] at h'; omega
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h),
      Fin.contractNth_apply_of_eq _ _ _ _ (by simpa using h), Function.comp_apply,
      Function.comp_apply]
    have hi : i = j := Fin.ext h
    subst hi
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h),
      Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h), Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne]
    · exact fun h' ↦ by simp [Fin.ext_iff] at h'; omega
    · exact fun h' ↦ by simp [Fin.ext_iff] at h'; omega

lemma contractNth_last {n : ℕ} (g : Fin (n + 1) → G) :
    Fin.contractNth (Fin.last n) (· * ·) g = fun i ↦ g i.castSucc := by
  funext i
  exact Fin.contractNth_apply_of_lt _ _ _ _ (by simp)

/-- The alternating pairing kills coboundaries. -/
theorem altPairing_d {n : ℕ} (e : Fin (n + 1) → G) (b : (Fin n → G) → k) :
    altPairing e ((inhomogeneousCochains.d (Rep.trivial k G k) n).hom b) = 0 := by
  unfold altPairing
  rw [Finset.sum_congr rfl fun σ _ ↦ by rw [d_trivial_apply b (e ∘ σ)]]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm, Fin.sum_univ_castSucc]
  -- the inner faces cancel in pairs
  have hinner : ∀ j : Fin n, ∑ σ : Equiv.Perm (Fin (n + 1)),
      ((Equiv.Perm.sign σ : ℤ) : k) * ((-1 : k) ^ ((j.castSucc : ℕ) + 1) *
        b (Fin.contractNth j.castSucc (· * ·) (e ∘ σ))) = 0 := by
    intro j
    simp_rw [mul_left_comm _ ((-1 : k) ^ _), ← Finset.mul_sum]
    rw [sum_sign_mul_eq_zero (fun σ ↦ b (Fin.contractNth j.castSucc (· * ·) (e ∘ σ)))
      (a := j.castSucc) (b := j.succ) (Fin.castSucc_lt_succ).ne fun σ ↦ ?_, mul_zero]
    simp only [Equiv.Perm.coe_mul]
    rw [← Function.comp_assoc, contractNth_comp_swap]
  simp only [hinner, Finset.sum_const_zero, zero_add, contractNth_last]
  -- the outer faces cancel after a cyclic rotation
  rw [add_comm, ← Equiv.sum_comp (Equiv.mulRight (finRotate (n + 1)))]
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, sign_finRotate, Equiv.Perm.coe_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun σ _ ↦ ?_
  have hrot : (fun i : Fin n ↦ (e ∘ σ ∘ finRotate (n + 1)) i.castSucc) =
      fun i ↦ (e ∘ σ) i.succ := by
    funext i
    simp [finRotate_apply, Fin.coeSucc_eq_succ]
  rw [hrot]
  have h1 : (-1 : k) ^ n * (-1) ^ (n + 1) = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨n, by ring⟩
  push_cast [Fin.val_last, Nat.add_sub_cancel]
  linear_combination ((Equiv.Perm.sign σ : ℤ) : k) * (b fun i ↦ (e ∘ σ) i.succ) * h1

/-- The cup product `a₀ ∪ ⋯ ∪ a_{n-1}` of homomorphisms `aᵢ : G → k`, as an `n`-cochain with
values in the trivial representation: `(g₀, …, g_{n-1}) ↦ ∏ aᵢ(gᵢ)`. -/
def cupHom {n : ℕ} (a : Fin n → Additive G →+ k) : (Fin n → G) → k :=
  fun g ↦ ∏ i, a i (Additive.ofMul (g i))

/-- The partial products `T m = ∏ᵢ aᵢ(g_{i or i+1})`, taking `gᵢ` for `i < m` and `g_{i+1}` for
`i ≥ m`, through which the coboundary of the cup product telescopes. -/
def cupPartial {n : ℕ} (a : Fin n → Additive G →+ k) (g : Fin (n + 1) → G) (m : ℕ) : k :=
  ∏ i : Fin n, a i (Additive.ofMul (g (if (i : ℕ) < m then i.castSucc else i.succ)))

lemma cupHom_contractNth_castSucc {n : ℕ} (a : Fin n → Additive G →+ k) (g : Fin (n + 1) → G)
    (j : Fin n) :
    cupHom a (Fin.contractNth j.castSucc (· * ·) g) =
      cupPartial a g (j + 1) + cupPartial a g j := by
  unfold cupHom cupPartial
  rw [Fintype.prod_eq_mul_prod_compl j, Fintype.prod_eq_mul_prod_compl j,
    Fintype.prod_eq_mul_prod_compl j, Fin.contractNth_apply_of_eq _ _ _ _ (by simp),
    ofMul_mul, map_add, add_mul]
  congr 1
  · rw [ite_eq_left (by omega)]
    congr 1
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    have hi : i ≠ j := by simpa using hi
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hi) with h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h), ite_eq_left (by omega)]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h), ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]
    congr 1
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    have hi : i ≠ j := by simpa using hi
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hi) with h | h
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simpa using h), ite_eq_left (by omega)]
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simpa using h), ite_eq_right (by omega)]

/-- The cup product of homomorphisms is a cocycle. -/
theorem d_cupHom {n : ℕ} (a : Fin n → Additive G →+ k) :
    (inhomogeneousCochains.d (Rep.trivial k G k) n).hom (cupHom a) = 0 := by
  funext g
  change _ = (0 : k)
  rw [d_trivial_apply, Fin.sum_univ_castSucc, contractNth_last]
  simp only [cupHom_contractNth_castSucc, Fin.val_castSucc, Fin.val_last]
  have h0 : cupHom a (fun i ↦ g i.succ) = cupPartial a g 0 := by
    simp [cupHom, cupPartial]
  have hn : cupHom a (fun i ↦ g i.castSucc) = cupPartial a g n := by
    simp only [cupHom, cupPartial]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [ite_eq_left i.isLt]
  rw [h0, hn]
  have htel : ∑ j : Fin n, (-1 : k) ^ ((j : ℕ) + 1) *
      (cupPartial a g (j + 1) + cupPartial a g j) =
      (-1) ^ n * cupPartial a g n - cupPartial a g 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ (-1 : k) ^ (j + 1) *
      (cupPartial a g (j + 1) + cupPartial a g j)) n]
    have := Finset.sum_range_sub (fun m ↦ (-1 : k) ^ m * cupPartial a g m) n
    simp only [pow_zero, one_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [htel]
  ring

/-- The alternating pairing of the fundamental cycle of a dual family with the cup product of
the dual homomorphisms is `1`. -/
theorem altPairing_cupHom {n : ℕ} (e : Fin n → G) (a : Fin n → Additive G →+ k)
    (h : ∀ i j, a i (Additive.ofMul (e j)) = if i = j then 1 else 0) :
    altPairing e (cupHom a) = 1 := by
  unfold altPairing cupHom
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp [h]
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra! H
      exact hσ (Equiv.ext H)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h, Ne.symm hi]), mul_zero]
  · simp

/-- **Nonvanishing of `Hⁿ(G, k)`.** Let `G` be a commutative group and `k` a nontrivial
commutative ring. If there are homomorphisms `aᵢ : G → k` and elements `eⱼ ∈ G`, `i, j < n`, with
`aᵢ(eⱼ) = δᵢⱼ`, then `Hⁿ(G, k) ≠ 0` for the trivial representation `k`: the cup product
`a₀ ∪ ⋯ ∪ a_{n-1}` is a cocycle whose alternating pairing with the fundamental cycle of the `eⱼ` is
`1`, while that pairing kills coboundaries. -/
theorem not_isZero_of_dualFamily [Nontrivial k] {n : ℕ} (e : Fin (n + 1) → G)
    (a : Fin (n + 1) → Additive G →+ k)
    (h : ∀ i j, a i (Additive.ofMul (e j)) = if i = j then 1 else 0) :
    ¬ Limits.IsZero (groupCohomology (Rep.trivial k G k) (n + 1)) := by
  intro hZ
  have hex := ((inhomogeneousCochains (Rep.trivial k G k)).exactAt_iff_isZero_homology
    (n + 1)).2 hZ
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  have key : ∀ x : (Fin (n + 1) → G) → k,
      (inhomogeneousCochains.d (Rep.trivial k G k) (n + 1)).hom x = 0 →
        ∃ y, (inhomogeneousCochains.d (Rep.trivial k G k) n).hom y = x := by
    intro x hx
    have hg : (HomologicalComplex.sc' (inhomogeneousCochains (Rep.trivial k G k)) n (n + 1)
        (n + 2)).g = inhomogeneousCochains.d (Rep.trivial k G k) (n + 1) :=
      inhomogeneousCochains.d_def _ (n + 1)
    have hf : (HomologicalComplex.sc' (inhomogeneousCochains (Rep.trivial k G k)) n (n + 1)
        (n + 2)).f = inhomogeneousCochains.d (Rep.trivial k G k) n :=
      inhomogeneousCochains.d_def _ n
    obtain ⟨y, hy⟩ := hex x (by rw [hg]; exact hx)
    exact ⟨y, by rw [hf] at hy; exact hy⟩
  obtain ⟨b, hb'⟩ := key (cupHom a) (d_cupHom a)
  have := altPairing_d e b
  rw [hb', altPairing_cupHom e a h] at this
  exact one_ne_zero this

/-- `Hⁿ(⊕_ι ℤ, k) ≠ 0` in every positive degree for an infinite index type `ι` and a nontrivial
commutative ring `k`, with trivial action; in particular `Hⁿ(⊕_ℕ ℤ, Λ) ≠ 0` for `n ≥ 1`, the
group-cohomological input of blueprint `sk-rem-sf-fullcd-scope`. -/
theorem not_isZero_groupCohomology_finsupp [Nontrivial k] (ι : Type u) [Infinite ι] (n : ℕ) :
    ¬ Limits.IsZero
      (groupCohomology (Rep.trivial k (Multiplicative (ι →₀ ℤ)) k) (n + 1)) := by
  let f : ℕ ↪ ι := Infinite.natEmbedding ι
  refine not_isZero_of_dualFamily (fun j ↦ Multiplicative.ofAdd (Finsupp.single (f j) 1))
    (fun i ↦ (Int.castAddHom k).comp ((Finsupp.applyAddHom (f i)).comp
      (AddEquiv.additiveMultiplicative _).toAddMonoidHom)) fun i j ↦ ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.applyAddHom_apply,
    Int.coe_castAddHom]
  change ((Finsupp.single (f j) (1 : ℤ) (f i) : ℤ) : k) = _
  by_cases hij : i = j
  · subst hij; simp
  · classical
    rw [Finsupp.single_apply, ite_eq_right (fun h ↦ hij (Fin.ext (f.injective h).symm)),
      ite_eq_right hij]
    simp

/-- The differential of inhomogeneous cochains is precomposition with the differential of the bar
resolution, under `Rep.freeLiftLEquiv`. -/
lemma freeLiftLEquiv_d_comp {n : ℕ} (A : Rep.{u} k G)
    (g : (Rep.barComplex k G).X n ⟶ A) :
    Rep.freeLiftLEquiv k G (Fin (n + 1) → G) A ((Rep.barComplex k G).d (n + 1) n ≫ g) =
      (inhomogeneousCochains.d A n).hom (Rep.freeLiftLEquiv k G (Fin n → G) A g) := by
  rw [inhomogeneousCochains.d_eq]
  simp
  rfl

/-- The `Ext`-form of `groupCohomology.not_isZero_of_dualFamily`: for a dual family as there,
`Extⁿ(k, k) ≠ 0` in `Rep k G`. The class of the cup product, computed on the bar resolution
(`CategoryTheory.ProjectiveResolution.extMk`), is nonzero: by
`CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff` it would otherwise be a coboundary. -/
theorem exists_ext_ne_zero_of_dualFamily.{w} [Nontrivial k] [HasExt.{w} (Rep.{u} k G)] {n : ℕ}
    (e : Fin (n + 1) → G) (a : Fin (n + 1) → Additive G →+ k)
    (h : ∀ i j, a i (Additive.ofMul (e j)) = if i = j then 1 else 0) :
    ∃ x : Abelian.Ext (Rep.trivial k G k) (Rep.trivial k G k) (n + 1), x ≠ 0 := by
  let R := Rep.barResolution k G
  let E := Rep.freeLiftLEquiv k G (Fin (n + 1) → G) (Rep.trivial k G k)
  let f : (Rep.barComplex k G).X (n + 1) ⟶ Rep.trivial k G k := E.symm (cupHom a)
  have hf : R.complex.d (n + 2) (n + 1) ≫ f = 0 := by
    apply (Rep.freeLiftLEquiv k G (Fin (n + 1 + 1) → G) (Rep.trivial k G k)).injective
    change Rep.freeLiftLEquiv k G (Fin (n + 1 + 1) → G) (Rep.trivial k G k)
      ((Rep.barComplex k G).d (n + 1 + 1) (n + 1) ≫ f) = _
    rw [freeLiftLEquiv_d_comp (n := n + 1), LinearEquiv.apply_symm_apply, d_cupHom, map_zero]
  refine ⟨R.extMk f (n + 2) rfl hf, fun h0 ↦ ?_⟩
  obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).1 h0
  have := altPairing_d e (Rep.freeLiftLEquiv k G (Fin n → G) (Rep.trivial k G k) g)
  rw [← freeLiftLEquiv_d_comp] at this
  change altPairing e (E ((Rep.barComplex k G).d (n + 1) n ≫ g)) = 0 at this
  change (Rep.barComplex k G).d (n + 1) n ≫ g = f at hg
  rw [hg, LinearEquiv.apply_symm_apply, altPairing_cupHom e a h] at this
  exact one_ne_zero this

/-- The `Ext`-form of `groupCohomology.not_isZero_groupCohomology_finsupp`:
`Extⁿ(k, k) ≠ 0` in `Rep k (⊕_ι ℤ)` for `n ≥ 1` and an infinite index type `ι`. -/
theorem exists_ext_ne_zero_finsupp.{w} [Nontrivial k] (ι : Type u) [Infinite ι]
    [HasExt.{w} (Rep.{u} k (Multiplicative (ι →₀ ℤ)))] (n : ℕ) :
    ∃ x : Abelian.Ext (Rep.trivial k (Multiplicative (ι →₀ ℤ)) k)
      (Rep.trivial k (Multiplicative (ι →₀ ℤ)) k) (n + 1), x ≠ 0 := by
  let f : ℕ ↪ ι := Infinite.natEmbedding ι
  refine exists_ext_ne_zero_of_dualFamily (fun j ↦ Multiplicative.ofAdd (Finsupp.single (f j) 1))
    (fun i ↦ (Int.castAddHom k).comp ((Finsupp.applyAddHom (f i)).comp
      (AddEquiv.additiveMultiplicative _).toAddMonoidHom)) fun i j ↦ ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.applyAddHom_apply,
    Int.coe_castAddHom]
  change ((Finsupp.single (f j) (1 : ℤ) (f i) : ℤ) : k) = _
  by_cases hij : i = j
  · subst hij; simp
  · classical
    rw [Finsupp.single_apply, ite_eq_right (fun h ↦ hij (Fin.ext (f.injective h).symm)),
      ite_eq_right hij]
    simp

end groupCohomology

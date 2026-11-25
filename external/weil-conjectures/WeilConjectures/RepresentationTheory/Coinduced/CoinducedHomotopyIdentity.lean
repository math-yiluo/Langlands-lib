/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.Coinduced.CoinducedHomotopyContinuous
import Mathlib.Tactic.Abel

/-!
# The coinduced contraction satisfies the homotopy identity

Source: Stacks Project, etale-cohomology.tex, Tag 0DVG,
label section-continuous-group-cohomology, final profinite comparison
(blueprint: lem-exc-coinduced-homotopy-identity).
-/

@[expose] public section

universe u v w

namespace Rep

private def curryLocallyConstant
    {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (F : LocallyConstant (X × Y) V) : LocallyConstant X (LocallyConstant Y V) where
  toFun x := ⟨fun y ↦ F (x, y),
    F.isLocallyConstant.comp_continuous (continuous_const.prodMk continuous_id)⟩
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hf₀ : IsLocallyConstant (fun p : X × Y ↦ F (x, p.2)) :=
      F.isLocallyConstant.comp_continuous (continuous_const.prodMk continuous_snd)
    have hopen : IsOpen {p : X × Y | F p = F (x, p.2)} :=
      (F.isLocallyConstant.prodMk hf₀) {p | p.1 = p.2}
    have he := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := x) (P := fun x' y ↦ F (x', y) = F (x, y))
      (fun y _ ↦ hopen.mem_nhds (by rfl))
    filter_upwards [he] with x' hx'
    exact LocallyConstant.ext (fun y ↦ hx' y (Set.mem_univ y))

private theorem locallyConstant_evaluate
    {X Y T V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    (F : LocallyConstant X (LocallyConstant Y V))
    (a : T → X) (b : T → Y) (ha : Continuous a) (hb : Continuous b) :
    IsLocallyConstant (fun t ↦ F (a t) (b t)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  filter_upwards [(F.isLocallyConstant.comp_continuous ha).eventually_eq t,
    ((F (a t)).isLocallyConstant.comp_continuous hb).eventually_eq t] with t' h₁ h₂
  change F (a t') = F (a t) at h₁
  change F (a t) (b t') = F (a t) (b t) at h₂
  rw [h₁, h₂]

private def coinducedLeading
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    (V : Type w) (n : ℕ)
    (F : LocallyConstant (Fin n → G) (LocallyConstant G V)) :
    LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V) :=
  curryLocallyConstant ⟨fun p ↦ F (fun i ↦ p.1 i.succ) (p.2 * p.1 0),
    locallyConstant_evaluate F (fun p : (Fin (n + 1) → G) × G ↦ fun i ↦ p.1 i.succ)
      (fun p : (Fin (n + 1) → G) × G ↦ p.2 * p.1 0)
      (continuous_pi fun i ↦ (continuous_apply i.succ).comp continuous_fst)
      (continuous_snd.mul ((continuous_apply 0).comp continuous_fst))⟩

private def coinducedLeadingLinearMap
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    (A : Type v) [Ring A] (V : Type w) [AddCommGroup V] [Module A V] (n : ℕ) :
    LocallyConstant (Fin n → G) (LocallyConstant G V) →ₗ[A]
      LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V) where
  toFun := coinducedLeading G V n
  map_add' F H := by ext g x; rfl
  map_smul' a F := by ext g x; rfl

private def coinducedDifferential
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    (A : Type v) [Ring A] (V : Type w) [AddCommGroup V] [Module A V] (n : ℕ) :
    LocallyConstant (Fin n → G) (LocallyConstant G V) →ₗ[A]
      LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V) :=
  coinducedLeadingLinearMap G A V n + ∑ k : Fin (n + 1),
    (-1 : ℤ) ^ (k.val + 1) • LocallyConstant.comapₗ A
      ⟨Fin.contractNth k (· * ·), by
        apply continuous_pi
        intro i
        unfold Fin.contractNth
        split_ifs
        · exact continuous_apply _
        · exact (continuous_apply _).mul (continuous_apply _)
        · exact continuous_apply _⟩

private theorem coinducedDifferential_apply
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    (A : Type v) [Ring A] (V : Type w) [AddCommGroup V] [Module A V] (n : ℕ)
    (F : LocallyConstant (Fin n → G) (LocallyConstant G V))
    (g : Fin (n + 1) → G) (x : G) :
    coinducedDifferential G A V n F g x = F (fun i ↦ g i.succ) (x * g 0) +
      ∑ k : Fin (n + 1),
        (-1 : ℤ) ^ (k.val + 1) • F (Fin.contractNth k (· * ·) g) x := by
  simp only [coinducedDifferential, coinducedLeadingLinearMap, Int.reduceNeg,
    LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, coinducedLeading,
    curryLocallyConstant, LocallyConstant.coe_mk, LinearMap.coe_sum, LinearMap.coe_smul,
    Finset.sum_apply, Pi.smul_apply, LocallyConstant.coe_add, Pi.add_apply, add_right_inj]
  have sum_eval (s : Finset (Fin (n + 1)))
      (f : Fin (n + 1) → LocallyConstant (Fin (n + 1) → G) (LocallyConstant G V)) :
      (∑ i ∈ s, f i) g x = ∑ i ∈ s, f i g x :=
    map_sum ((LocallyConstant.evalₗ A x).comp (LocallyConstant.evalₗ A g)) f s
  rw [sum_eval]
  rfl

/-- The inhomogeneous continuous cochain differential and the evaluation contraction
satisfy the contracting homotopy identity in every positive degree.
The witnesses `d` and `h` are uniquely specified by their pointwise formulas;
`h n` is the paper's `h_{n+1}`, so `n = 0` includes the degree-one identity.
Nested locally constant maps give the discrete topology on the coinduced module.
`Fin.contractNth` combines adjacent entries, or drops the last entry at the last index.
Integer scalar multiplication expresses alternating signs over an arbitrary ring.

Source: Stacks Project, etale-cohomology.tex, Tag 0DVG, label
section-continuous-group-cohomology (blueprint: lem-exc-coinduced-homotopy-identity).

Proof: (1) Use `lem-exc-coinduced-homotopy-continuous`
(`Rep.exists_coinduced_continuous_contraction`) for the evaluation contractions.
Construct the displayed differential directly. The leading expression is jointly
locally constant in the tuple and the function variable: near a point the outer
cochain is fixed, and then its value is locally constant. Compactness of `G` makes
its curry locally constant into the discrete function module. The other faces are
continuous precompositions with multiplication and deletion of tuple entries.
All operations are linear pointwise. Fix a positive degree,
a group tuple and `x`. Expand `d h` using right translation. Its leading term is
`F(x*g_1,g_2,...)(1)`, followed by the alternating interior product terms and the
endpoint with sign `(-1)^degree`. This also covers `d^0` in degree one.
(2) Expand `h d` by evaluating `d F` on `(x,g_1,...)` at one. Its leading term is
`F(g_1,...)(x)`, followed by the negative leading term from (1), the opposite interior
product terms, and the endpoint with sign `(-1)^(degree+1)`.
(3) Add the expansions. Each product term and endpoint cancels, leaving only
`F(g_1,...)(x)`. Extensionality in `x` and the tuple gives equality of continuous
cochains, namely `d^{degree-1} h_degree F + h_{degree+1} d^degree F = F`. -/
theorem coinduced_homotopy_identity
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    (M : DiscreteContinuousRep.{v, u, w} A G) :
    ∃ (d : ∀ n : ℕ,
        LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V) →ₗ[A]
          LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V))
      (h : ∀ n : ℕ,
        LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V) →ₗ[A]
          LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V)),
      (∀ (n : ℕ) (F : LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V))
        (g : Fin (n + 1) → G) (x : G),
        d n F g x = F (fun i ↦ g i.succ) (x * g 0) +
          ∑ j : Fin (n + 1),
            (-1 : ℤ) ^ (j.val + 1) • F (Fin.contractNth j (· * ·) g) x) ∧
      (∀ (n : ℕ)
        (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V))
        (g : Fin n → G) (x : G), h n F g x = F (Fin.cons x g) 1) ∧
      (∀ (n : ℕ)
        (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V)),
        d n (h n F) + h (n + 1) (d (n + 1) F) = F) := by
  classical
  choose h hh using exists_coinduced_continuous_contraction G A M
  refine ⟨coinducedDifferential G A M.obj.V, h,
    coinducedDifferential_apply G A M.obj.V, hh, ?_⟩
  intro n F
  apply LocallyConstant.ext
  intro g
  apply LocallyConstant.ext
  intro x
  change coinducedDifferential G A M.obj.V n (h n F) g x +
    h (n + 1) (coinducedDifferential G A M.obj.V (n + 1) F) g x = F g x
  rw [hh (n + 1), coinducedDifferential_apply, coinducedDifferential_apply]
  simp only [hh, Fin.cons_succ, Fin.cons_zero, one_mul]
  change F (Fin.cons (x * g 0) (fun k ↦ g k.succ)) 1 +
    (∑ k : Fin (n + 1),
      (-1 : ℤ) ^ (k.val + 1) • F (Fin.cons x (Fin.contractNth k (· * ·) g)) 1) +
    (F g x + ∑ k : Fin (n + 2),
      (-1 : ℤ) ^ (k.val + 1) • F (Fin.contractNth k (· * ·) (Fin.cons x g)) 1) =
      F g x
  rw [Fin.sum_univ_succ (fun k : Fin (n + 2) ↦
    (-1 : ℤ) ^ (k.val + 1) • F (Fin.contractNth k (· * ·) (Fin.cons x g)) 1)]
  have hzero : Fin.contractNth 0 (· * ·) (Fin.cons x g) =
      Fin.cons (x * g 0) (fun i ↦ g i.succ) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [Fin.contractNth]
  have hsucc (k : Fin (n + 1)) :
      Fin.contractNth k.succ (· * ·) (Fin.cons x g) =
        Fin.cons x (Fin.contractNth k (· * ·) g) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [Fin.contractNth]
  simp only [Fin.val_zero, zero_add, pow_one, neg_one_zsmul,
    hzero, hsucc, Fin.val_succ]
  simp only [pow_succ', mul_zsmul, neg_one_zsmul, Finset.sum_neg_distrib]
  abel

end Rep

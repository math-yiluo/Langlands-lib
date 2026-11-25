/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Standard graded algebras

Let `k` be a field. A *standard graded `k`-algebra* is an `ℕ`-graded commutative `k`-algebra
`S = ⨁ₙ Sₙ` which is generated as a `k`-algebra by finitely many elements of degree one. Then
`S₀ = k` (more precisely, `S₀` is the image of `k`), and every `Sₙ = S₁ ^ n` is a
finite-dimensional `k`-vector space.

Given two linear forms `l₀, l₁ ∈ S₁` without common zero on `Proj S`, we show that
`S_{n + 1} = l₀ Sₙ + l₁ Sₙ` for all large `n`, that `S` is a finite module over the subalgebra
`k[l₀, l₁]`, and that the degree-zero part `S_(l₀)` of `S[l₀⁻¹]` is a finite module over the
subalgebra `k[l₁ / l₀]`. Geometrically, the last statement is the algebraic content of the
finiteness of the morphism `Proj S → ℙ¹` given by `[l₀ : l₁]` over the chart `D₊(l₀)`.

## Main definitions

- `GradedAlgebra.IsStandard 𝒜` — the grading `𝒜` makes `S` a standard graded `k`-algebra.

## Main statements

- `GradedAlgebra.IsStandard.grade_eq_pow` — `𝒜 n = 𝒜 1 ^ n`.
- `GradedAlgebra.IsStandard.grade_zero_eq_one` — `𝒜 0 = 1`, i.e. `S₀` is the image of `k`.
- `GradedAlgebra.IsStandard.finite_grade` — each `𝒜 n` is finite-dimensional over `k`.
- `GradedAlgebra.IsStandard.exists_grade_succ_eq_span_mul` — if `l₀, l₁ ∈ S₁` have no common
  zero on `Proj S`, then `S_{n + 1} = (k l₀ + k l₁) Sₙ` for all large `n`.
- `GradedAlgebra.IsStandard.finite_adjoin_pair` — then `S` is finite over `k[l₀, l₁]`.
- `GradedAlgebra.IsStandard.finite_away` — and `S_(l₀)` is finite over `k[l₁ / l₀]`.

The statement that a vector space over an infinite field is not a finite union of proper
subspaces (blueprint `theorem-riemann-roch-coherent-serre-duality`) is
`Subspace.iUnion_ne_univ_of_ne_top`, a restatement of Mathlib's
`Subspace.biUnion_ne_univ_of_top_notMem`.
-/

@[expose] public section

namespace HomogeneousLocalization.Away

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid ι]
  [DecidableEq ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] {d : ι} {f : A}

/-- The fraction `(a + b) / f ^ n` is `a / f ^ n + b / f ^ n`. -/
lemma mk_add (hf : f ∈ 𝒜 d) (n : ℕ) (a b : A) (ha : a ∈ 𝒜 (n • d)) (hb : b ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n (a + b) (add_mem ha hb) = Away.mk 𝒜 hf n a ha + Away.mk 𝒜 hf n b hb := by
  apply val_injective
  rw [val_add, Away.val_mk, Away.val_mk, Away.val_mk, Localization.add_mk_self]

/-- The fraction `(c • a) / f ^ n` is `c • (a / f ^ n)`. -/
lemma mk_smul (hf : f ∈ 𝒜 d) (n : ℕ) (c : R) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n (c • a) (Submodule.smul_mem _ c ha) = c • Away.mk 𝒜 hf n a ha :=
  rfl

/-- The fraction `0 / f ^ n` is `0`. -/
lemma mk_zero (hf : f ∈ 𝒜 d) (n : ℕ) (h : (0 : A) ∈ 𝒜 (n • d)) :
    Away.mk 𝒜 hf n 0 h = 0 :=
  mk_eq_zero_of_num _ rfl

end HomogeneousLocalization.Away

namespace GradedAlgebra

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] (𝒜 : ℕ → Submodule k S)
  [GradedAlgebra 𝒜]

/-- In an `ℕ`-graded algebra, products of `n` elements of degree one have degree `n`. -/
theorem grade_one_pow_le (n : ℕ) : 𝒜 1 ^ n ≤ 𝒜 n := by
  induction n with
  | zero => exact Submodule.one_le.mpr SetLike.GradedOne.one_mem
  | succ n ih =>
    rw [pow_succ, Submodule.mul_le]
    intro x hx y hy
    exact SetLike.mul_mem_graded (ih hx) hy

/-- A *standard graded `k`-algebra*: an `ℕ`-graded `k`-algebra `S = ⨁ₙ 𝒜 n` which is
generated as a `k`-algebra by finitely many elements of degree one, i.e. `𝒜 1` is a
finite-dimensional `k`-subspace generating `S` as a `k`-algebra. The condition `S₀ = k` of the
blueprint is then automatic, see `GradedAlgebra.IsStandard.grade_zero_eq_one`.
(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
class IsStandard : Prop where
  /-- The degree-one part is finite-dimensional. -/
  fg_one : (𝒜 1).FG
  /-- The degree-one part generates the whole algebra. -/
  adjoin_one : Algebra.adjoin k (𝒜 1 : Set S) = ⊤

namespace IsStandard

variable {𝒜} [IsStandard 𝒜]

variable (𝒜) in
/-- In a standard graded algebra, the degree-`n` part is spanned by products of `n` elements
of degree one. (blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem grade_eq_pow (n : ℕ) : 𝒜 n = 𝒜 1 ^ n := by
  refine le_antisymm (fun x hx => ?_) (grade_one_pow_le 𝒜 n)
  have key (y : S) (m : ℕ) : (DirectSum.decompose 𝒜 y m : S) ∈ 𝒜 1 ^ m := by
    have hy : y ∈ Subalgebra.toSubmodule (Algebra.adjoin k (𝒜 1 : Set S)) := by
      rw [adjoin_one]
      trivial
    rw [Algebra.adjoin_eq_span] at hy
    induction hy using Submodule.span_induction generalizing m with
    | mem z hz =>
      obtain ⟨j, hj⟩ : ∃ j, z ∈ 𝒜 1 ^ j := by
        induction hz using Submonoid.closure_induction with
        | mem w hw => exact ⟨1, by rwa [pow_one]⟩
        | one => exact ⟨0, by simpa using Submodule.one_le.mp (le_refl (1 : Submodule k S))⟩
        | mul a b _ _ ha hb =>
          obtain ⟨i, hi⟩ := ha
          obtain ⟨j, hj⟩ := hb
          exact ⟨i + j, pow_add (𝒜 1) i j ▸ Submodule.mul_mem_mul hi hj⟩
      by_cases hjm : j = m
      · subst hjm
        rwa [DirectSum.decompose_of_mem_same 𝒜 (grade_one_pow_le 𝒜 j hj)]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 (grade_one_pow_le 𝒜 j hj) hjm]
        exact zero_mem _
    | zero => simp
    | add a b _ _ ha hb => simpa using add_mem (ha m) (hb m)
    | smul c a _ ha => simpa [DirectSum.smul_apply] using Submodule.smul_mem _ c (ha m)
  simpa [DirectSum.decompose_of_mem_same 𝒜 hx] using key x n

/-- In a standard graded `k`-algebra the degree-zero part is (the image of) `k`.
(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem grade_zero_eq_one : 𝒜 0 = 1 := by
  rw [grade_eq_pow 𝒜 0, pow_zero]

/-- Each graded piece of a standard graded `k`-algebra is finite-dimensional.
(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
instance finite_grade (n : ℕ) : Module.Finite k (𝒜 n) := by
  rw [Module.Finite.iff_fg, grade_eq_pow 𝒜 n]
  exact (fg_one (𝒜 := 𝒜)).pow n

open ProjectiveSpectrum

/-- Let `S` be a standard graded `k`-algebra and `l₀, l₁ ∈ S₁` without common zero on `Proj S`.
Then `S_{n + 1} = l₀ Sₙ + l₁ Sₙ` for all large `n`.
(blueprint: `theorem-riemann-roch-coherent-serre-duality`) -/
theorem exists_grade_succ_eq_span_mul {l₀ l₁ : S} (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1)
    (h : basicOpen 𝒜 l₀ ⊔ basicOpen 𝒜 l₁ = ⊤) :
    ∃ N, ∀ n ≥ N, 𝒜 (n + 1) = Submodule.span k {l₀, l₁} * 𝒜 n := by
  set J := Ideal.span ({l₀, l₁} : Set S)
  have hJ : J.IsHomogeneous 𝒜 := Ideal.homogeneous_span 𝒜 _ (by
    rintro x (rfl | rfl)
    exacts [⟨1, h₀⟩, ⟨1, h₁⟩])
  have hrad : Ideal.span (𝒜 1 : Set S) ≤ J.radical := by
    rw [Ideal.span_le, hJ.radical_eq]
    intro x hx
    rw [SetLike.mem_coe, Submodule.mem_sInf]
    rintro P ⟨hPh, hJP, hP⟩
    by_contra hxP
    have hirr : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ ⟨P, hPh⟩ := fun hle => hxP (hle (by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne 𝒜 hx one_ne_zero]))
    have hmem : (⟨⟨P, hPh⟩, hP, hirr⟩ : ProjectiveSpectrum 𝒜) ∈
        basicOpen 𝒜 l₀ ⊔ basicOpen 𝒜 l₁ := h ▸ trivial
    rcases TopologicalSpace.Opens.mem_sup.mp hmem with h' | h'
    · exact h' (hJP (Ideal.subset_span (by simp)))
    · exact h' (hJP (Ideal.subset_span (by simp)))
  obtain ⟨s, hs⟩ := fg_one (𝒜 := 𝒜)
  have hfg : (Ideal.span (𝒜 1 : Set S)).FG :=
    ⟨s, by
      rw [← hs]
      exact (Submodule.span_span_of_tower k S (s : Set S)).symm⟩
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
  have hpow (n : ℕ) : 𝒜 n ≤ (Ideal.span (𝒜 1 : Set S) ^ n).restrictScalars k := by
    rw [grade_eq_pow 𝒜 n]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Submodule.mul_le]
      intro x hx y hy
      exact Ideal.mul_mem_mul (ih hx) (Ideal.subset_span hy)
  refine ⟨m, fun n hn => le_antisymm (fun x hx => ?_) ?_⟩
  · have hxJ : x ∈ J := hm (Ideal.pow_le_pow_right (by omega) (hpow _ hx))
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hxJ
    rw [← DirectSum.decompose_of_mem_same 𝒜 hx, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add, DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 h₀ (by omega),
      DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 h₁ (by omega), Nat.add_sub_cancel,
      mul_comm _ l₀, mul_comm _ l₁]
    exact add_mem (Submodule.mul_mem_mul (Submodule.subset_span (by simp)) (Subtype.prop _))
      (Submodule.mul_mem_mul (Submodule.subset_span (by simp)) (Subtype.prop _))
  · rw [Submodule.mul_le]
    intro l hl y hy
    have hl1 : l ∈ 𝒜 1 := (Submodule.span_le.mpr (by
      rintro x (rfl | rfl)
      exacts [h₀, h₁])) hl
    rw [add_comm]
    exact SetLike.mul_mem_graded hl1 hy

/-- Let `S` be a standard graded `k`-algebra and `l₀, l₁ ∈ S₁` without common zero on `Proj S`.
Then `S` is a finite module over the subalgebra `k[l₀, l₁]`.
(blueprint: `theorem-riemann-roch-coherent-serre-duality`, algebraic part) -/
theorem finite_adjoin_pair {l₀ l₁ : S} (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1)
    (h : basicOpen 𝒜 l₀ ⊔ basicOpen 𝒜 l₁ = ⊤) :
    Module.Finite (Algebra.adjoin k {l₀, l₁}) S := by
  classical
  obtain ⟨N, hN⟩ := exists_grade_succ_eq_span_mul h₀ h₁ h
  set R := Algebra.adjoin k ({l₀, l₁} : Set S)
  obtain ⟨t, ht⟩ : (⨆ i ∈ Finset.range (N + 1), 𝒜 i).FG :=
    Submodule.fg_biSup _ _ fun i _ => Module.Finite.iff_fg.mp inferInstance
  have hbase (n : ℕ) (hn : n ≤ N) : 𝒜 n ≤ (Submodule.span R (t : Set S)).restrictScalars k :=
    ((le_iSup₂ (f := fun i (_ : i ∈ Finset.range (N + 1)) => 𝒜 i) n
      (Finset.mem_range.mpr (by omega))).trans ht.ge).trans
      (Submodule.span_le_restrictScalars k R _)
  have key (n : ℕ) : 𝒜 n ≤ (Submodule.span R (t : Set S)).restrictScalars k := by
    induction n with
    | zero => exact hbase 0 (Nat.zero_le _)
    | succ n ih =>
      by_cases hn : N ≤ n
      · rw [hN n hn, Submodule.mul_le]
        intro l hl y hy
        exact Submodule.smul_mem _ (⟨l, (Submodule.span_le (p := Subalgebra.toSubmodule R)).mpr
          Algebra.subset_adjoin hl⟩ : R)
          (ih hy)
      · exact hbase (n + 1) (by omega)
  refine ⟨⟨t, eq_top_iff.mpr fun x _ => ?_⟩⟩
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Submodule.sum_mem _ fun i _ => key i (DirectSum.decompose 𝒜 x i).2

open HomogeneousLocalization

/-- Let `S` be a standard graded `k`-algebra and `l₀, l₁ ∈ S₁` without common zero on `Proj S`.
Then the degree-zero part `S_(l₀)` of `S[l₀⁻¹]` is a finite module over the subalgebra
generated by `l₁ / l₀`. Exchanging the roles of `l₀` and `l₁` gives the same statement for
`S_(l₁)` over `k[l₀ / l₁]`.
(blueprint: `theorem-riemann-roch-coherent-serre-duality`, algebraic part) -/
theorem finite_away {l₀ l₁ : S} (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1)
    (h : basicOpen 𝒜 l₀ ⊔ basicOpen 𝒜 l₁ = ⊤) :
    Module.Finite (Algebra.adjoin k {Away.mk 𝒜 h₀ 1 l₁ h₁}) (Away 𝒜 l₀) := by
  classical
  obtain ⟨N, hN⟩ := exists_grade_succ_eq_span_mul h₀ h₁ h
  set R := Algebra.adjoin k {Away.mk 𝒜 h₀ 1 l₁ h₁}
  let φ : 𝒜 (N • 1) →ₗ[k] Away 𝒜 l₀ :=
    { toFun y := Away.mk 𝒜 h₀ N y y.2
      map_add' y z := Away.mk_add 𝒜 h₀ N y z y.2 z.2
      map_smul' c y := Away.mk_smul 𝒜 h₀ N c y y.2 }
  obtain ⟨g, hg⟩ : (LinearMap.range φ).FG := Module.Finite.iff_fg.mp inferInstance
  set M : Submodule R (Away 𝒜 l₀) := Submodule.span R (g : Set (Away 𝒜 l₀))
  have hrange : LinearMap.range φ ≤ M.restrictScalars k :=
    hg ▸ Submodule.span_le_restrictScalars k R _
  have hspan : Submodule.span k {l₀, l₁} ≤ 𝒜 (1 • 1) := Submodule.span_le.mpr (by
    rintro x (rfl | rfl)
    exacts [h₀, h₁])
  have hL (l : S) (hl : l ∈ Submodule.span k {l₀, l₁}) (hl' : l ∈ 𝒜 (1 • 1)) :
      Away.mk 𝒜 h₀ 1 l hl' ∈ R := by
    induction hl using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [Away.mk_self]
        exact one_mem R
      · exact Algebra.self_mem_adjoin_singleton k _
    | zero =>
      rw [Away.mk_zero]
      exact zero_mem R
    | add x y hx hy ihx ihy =>
      rw [Away.mk_add 𝒜 h₀ 1 x y (hspan hx) (hspan hy)]
      exact add_mem (ihx _) (ihy _)
    | smul c x hx ih =>
      rw [Away.mk_smul 𝒜 h₀ 1 c x (hspan hx)]
      exact Subalgebra.smul_mem R (ih _) c
  have hbase (n : ℕ) (hn : n ≤ N) (x : S) (hx : x ∈ 𝒜 (n • 1)) : Away.mk 𝒜 h₀ n x hx ∈ M := by
    have hx' : x * l₀ ^ (N - n) ∈ 𝒜 (N • 1) := by
      have := SetLike.mul_mem_graded hx (SetLike.pow_mem_graded (N - n) h₀)
      simpa [Nat.add_sub_cancel' hn] using this
    rw [Away.mk_eq_mk_of_mul_pow_eq 𝒜 h₀ hx hx'
      (by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hn])]
    exact hrange ⟨⟨_, hx'⟩, rfl⟩
  have key (n : ℕ) (x : S) (hx : x ∈ 𝒜 (n • 1)) : Away.mk 𝒜 h₀ n x hx ∈ M := by
    induction n generalizing x with
    | zero => exact hbase 0 (Nat.zero_le _) x hx
    | succ n ih =>
      by_cases hn : N ≤ n
      · have hle : Submodule.span k {l₀, l₁} * 𝒜 n ≤ 𝒜 ((n + 1) • 1) := by
          rw [← hN n hn]
          simp
        have hx' : x ∈ Submodule.span k {l₀, l₁} * 𝒜 n := by
          rw [← hN n hn]
          simpa using hx
        revert hx
        induction hx' using Submodule.mul_induction_on' with
        | mem_mul_mem l hl y hy =>
          intro hx
          have hyn : y ∈ 𝒜 (n • 1) := by simpa using hy
          rw [Away.mk_eq_mk_of_mul_pow_eq 𝒜 h₀ hx
            (add_smul 1 n 1 ▸ SetLike.mul_mem_graded (hspan hl) hyn) (by rw [add_comm 1 n]),
            ← Away.mk_mul 𝒜 h₀ 1 n l y (hspan hl) hyn]
          exact M.smul_mem ⟨_, hL l hl (hspan hl)⟩ (ih y hyn)
        | add a ha b hb iha ihb =>
          intro hx
          rw [Away.mk_add 𝒜 h₀ _ a b (hle ha) (hle hb)]
          exact add_mem (iha _) (ihb _)
      · exact hbase (n + 1) (by omega) x hx
  refine ⟨⟨g, eq_top_iff.mpr fun z _ => ?_⟩⟩
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 h₀ z
  exact key n x hx

/-- Let `S` be a standard graded `k`-algebra whose degree-one part is spanned by a family
`l : ι → S₁`. Then the degree-zero part `S_(lᵢ)` of `S[lᵢ⁻¹]` is generated as a `k`-algebra
by the quotients `lⱼ / lᵢ`. -/
theorem adjoin_away_eq_top {ι : Type*} {l : ι → S} (hl : ∀ j, l j ∈ 𝒜 1)
    (hspan : 𝒜 1 ≤ Submodule.span k (Set.range l)) (i : ι) :
    Algebra.adjoin k (Set.range fun j ↦ Away.mk 𝒜 (hl i) 1 (l j) (by simpa using hl j)) =
      ⊤ := by
  set R := Algebra.adjoin k (Set.range fun j ↦ Away.mk 𝒜 (hl i) 1 (l j) (by simpa using hl j))
  have hspan' : Submodule.span k (Set.range l) ≤ 𝒜 (1 • 1) := Submodule.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    simpa using hl j)
  have hL (x : S) (hx : x ∈ Submodule.span k (Set.range l)) (hx' : x ∈ 𝒜 (1 • 1)) :
      Away.mk 𝒜 (hl i) 1 x hx' ∈ R := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨j, rfl⟩
    | zero =>
      rw [Away.mk_zero]
      exact zero_mem R
    | add x y hx hy ihx ihy =>
      rw [Away.mk_add 𝒜 (hl i) 1 x y (hspan' hx) (hspan' hy)]
      exact add_mem (ihx _) (ihy _)
    | smul c x hx ih =>
      rw [Away.mk_smul 𝒜 (hl i) 1 c x (hspan' hx)]
      exact Subalgebra.smul_mem R (ih _) c
  have key (n : ℕ) (x : S) (hx : x ∈ 𝒜 (n • 1)) : Away.mk 𝒜 (hl i) n x hx ∈ R := by
    induction n generalizing x with
    | zero =>
      have hx0 : x ∈ (1 : Submodule k S) := by
        rw [← grade_zero_eq_one (𝒜 := 𝒜)]
        simpa using hx
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hx0
      have h1 : (1 : S) ∈ 𝒜 (0 • 1) := by simpa using SetLike.GradedOne.one_mem (A := 𝒜)
      have : Away.mk 𝒜 (hl i) 0 (algebraMap k S c) hx = c • Away.mk 𝒜 (hl i) 0 1 h1 := by
        rw [← Away.mk_smul]
        congr 1
        exact Algebra.algebraMap_eq_smul_one c
      rw [this, Away.mk_one]
      exact Subalgebra.smul_mem R (one_mem R) c
    | succ n ih =>
      have hx' : x ∈ 𝒜 1 * 𝒜 n := by
        rw [grade_eq_pow 𝒜 n, ← pow_succ', ← grade_eq_pow 𝒜 (n + 1)]
        simpa using hx
      revert hx
      induction hx' using Submodule.mul_induction_on' with
      | mem_mul_mem a ha y hy =>
        intro hx
        have hyn : y ∈ 𝒜 (n • 1) := by simpa using hy
        have ha' : a ∈ 𝒜 (1 • 1) := by simpa using ha
        rw [Away.mk_eq_mk_of_mul_pow_eq 𝒜 (hl i) hx
          (add_smul 1 n 1 ▸ SetLike.mul_mem_graded ha' hyn) (by rw [add_comm 1 n]),
          ← Away.mk_mul 𝒜 (hl i) 1 n a y ha' hyn]
        exact mul_mem (hL a (hspan ha) ha') (ih y hyn)
      | add a ha b hb iha ihb =>
        intro hx
        have hle (z : S) (hz : z ∈ 𝒜 1 * 𝒜 n) : z ∈ 𝒜 ((n + 1) • 1) := by
          have : 𝒜 1 * 𝒜 n ≤ 𝒜 (1 + n) :=
            Submodule.mul_le.mpr fun a ha b hb => SetLike.mul_mem_graded ha hb
          simpa [add_comm] using this hz
        rw [Away.mk_add 𝒜 (hl i) _ a b (hle a ha) (hle b hb)]
        exact add_mem (iha _) (ihb _)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 (hl i) z
  exact key n x hx

end IsStandard

end GradedAlgebra

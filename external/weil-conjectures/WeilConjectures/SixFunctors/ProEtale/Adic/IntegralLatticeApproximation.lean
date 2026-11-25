/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeScalarLinear

/-!
# Semilinearity of an integral lattice by `ℓ`-adic approximation

Let `M` be a finite `𝒪_E`-module, `W` a topological space and `ψ : C(W, M) → V` an additive map
to an abelian group without `ℓ`-torsion, on which the functions `f ∈ C(W, 𝒪_E)` act additively.
This file proves `ψ(f • m) = f • ψ(m)` for all `f`
(`PadicAlgCl.map_smul_of_forall_exists_approx`), assuming:

- it holds for a class of functions approximating every `f` modulo every power of `ℓ` (e.g. the
  locally constant functions with values in `ℕ` when `ℤ_ℓ → 𝒪_E` is onto);
- the action preserves the image of `ψ` (the integrality of the action on the lattice);
- the kernel of `ψ` consists of torsion functions.

Writing `f = g + ℓᵏ s` with `g` in the class, the defect `ψ(f • m) - f • ψ(m)` is `ℓᵏ` times the
defect of `s`; both lie in the image of `ψ`, so the defect is the image of a function whose values
are, modulo torsion, divisible by every power of `ℓ`, hence torsion (Krull's intersection theorem
for `M ⧸ M_tors`, `PadicAlgCl.exists_pow_smul_eq_zero_of_forall`). The torsion of `M` being
bounded, the defect is killed by a power of `ℓ`, hence vanishes.
-/

@[expose] public section

open PadicAlgCl

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (E : FiniteIntermediateField l) {M : Type*} [AddCommGroup M]
  [Module (integers l E.1) M]

variable (M) in
/-- The `ℓ`-power torsion submodule `{y | ∃ n, ℓⁿ • y = 0}` of an `𝒪_E`-module. -/
def powTorsion : Submodule (integers l E.1) M where
  carrier := {y | ∃ n : ℕ, l ^ n • y = 0}
  add_mem' := by
    rintro y z ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [smul_add, pow_add, mul_smul, mul_smul, smul_comm (l ^ a) (l ^ b) y, ha, hb,
      smul_zero, smul_zero, add_zero]
  zero_mem' := ⟨0, smul_zero _⟩
  smul_mem' := by
    rintro r y ⟨n, hn⟩
    exact ⟨n, by rw [smul_comm, hn, smul_zero]⟩

lemma mem_powTorsion {y : M} : y ∈ powTorsion E M ↔ ∃ n : ℕ, l ^ n • y = 0 :=
  Iff.rfl

variable [Module.Finite (integers l E.1) M]

include E in
/-- An element of a finite `𝒪_E`-module which is, modulo `ℓ`-power torsion, divisible by every
power of `ℓ` is `ℓ`-power torsion. -/
lemma exists_pow_smul_eq_zero_of_forall {y : M}
    (hy : ∀ k : ℕ, ∃ z : M, ∃ n : ℕ, l ^ n • (y - l ^ k • z) = 0) :
    ∃ n : ℕ, l ^ n • y = 0 := by
  have h := eq_zero_of_forall_eq_pow_smul l E (Submodule.Quotient.mk (p := powTorsion E M) y)
    fun k ↦ by
      obtain ⟨z, n, hn⟩ := hy k
      refine ⟨Submodule.Quotient.mk z, ?_⟩
      rw [← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨n, hn⟩
  exact (Submodule.Quotient.mk_eq_zero _).1 h

include E in
/-- The `ℓ`-power torsion of a finite `𝒪_E`-module is killed by a single power of `ℓ`. -/
lemma exists_pow_smul_eq_zero_of_mem_powTorsion :
    ∃ N : ℕ, ∀ y : M, (∃ n : ℕ, l ^ n • y = 0) → l ^ N • y = 0 := by
  have : IsNoetherian (integers l E.1) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  let K : ℕ →o Submodule (integers l E.1) M :=
    ⟨fun n ↦ LinearMap.ker (((l ^ n : ℕ) : integers l E.1) • LinearMap.id), fun a b hab y hy ↦ by
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      rw [pow_add, Nat.cast_mul, mul_comm, mul_smul, hy, smul_zero]⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.2 inferInstance) K
  refine ⟨N, fun y ⟨n, hn⟩ ↦ ?_⟩
  have hy : y ∈ K (max n N) := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (le_max_left n N)
    change (((l ^ max n N : ℕ) : integers l E.1)) • y = 0
    rw [Nat.cast_smul_eq_nsmul, hc, pow_add, mul_comm, mul_smul, hn, smul_zero]
  rw [← hN _ (le_max_right n N)] at hy
  change (((l ^ N : ℕ) : integers l E.1)) • y = 0 at hy
  rwa [Nat.cast_smul_eq_nsmul] at hy

variable {W : Type*} [TopologicalSpace W] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [TopologicalSpace (integers l E.1)] [IsTopologicalRing (integers l E.1)]
  [ContinuousSMul (integers l E.1) M] {V : Type*}
  [AddCommGroup V] (ψ : C(W, M) →+ V) (act : C(W, integers l E.1) → V →+ V)

/-- **Semilinearity by `ℓ`-adic approximation.** Let `ψ : C(W, M) → V` be additive, `V` without
`ℓ`-torsion, with an action of `C(W, 𝒪_E)` additive in the function, preserving the image of
`ψ`, and suppose that the kernel of `ψ` consists of `ℓ`-power torsion functions. If every
`f ∈ C(W, 𝒪_E)` is congruent modulo every power of `ℓ` to a function `g` with
`ψ(g • m) = g • ψ(m)` for all `m`, then `ψ(f • m) = f • ψ(m)` for all `f` and `m`. -/
theorem map_smul_of_forall_exists_approx
    (hact : ∀ (f g : C(W, integers l E.1)) (v : V), act (f + g) v = act f v + act g v)
    (hact_nsmul : ∀ (n : ℕ) (f : C(W, integers l E.1)) (v : V), act (n • f) v = n • act f v)
    (hV : ∀ v : V, l • v = 0 → v = 0)
    (hint : ∀ (f : C(W, integers l E.1)) (m : C(W, M)), ∃ e : C(W, M), act f (ψ m) = ψ e)
    (hker : ∀ t : C(W, M), ψ t = 0 → ∃ n : ℕ, l ^ n • t = 0)
    (happrox : ∀ (f : C(W, integers l E.1)) (k : ℕ), ∃ g s : C(W, integers l E.1),
      f = g + l ^ k • s ∧ ∀ m : C(W, M), ψ (g • m) = act g (ψ m))
    (f : C(W, integers l E.1)) (m : C(W, M)) :
    ψ (f • m) = act f (ψ m) := by
  obtain ⟨e₀, he₀⟩ := hint f m
  -- the defect is `ψ (f • m - e₀)`
  rw [← sub_eq_zero, he₀, ← map_sub]
  have hdiv (k : ℕ) : ∃ c : C(W, M), ∃ n : ℕ, l ^ n • (f • m - e₀ - l ^ k • c) = 0 := by
    obtain ⟨g, s, rfl, hg⟩ := happrox f k
    obtain ⟨e, he⟩ := hint s m
    refine ⟨s • m - e, hker _ ?_⟩
    have h1 : (g + l ^ k • s) • m = g • m + l ^ k • (s • m) := by
      rw [add_smul, smul_assoc]
    simp only [map_sub, map_add, map_nsmul, h1, hg]
    rw [← he₀, hact, hact_nsmul, ← he, smul_sub]
    abel
  obtain ⟨N, hN⟩ := exists_pow_smul_eq_zero_of_mem_powTorsion E (M := M)
  have hpt (x : W) : l ^ N • (f • m - e₀) x = 0 := by
    refine hN _ (exists_pow_smul_eq_zero_of_forall E fun k ↦ ?_)
    obtain ⟨c, n, hc⟩ := hdiv k
    exact ⟨c x, n, congrArg (fun h : C(W, M) ↦ h x) hc⟩
  have h0 : l ^ N • ψ (f • m - e₀) = 0 := by
    rw [← map_nsmul]
    exact (congrArg ψ (ContinuousMap.ext hpt)).trans (map_zero ψ)
  have key (N : ℕ) (v : V) (hv : l ^ N • v = 0) : v = 0 := by
    induction N generalizing v with
    | zero => simpa using hv
    | succ N ih => exact ih v (hV _ (by rwa [pow_succ', mul_smul] at hv))
  exact key N _ h0

end PadicAlgCl

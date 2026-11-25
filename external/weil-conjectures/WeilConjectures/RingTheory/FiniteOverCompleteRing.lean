/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite modules over adically complete rings

Source: Stacks Project, Algebra, Lemma 10.96.12 (Tag 031D), including the
lifting-of-generators assertion in its proof
(blueprint: lem-weil-pbc-finite-over-complete-ring).
-/

@[expose] public section

universe u v

namespace Module

private theorem mem_smul_top_pi_iff {A : Type u} [CommRing A] (J : Ideal A)
    {r : ℕ} (a : Fin r → A) :
    a ∈ (J • ⊤ : Submodule A (Fin r → A)) ↔ ∀ j, a j ∈ J := by
  classical
  constructor
  · intro ha j
    have h := Submodule.smul_top_le_comap_smul_top J (LinearMap.proj j) ha
    simpa using h
  · intro ha
    have heq : a = ∑ j, a j • Pi.single j (1 : A) := by
      ext j
      simp [Pi.single_apply]
    rw [heq]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem_smul (ha j) Submodule.mem_top

private theorem precomplete_fin {A : Type u} [CommRing A] (I : Ideal A)
    [IsPrecomplete I A] (r : ℕ) : IsPrecomplete I (Fin r → A) := by
  classical
  constructor
  intro f hf
  have hc (j : Fin r) : ∃ L : A, ∀ n, f n j ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
    apply IsPrecomplete.prec' (I := I)
    intro m n hmn
    have h := (mem_smul_top_pi_iff (I ^ m) (f m - f n)).mp
      (SModEq.sub_mem.mp (hf hmn)) j
    simpa [SModEq.sub_mem] using h
  choose L hL using hc
  refine ⟨L, fun n ↦ SModEq.sub_mem.mpr ?_⟩
  apply (mem_smul_top_pi_iff (I ^ n) _).mpr
  intro j
  simpa [SModEq.sub_mem] using hL j n

/-- (blueprint: lem-weil-pbc-finite-over-complete-ring)
Stacks Project, Algebra, Lemma 10.96.12 (Tag 031D): a Hausdorff module over an
`I`-adically complete ring is finite if its reduction modulo `I` is finite.
Every finite family whose images generate the reduction already generates the module.

Proof (the node's successive-approximation form of the proof of Tags 031D and 0315):
1. Let `x₁, …, xᵣ` lift generators of `M/IM`, and let `N` be their span. For each `k`,
   express any element of `I^k M` modulo `I^(k+1) M` as a combination of the `xᵢ`
   with coefficients in `I^k`: expand it as a finite sum of products, then express
   each module factor modulo `IM` using the given quotient generators.
2. For `m : M`, repeatedly apply step 1 to obtain errors `mₙ ∈ I^n M` and coefficient
   partial sums `sᵢ⁽ⁿ⁾` with `m = ∑ᵢ sᵢ⁽ⁿ⁾ xᵢ + mₙ`. The differences of successive
   coefficients lie in `I^n`, so these partial sums give compatible residue classes.
3. By completeness of `A` [def-weil-pbc-adically-complete-ring], the compatible classes
   in the completion [def-weil-pbc-adic-completion] lift to coefficients `aᵢ : A`.
   For all `n`, `aᵢ - sᵢ⁽ⁿ⁾ ∈ I^n`.
4. Thus `m - ∑ᵢ aᵢ xᵢ` lies in every `I^n M`, hence vanishes by Hausdorffness.
   The chosen family spans `M`. Finiteness of the quotient supplies such a finite family,
   giving `Module.Finite A M` [def-weil-finitely-generated-module]. -/
theorem finite_and_span_eq_top_of_adicComplete
    {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    [IsAdicComplete I A] [IsHausdorff I M]
    [Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))] :
    Module.Finite A M ∧
      ∀ (r : ℕ) (x : Fin r → M),
        Submodule.span (A ⧸ I)
          (Set.range (fun j ↦ (I • (⊤ : Submodule A M)).mkQ (x j))) = ⊤ →
        Submodule.span A (Set.range x) = ⊤ := by
  classical
  have hspan : ∀ (r : ℕ) (x : Fin r → M),
      Submodule.span (A ⧸ I)
        (Set.range (fun j ↦ (I • (⊤ : Submodule A M)).mkQ (x j))) = ⊤ →
      Submodule.span A (Set.range x) = ⊤ := by
    intro r x hx
    have : IsPrecomplete I (Fin r → A) := precomplete_fin I r
    apply (span_range_eq_top_iff_surjective_fintypeLinearCombination A x).mpr
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro y
    obtain ⟨c, hc⟩ :=
      (span_range_eq_top_iff_surjective_fintypeLinearCombination (A ⧸ I) _).mp hx y
    choose a ha using fun j ↦ Ideal.Quotient.mk_surjective (c j)
    refine ⟨a, ?_⟩
    change (I • (⊤ : Submodule A M)).mkQ (∑ j, a j • x j) = y
    rw [map_sum]
    simpa only [Fintype.linearCombination_apply, ← ha,
      Module.Quotient.mk_smul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_smul,
      map_smul] using hc
  refine ⟨?_, hspan⟩
  obtain ⟨r, y, hy⟩ := Module.Finite.exists_fin (R := A ⧸ I)
    (M := M ⧸ (I • ⊤ : Submodule A M))
  choose x hx using fun j ↦ (I • (⊤ : Submodule A M)).mkQ_surjective (y j)
  have hxspan := hspan r x (by simpa only [hx] using hy)
  exact Module.Finite.of_fg_top (hxspan ▸ Submodule.fg_span (Set.finite_range x))

end Module

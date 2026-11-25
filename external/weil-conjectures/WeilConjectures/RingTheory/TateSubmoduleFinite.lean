/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.RingTheory.FiniteOverCompleteRing

/-!
# Finiteness of adic completions and Tate modules over complete rings

Let `Λ` be a ring, complete for the adic topology of an ideal `I`. Using the complete Nakayama
lemma `Module.finite_and_span_eq_top_of_adicComplete`:

- `Module.finite_adicCompletion`: if `I` is finitely generated and `A ⧸ I A` is a finite
  `Λ`-module, the completion `Â` of `A` is a finite `Λ`-module;
- `Module.tateSubmodule ϖ B`: the `ϖ`-adic Tate module `lim (B[ϖⁿ⁺¹], ϖ)` of a `Λ`-module `B`, as
  a submodule of `ℕ → B`;
- `Module.finite_tateSubmodule`: if `Λ` is noetherian and `ϖ`-adically complete and the
  `ϖ`-torsion `B[ϖ]` is finitely generated, the Tate module is a finite `Λ`-module.

These are the two outer terms of the exact sequence `0 → Ĥⁱ → lim Hⁱ(K ⊗ᴸ Λ/ϖⁿ⁺¹) → T_ϖ Hⁱ⁺¹`
computing the limit of the cohomology of the reductions of a complex `K`
(`ModuleCat.finite_limit_of_exact_tateSubmodule`).
-/

@[expose] public section

universe u v

namespace Module

variable {Λ : Type u} [CommRing Λ]

section Completion

variable (I : Ideal Λ) (A : Type v) [AddCommGroup A] [Module Λ A]

/-- The reduction `A ⧸ I A ⟶ Â ⧸ I Â` is surjective when `I` is finitely generated. -/
lemma surjective_mapQ_of_adicCompletion (hI : I.FG) :
    Function.Surjective ((I • ⊤ : Submodule Λ A).mapQ (I • ⊤ : Submodule Λ (AdicCompletion I A))
      (AdicCompletion.of I A) (Submodule.smul_top_le_comap_smul_top I _)) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective _ (x.val 1)
  refine ⟨Submodule.Quotient.mk a, ?_⟩
  rw [Submodule.mapQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have h : AdicCompletion.of I A a - x ∈ (AdicCompletion.eval I A 1).ker := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, AdicCompletion.eval_apply, ha,
      sub_self]
  rwa [← AdicCompletion.pow_smul_top_eq_ker_eval hI, pow_one] at h

/-- **Finiteness of a completion.** Over a ring complete for a finitely generated ideal `I`, the
`I`-adic completion of a module `A` with `A ⧸ I A` finite is a finite module (complete
Nakayama lemma, `Module.finite_and_span_eq_top_of_adicComplete`). -/
theorem finite_adicCompletion [IsAdicComplete I Λ] (hI : I.FG)
    [Module.Finite Λ (A ⧸ (I • ⊤ : Submodule Λ A))] :
    Module.Finite Λ (AdicCompletion I A) := by
  have : Module.Finite Λ
      (AdicCompletion I A ⧸ (I • ⊤ : Submodule Λ (AdicCompletion I A))) :=
    Module.Finite.of_surjective _ (surjective_mapQ_of_adicCompletion I A hI)
  have : Module.Finite (Λ ⧸ I)
      (AdicCompletion I A ⧸ (I • ⊤ : Submodule Λ (AdicCompletion I A))) :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  exact (finite_and_span_eq_top_of_adicComplete I (AdicCompletion I A)).1

end Completion

section Tate

variable (ϖ : Λ) (B : Type v) [AddCommGroup B] [Module Λ B]

/-- The `ϖ`-adic Tate module `T_ϖ B = lim (B[ϖⁿ⁺¹], ϖ)` of a `Λ`-module `B`: the sequences `t` of
elements of `B` with `ϖⁿ⁺¹ • t n = 0` and `ϖ • t (n + 1) = t n`. -/
def tateSubmodule : Submodule Λ (ℕ → B) where
  carrier := {t | ∀ n, ϖ ^ (n + 1) • t n = 0 ∧ ϖ • t (n + 1) = t n}
  zero_mem' := by simp
  add_mem' ha hb n := ⟨by simp [smul_add, (ha n).1, (hb n).1],
    by simp [smul_add, (ha n).2, (hb n).2]⟩
  smul_mem' c t ht n := ⟨by simp [smul_comm _ c, (ht n).1], by simp [smul_comm ϖ c, (ht n).2]⟩

variable {ϖ B}

lemma mem_tateSubmodule {t : ℕ → B} :
    t ∈ tateSubmodule ϖ B ↔ ∀ n, ϖ ^ (n + 1) • t n = 0 ∧ ϖ • t (n + 1) = t n :=
  Iff.rfl

/-- An element of the Tate module with vanishing first coordinate is divisible by `ϖ`. -/
lemma mem_smul_top_of_tateSubmodule {t : tateSubmodule ϖ B} (ht : (t : ℕ → B) 0 = 0) :
    t ∈ (Ideal.span {ϖ} • ⊤ : Submodule Λ (tateSubmodule ϖ B)) := by
  have h := (mem_tateSubmodule.1 t.2)
  have h' : ∀ n, ϖ ^ n • (t : ℕ → B) n = 0 := by
    intro n
    induction n with
    | zero => simp [ht]
    | succ n ih => rw [pow_succ, mul_smul, (h n).2, ih]
  have hs : (fun n ↦ (t : ℕ → B) (n + 1)) ∈ tateSubmodule ϖ B :=
    fun n ↦ ⟨h' (n + 1), (h (n + 1)).2⟩
  have heq : t = ϖ • (⟨_, hs⟩ : tateSubmodule ϖ B) :=
    Subtype.ext (funext fun n ↦ ((h n).2).symm)
  rw [heq]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top

instance : IsHausdorff (Ideal.span {ϖ}) (tateSubmodule ϖ B) where
  haus' t ht := by
    refine Subtype.ext (funext fun n ↦ ?_)
    have h := ht (n + 1)
    rw [SModEq.zero, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨s, -, hs⟩ := h
    rw [← hs]
    exact ((mem_tateSubmodule.1 s.2) n).1

/-- **Finiteness of a Tate module.** Over a noetherian `ϖ`-adically complete ring, the Tate
module `T_ϖ B` of a module whose `ϖ`-torsion `B[ϖ]` is finitely generated is finite: it is
`ϖ`-adically separated, and `T_ϖ B ⧸ ϖ` embeds in `B[ϖ]` through the first coordinate. -/
theorem finite_tateSubmodule [IsNoetherianRing Λ] [IsAdicComplete (Ideal.span {ϖ}) Λ]
    (hB : (LinearMap.ker (ϖ • LinearMap.id : B →ₗ[Λ] B)).FG) :
    Module.Finite Λ (tateSubmodule ϖ B) := by
  set K := LinearMap.ker (ϖ • LinearMap.id : B →ₗ[Λ] B)
  have : Module.Finite Λ K := Module.Finite.iff_fg.2 hB
  let p : tateSubmodule ϖ B →ₗ[Λ] K := LinearMap.codRestrict K
    ((LinearMap.proj 0).comp (tateSubmodule ϖ B).subtype) fun t ↦
      LinearMap.mem_ker.2 (by simpa using ((mem_tateSubmodule.1 t.2) 0).1)
  have hker : LinearMap.ker p ≤ (Ideal.span {ϖ} • ⊤ : Submodule Λ (tateSubmodule ϖ B)) :=
    fun t ht ↦ mem_smul_top_of_tateSubmodule (congrArg Subtype.val ht)
  have : Module.Finite Λ (LinearMap.range p) :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
  have : Module.Finite Λ (tateSubmodule ϖ B ⧸ LinearMap.ker p) :=
    Module.Finite.equiv p.quotKerEquivRange.symm
  have : Module.Finite Λ (tateSubmodule ϖ B ⧸
      (Ideal.span {ϖ} • ⊤ : Submodule Λ (tateSubmodule ϖ B))) :=
    Module.Finite.of_surjective _ (Submodule.factor_surjective hker)
  have : Module.Finite (Λ ⧸ Ideal.span {ϖ}) (tateSubmodule ϖ B ⧸
      (Ideal.span {ϖ} • ⊤ : Submodule Λ (tateSubmodule ϖ B))) :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  exact (finite_and_span_eq_top_of_adicComplete (Ideal.span {ϖ}) _).1

end Tate

end Module

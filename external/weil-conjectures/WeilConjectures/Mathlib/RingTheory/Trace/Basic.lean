/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Trace.Basic

/-!
# Trace duality for finite étale algebras over a field

The trace form of a finite étale algebra `A` over a field `K` is nondegenerate, so composing with
the trace `Tr_{A/K}` identifies `A`-linear forms on an `A`-module with `K`-linear forms.

## Main results

- `Algebra.Etale.exists_trace_mul_ne_zero`: the trace form of a finite étale algebra over a field
  is nondegenerate.
- `Algebra.Etale.linearMapEquivDual`: `Hom_A(P, A) ≃ Hom_K(P, K)` by composing with the trace.
-/

@[expose] public section

open Module

namespace Algebra

variable {K : Type*} [Field K]

/-- The trace of an element of a factor of a finite product of finite field extensions. -/
theorem trace_pi_single {ι : Type*} [Finite ι] [DecidableEq ι] (L : ι → Type*)
    [∀ i, Field (L i)] [∀ i, Algebra K (L i)] [∀ i, Module.Finite K (L i)] (i : ι) (y : L i) :
    Algebra.trace K (Π j, L j) (Pi.single i y) = Algebra.trace K (L i) y := by
  have := Fintype.ofFinite ι
  have h : Algebra.lmul K (Π j, L j) (Pi.single i y) =
      LinearMap.single K L i ∘ₗ (Algebra.lmul K (L i) y ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [Algebra.trace_apply, h, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have : (LinearMap.proj i : (Π j, L j) →ₗ[K] L i) ∘ₗ LinearMap.single K L i = LinearMap.id := by
    refine LinearMap.ext fun x ↦ ?_
    simp
  rw [this, LinearMap.comp_id, ← Algebra.trace_apply]

/-- The trace form of a finite étale algebra over a field is nondegenerate: every nonzero `a`
has `Tr(a b) ≠ 0` for some `b`. -/
theorem Etale.exists_trace_mul_ne_zero {A : Type*} [CommRing A] [Algebra K A] [Algebra.Etale K A]
    {a : A} (ha : a ≠ 0) : ∃ b, Algebra.trace K A (a * b) ≠ 0 := by
  classical
  obtain ⟨I, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  have := Fintype.ofFinite I
  have : ∀ i, Module.Finite K (L i) := fun i ↦ (hL i).1
  have : ∀ i, Algebra.IsSeparable K (L i) := fun i ↦ (hL i).2
  have : Module.Finite K A := Module.Finite.equiv e.symm.toLinearEquiv
  have htr (x : A) : Algebra.trace K A x = Algebra.trace K (Π j, L j) (e x) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
    congr 1
    ext y
    simp [LinearEquiv.conj_apply]
  obtain ⟨i, hi⟩ : ∃ i, e a i ≠ 0 := by
    by_contra! h
    exact ha (e.injective (by ext i; simp [h i]))
  obtain ⟨y, hy⟩ : ∃ y, Algebra.trace K (L i) (e a i * y) ≠ 0 := by
    by_contra! h
    exact hi ((traceForm_nondegenerate K (L i)).1 _ fun y ↦ by simpa using h y)
  refine ⟨e.symm (Pi.single i y), ?_⟩
  have hmul : e a * Pi.single i y = Pi.single i (e a i * y) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [htr, map_mul, AlgEquiv.apply_symm_apply, hmul, trace_pi_single]
  exact hy

variable {A : Type*} [CommRing A] [Algebra K A] [Algebra.Etale K A]

/-- For a finite étale `K`-algebra `A`, the trace pairing identifies `A` with its `K`-dual. -/
theorem Etale.bijective_traceDual :
    Function.Bijective (fun a : A ↦ (Algebra.trace K A).comp (Algebra.lmul K A a)) := by
  have : Module.Finite K A := FormallyUnramified.finite_of_free K A
  let τ : A →ₗ[K] Module.Dual K A :=
    { toFun a := (Algebra.trace K A).comp (Algebra.lmul K A a)
      map_add' a b := by ext; simp
      map_smul' c a := by ext; simp }
  have hinj : Function.Injective τ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra h
    obtain ⟨b, hb⟩ := exists_trace_mul_ne_zero (K := K) h
    exact hb (by simpa [τ] using congr($ha b))
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 hinj⟩

variable (K A) in
/-- **Trace duality for finite étale algebras.** For a finite étale `K`-algebra `A` and an
`A`-module `P`, composing with the trace `Tr_{A/K}` identifies `A`-linear forms on `P` with
`K`-linear forms. -/
noncomputable def Etale.linearMapEquivDual (P : Type*) [AddCommGroup P] [Module A P] [Module K P]
    [IsScalarTower K A P] : (P →ₗ[A] A) ≃ₗ[K] Module.Dual K P :=
  LinearEquiv.ofBijective
    { toFun φ := (Algebra.trace K A).comp (φ.restrictScalars K)
      map_add' φ ψ := by ext; simp
      map_smul' c φ := by ext; simp } <| by
    have hτ := bijective_traceDual (K := K) (A := A)
    refine ⟨fun φ ψ h ↦ LinearMap.ext fun p ↦ ?_, fun l ↦ ?_⟩
    · refine hτ.1 (LinearMap.ext fun b ↦ ?_)
      have := congr($h (b • p))
      simpa [mul_comm b] using this
    · choose t ht using fun p : P ↦ hτ.2 ((l : P →ₗ[K] K).comp
        ((LinearMap.toSpanSingleton A P p).restrictScalars K))
      have ht' (p : P) (b : A) : Algebra.trace K A (b * t p) = l (b • p) := by
        simpa [mul_comm] using congr($(ht p) b)
      let φ : P →ₗ[A] A :=
        { toFun := t
          map_add' p q := hτ.1 (LinearMap.ext fun b ↦ by
            change Algebra.trace K A (t (p + q) * b) = Algebra.trace K A ((t p + t q) * b)
            rw [add_mul, map_add, mul_comm, ht', mul_comm, ht', mul_comm, ht', smul_add,
              map_add])
          map_smul' a p := hτ.1 (LinearMap.ext fun b ↦ by
            change Algebra.trace K A (t (a • p) * b) = Algebra.trace K A ((a * t p) * b)
            rw [mul_comm, ht', show a * t p * b = (b * a) * t p by ring, ht', mul_smul]) }
      refine ⟨φ, LinearMap.ext fun p ↦ ?_⟩
      change Algebra.trace K A (t p) = l p
      simpa using ht' p 1

@[simp]
theorem Etale.linearMapEquivDual_apply (P : Type*) [AddCommGroup P] [Module A P] [Module K P]
    [IsScalarTower K A P] (φ : P →ₗ[A] A) (p : P) :
    linearMapEquivDual K A P φ p = Algebra.trace K A (φ p) :=
  rfl

end Algebra

end

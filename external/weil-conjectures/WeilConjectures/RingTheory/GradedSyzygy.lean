/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Finite
import WeilConjectures.RingTheory.GradedFreeCover
import WeilConjectures.RingTheory.GradedKernelInternal
import WeilConjectures.RingTheory.GradedNakayamaFree
import WeilConjectures.RingTheory.SecondSyzygyTorVanishes

/-!
# Graded syzygies over the two-variable polynomial ring

Source: Weil conjectures blueprint, `sec-picard-framework/det-thm-picard-duality`,
`theorem-riemann-roch-coherent-serre-duality`, proof, first sentence (blueprint:
lem-sc-p1-graded-syzygy).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A finite graded module over `k[x₀,x₁]` has a finite graded free resolution of length two.
Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, proof, first sentence
(blueprint: lem-sc-p1-graded-syzygy).

`homogeneousSubmodule` is the total-degree grading, extended by zero in negative degrees.
A finite homogeneous basis of degrees `-d a` presents a finite sum of shifts `S(d a)`:
the convention of `def-weil-pbc-proj-twisting-sheaf` (2) is `S(d)_n = S_{d+n}`.
The index `i : Fin 3` labels `F₀,F₁,F₂`; ranks may be zero and shifts may be any integer.
The sheaf conventions of `def-sc-p1-standard` do not enter this module statement.

Proof:
1. `exists_graded_free_cover` constructs a graded finite free surjection `q₀ : F₀ → M`.
2. `graded_kernel_internal_finite` makes its kernel internally graded and finite. Apply the
   cover theorem again to obtain a graded surjection `q₁ : F₁ → ker q₀`.
3. Apply the kernel theorem again to `q₁`. The theorem `second_syzygy_tor_vanishes`, using
   the Koszul resolution, Tor symmetry and dimension shifting, gives vanishing first Tor
   for `ker q₁`. The existing `graded_nakayama_free` gives a finite homogeneous basis.
4. Set `F₂ = ker q₁`, use its inclusion as `f₂`, and compose `q₁` with the inclusion of
   `ker q₀` to form `f₁`. Surjectivity of `q₁` identifies the image of `f₁` with `ker q₀`;
   injectivity of the kernel inclusion identifies `ker f₁` with the image of `f₂`.
   The inherited gradings give degree preservation. Package the three modules as a
   dependent family on `Fin 3`, negating the last basis degrees to match the shifts. -/
theorem exists_graded_free_resolution_two {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    [Module.Finite (MvPolynomial (Fin 2) k) M]
    (ℳ : ℤ → AddSubgroup M) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : M),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j → s • x ∈ ℳ ((n : ℤ) + j)) :
    ∃ (F : Fin 3 → ModuleCat.{u} (MvPolynomial (Fin 2) k))
      (𝒢 : ∀ i : Fin 3, ℤ → AddSubgroup (F i)) (r : Fin 3 → ℕ)
      (d : ∀ i : Fin 3, Fin (r i) → ℤ)
      (b : ∀ i : Fin 3, Module.Basis (Fin (r i)) (MvPolynomial (Fin 2) k) (F i))
      (f₂ : F 2 →ₗ[MvPolynomial (Fin 2) k] F 1)
      (f₁ : F 1 →ₗ[MvPolynomial (Fin 2) k] F 0)
      (f₀ : F 0 →ₗ[MvPolynomial (Fin 2) k] M),
      (∀ i : Fin 3, DirectSum.IsInternal (𝒢 i)) ∧
      (∀ (i : Fin 3) (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : F i),
        s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 i j →
          s • x ∈ 𝒢 i ((n : ℤ) + j)) ∧
      (∀ (i : Fin 3) (a : Fin (r i)), b i a ∈ 𝒢 i (-(d i a))) ∧
      (∀ (j : ℤ) (x : F 2), x ∈ 𝒢 2 j → f₂ x ∈ 𝒢 1 j) ∧
      (∀ (j : ℤ) (x : F 1), x ∈ 𝒢 1 j → f₁ x ∈ 𝒢 0 j) ∧
      (∀ (j : ℤ) (x : F 0), x ∈ 𝒢 0 j → f₀ x ∈ ℳ j) ∧
      Function.Injective f₂ ∧ LinearMap.range f₂ = LinearMap.ker f₁ ∧
      LinearMap.range f₁ = LinearMap.ker f₀ ∧ Function.Surjective f₀ := by
  classical
  let S := MvPolynomial (Fin 2) k
  obtain ⟨F₀, 𝒢₀, r₀, d₀, b₀, q₀, hG₀, hs₀, hb₀, hg₀, hq₀⟩ :=
    exists_graded_free_cover ℳ hℳ hsmul
  have : Module.Finite S F₀ := Module.Finite.of_basis b₀
  let 𝒦₁ : ℤ → AddSubgroup q₀.ker :=
    fun j ↦ (𝒢₀ j).comap q₀.ker.subtype.toAddMonoidHom
  obtain ⟨hK₁, hfiniteK₁, _⟩ :=
    graded_kernel_internal_finite 𝒢₀ hG₀ ℳ hℳ hs₀ q₀ hg₀
  have : Module.Finite S q₀.ker := hfiniteK₁
  have hsK₁ : ∀ (n : ℕ) (j : ℤ) (s : S) (x : q₀.ker),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒦₁ j →
        s • x ∈ 𝒦₁ ((n : ℤ) + j) := by
    intro n j s x hs hx
    exact hs₀ n j s x.val hs hx
  obtain ⟨F₁, 𝒢₁, r₁, d₁, b₁, q₁, hG₁, hs₁, hb₁, hg₁, hq₁⟩ :=
    exists_graded_free_cover 𝒦₁ hK₁ hsK₁
  have : Module.Finite S F₁ := Module.Finite.of_basis b₁
  let 𝒦₂ : ℤ → AddSubgroup q₁.ker :=
    fun j ↦ (𝒢₁ j).comap q₁.ker.subtype.toAddMonoidHom
  obtain ⟨hK₂, _, hgenK₂⟩ :=
    graded_kernel_internal_finite 𝒢₁ hG₁ 𝒦₁ hK₁ hs₁ q₁ hg₁
  have hsK₂ : ∀ (n : ℕ) (j : ℤ) (s : S) (x : q₁.ker),
      s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒦₂ j →
        s • x ∈ 𝒦₂ ((n : ℤ) + j) := by
    intro n j s x hs hx
    exact hs₁ n j s x.val hs hx
  obtain ⟨r₂, b₂, e₂, hb₂⟩ := graded_nakayama_free k q₁.ker 𝒦₂ hK₂ hsK₂ hgenK₂
    (second_syzygy_tor_vanishes F₀ F₁ r₀ r₁ b₀ b₁ q₀ hq₀ q₁ hq₁)
  let F₂ := ModuleCat.of S q₁.ker
  let f₁ : F₁ →ₗ[S] F₀ := q₀.ker.subtype.comp q₁
  have hgF₁ : ∀ (j : ℤ) (x : F₁), x ∈ 𝒢₁ j → f₁ x ∈ 𝒢₀ j := by
    intro j x hx
    exact hg₁ j x hx
  have hex₁ : LinearMap.range f₁ = LinearMap.ker q₀ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (q₁ y).property
    · intro hx
      obtain ⟨y, hy⟩ := hq₁ ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  have hex₂ : LinearMap.range q₁.ker.subtype = LinearMap.ker f₁ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (q₁ y.val).val = 0
      rw [LinearMap.mem_ker.mp y.property]
      rfl
    · intro hx
      have hx' : q₁ x = 0 := by
        apply Subtype.ext
        exact LinearMap.mem_ker.mp hx
      exact ⟨⟨x, LinearMap.mem_ker.mpr hx'⟩, rfl⟩
  refine ⟨![F₀, F₁, F₂],
    Fin.cases 𝒢₀ (Fin.cases 𝒢₁ (Fin.cases 𝒦₂ (fun i ↦ Fin.elim0 i))), ![r₀, r₁, r₂],
    Fin.cases d₀ (Fin.cases d₁ (Fin.cases (fun a ↦ -e₂ a) (fun i ↦ Fin.elim0 i))),
    Fin.cases b₀ (Fin.cases b₁ (Fin.cases b₂ (fun i ↦ Fin.elim0 i))), q₁.ker.subtype, f₁, q₀,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hex₂, hex₁, hq₀⟩
  · intro i
    fin_cases i
    · exact hG₀
    · exact hG₁
    · exact hK₂
  · intro i
    fin_cases i
    · exact hs₀
    · exact hs₁
    · exact hsK₂
  · intro i
    fin_cases i
    · exact hb₀
    · exact hb₁
    · simpa [Fin.cases, Fin.induction, Fin.induction.go] using hb₂
  · intro j x hx
    exact hx
  · simpa [Fin.cases, Fin.induction, Fin.induction.go] using hgF₁
  · simpa [Fin.cases, Fin.induction, Fin.induction.go] using hg₀
  · exact Subtype.val_injective

end MvPolynomial

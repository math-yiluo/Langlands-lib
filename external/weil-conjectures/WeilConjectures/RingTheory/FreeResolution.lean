/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Free resolutions of modules

This file collects elementary facts about resolutions of modules by free modules,
stated concretely in terms of `LinearMap.range` and `LinearMap.ker`.

* `Module.free_complex_maps_to_resolution`: a complex of free modules over `M` maps to any
  resolution of `N` over a linear map `M → N` (Stacks 00LS, part (1)).

The existence of finite free resolutions over Noetherian rings (Stacks 00LP) is
`Module.exists_finite_free_resolution` in `WeilConjectures.RingTheory.FiniteFreeResolution`.
-/

@[expose] public section

namespace Module

/-- Let `P` be a projective module, `f : A → B`, `g : B → C` linear maps with
`range f = ker g`, and `h : P → B` a linear map with `g ∘ h = 0`. Then `h` lifts along `f`. -/
theorem Projective.exists_comp_eq_of_range_eq_ker {R : Type*} [Ring R] {P A B C : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Projective R P] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (hfg : LinearMap.range f = LinearMap.ker g) (h : P →ₗ[R] B) (hgh : g ∘ₗ h = 0) :
    ∃ k : P →ₗ[R] A, f ∘ₗ k = h := by
  have hf (a : A) : f a ∈ LinearMap.ker g := hfg ▸ LinearMap.mem_range_self f a
  have hh (p : P) : h p ∈ LinearMap.ker g := by
    simpa using LinearMap.congr_fun hgh p
  obtain ⟨k, hk⟩ := projective_lifting_property (f.codRestrict _ hf) (h.codRestrict _ hh)
    (by
      rintro ⟨b, hb⟩
      obtain ⟨a, rfl⟩ : b ∈ LinearMap.range f := hfg ▸ hb
      exact ⟨a, rfl⟩)
  refine ⟨k, LinearMap.ext fun p => ?_⟩
  simpa using congrArg Subtype.val (LinearMap.congr_fun hk p)

/-- **A complex of free modules maps to a resolution** (Stacks 00LS, part (1)).
Let `φ : M → N` be a linear map, `⋯ → N₂ → N₁ → N₀ → N → 0` an exact sequence (with
augmentation `η` and differentials `∂ i : N_{i+1} → N_i`), and `⋯ → F₁ → F₀ → M` a complex of
free modules (augmentation `π`, differentials `δ i : F_{i+1} → F_i`, not necessarily exact).
Then there are linear maps `α i : F_i → N_i` with `η ∘ α 0 = φ ∘ π` and
`∂ i ∘ α (i + 1) = α i ∘ δ i` for all `i`.
(blueprint: `lem-weil-pbc-free-complex-maps-to-resolution`) -/
theorem free_complex_maps_to_resolution {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N)
    {N' : ℕ → Type*} [∀ i, AddCommGroup (N' i)] [∀ i, Module R (N' i)]
    (η : N' 0 →ₗ[R] N) (ϑ : ∀ i, N' (i + 1) →ₗ[R] N' i) (hη : Function.Surjective η)
    (hη₀ : LinearMap.range (ϑ 0) = LinearMap.ker η)
    (hϑ : ∀ i, LinearMap.range (ϑ (i + 1)) = LinearMap.ker (ϑ i))
    {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module.Free R (F i)]
    (π : F 0 →ₗ[R] M) (δ : ∀ i, F (i + 1) →ₗ[R] F i) (hπ : π ∘ₗ δ 0 = 0)
    (hδ : ∀ i, δ i ∘ₗ δ (i + 1) = 0) :
    ∃ α : ∀ i, F i →ₗ[R] N' i,
      η ∘ₗ α 0 = φ ∘ₗ π ∧ ∀ i, ϑ i ∘ₗ α (i + 1) = α i ∘ₗ δ i := by
  obtain ⟨α₀, hα₀⟩ := projective_lifting_property η (φ ∘ₗ π) hη
  obtain ⟨α₁, hα₁⟩ := Projective.exists_comp_eq_of_range_eq_ker hη₀ (α₀ ∘ₗ δ 0) (by
    rw [← LinearMap.comp_assoc, hα₀, LinearMap.comp_assoc, hπ, LinearMap.comp_zero])
  have step (i : ℕ) (p : {p : (F i →ₗ[R] N' i) × (F (i + 1) →ₗ[R] N' (i + 1)) //
      ϑ i ∘ₗ p.2 = p.1 ∘ₗ δ i}) :
      ∃ c : F (i + 2) →ₗ[R] N' (i + 2), ϑ (i + 1) ∘ₗ c = p.1.2 ∘ₗ δ (i + 1) :=
    Projective.exists_comp_eq_of_range_eq_ker (hϑ i) _ (by
      rw [← LinearMap.comp_assoc, p.2, LinearMap.comp_assoc, hδ, LinearMap.comp_zero])
  choose c hc using step
  let stage : (i : ℕ) → {p : (F i →ₗ[R] N' i) × (F (i + 1) →ₗ[R] N' (i + 1)) //
      ϑ i ∘ₗ p.2 = p.1 ∘ₗ δ i} := fun i =>
    Nat.rec ⟨(α₀, α₁), hα₁⟩ (fun i p => ⟨(p.1.2, c i p), hc i p⟩) i
  exact ⟨fun i => (stage i).1.1, hα₀, fun i => (stage i).2⟩

end Module

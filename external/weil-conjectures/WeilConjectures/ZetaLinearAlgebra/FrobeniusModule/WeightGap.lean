/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-!
# Frobenius-equivariant maps across a weight gap

The image of a Frobenius-equivariant linear map `g : M → N` is a Frobenius module, a quotient of
`M` and a subobject of `N`; over an algebraically closed field, if `g ≠ 0` it has an
eigenvalue, which is then an eigenvalue of both `M` and `N`. If `N` is dual to a Frobenius
module `D` up to a twist by `c`, every eigenvalue `α` of `N` gives the eigenvalue `c / α` of `D`.
Together: a Frobenius-equivariant map from a module of weights at most `w` to the dual of a
module of weights at most `-w`, twisted by `(-1)`, vanishes, its target having weights at least
`w + 2`.

## Main declarations

- `FrobeniusModule.range`: the image of a Frobenius-equivariant linear map.
- `FrobeniusModule.exists_hasEigenvalue_of_ne_zero`: a nonzero equivariant map has a common
  eigenvalue of source and target.
- `FrobeniusModule.hasEigenvalue_div_of_dual`: eigenvalues of a twisted dual.
- `FrobeniusModule.eq_zero_of_hasWeightsAtMost_of_dual`: the weight gap.
-/

@[expose] public section

universe u v t

namespace FrobeniusModule

variable {K : Type v} [Field K]

section Range

variable {M N : FrobeniusModule.{u, v} K} (g : M.carrier →ₗ[K] N.carrier)
  (hg : ∀ x, g (M.frobenius x) = N.frobenius (g x))

/-- The image of a Frobenius-equivariant linear map `g : M → N`: the Frobenius-stable subspace
`g(M)` of `N`, with the restricted Frobenius. -/
noncomputable def range : FrobeniusModule.{u, v} K where
  carrier := LinearMap.range g
  frobenius := LinearEquiv.ofInjectiveEndo
    (N.frobeniusEnd.restrict (p := LinearMap.range g) (q := LinearMap.range g) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨M.frobenius x, hg x⟩))
    (fun a b h ↦ Subtype.ext (N.frobenius.injective (congrArg Subtype.val h)))

include hg in
/-- A nonzero Frobenius-equivariant linear map between Frobenius modules over an algebraically
closed field has a common eigenvalue of source and target: an eigenvalue of its image. -/
theorem exists_hasEigenvalue_of_ne_zero [IsAlgClosed K] (hne : g ≠ 0) :
    ∃ α : K, M.frobeniusEnd.HasEigenvalue α ∧ N.frobeniusEnd.HasEigenvalue α := by
  have : Nontrivial (range g hg).carrier := by
    obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
      by_contra! h
      exact hne (LinearMap.ext h)
    exact ⟨⟨⟨g x, x, rfl⟩, 0, fun h ↦ hx (congrArg Subtype.val h)⟩⟩
  obtain ⟨α, hα⟩ := (range g hg).frobeniusEnd.exists_eigenvalue
  refine ⟨α, hasEigenvalue_of_surjective (N := range g hg) g.rangeRestrict
    (fun x ↦ Subtype.ext (hg x)) g.surjective_rangeRestrict hα,
    hasEigenvalue_of_injective (M := range g hg) (LinearMap.range g).subtype
    (fun _ ↦ rfl) Subtype.val_injective hα⟩

end Range

/-- Let `e : D ≃ N^∨` be a linear isomorphism with `e (F a) (F b) = c · e a b`, a perfect pairing
of `D` and `N` into the twist of `K` by `c`. Every eigenvalue `α` of the Frobenius of `N` is
nonzero, and `c / α` is an eigenvalue of the Frobenius of `D`: a linear form `f` with
`f ∘ F = α f` (an eigenvector of the transpose, which has the same characteristic polynomial)
corresponds to an eigenvector of `D` with eigenvalue `c / α`. -/
theorem hasEigenvalue_div_of_dual {N : FrobeniusModule.{u, v} K}
    {D : FrobeniusModule.{t, v} K} (e : D.carrier ≃ₗ[K] Module.Dual K N.carrier) (c : K)
    (he : ∀ a b, e (D.frobenius a) (N.frobenius b) = c * e a b) {α : K}
    (hα : N.frobeniusEnd.HasEigenvalue α) :
    α ≠ 0 ∧ D.frobeniusEnd.HasEigenvalue (c / α) := by
  have hα₀ : α ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, zero_smul] at hx
    exact hx.2 (N.frobenius.injective (hx.1.trans (map_zero _).symm))
  refine ⟨hα₀, ?_⟩
  have hT : Module.End.HasEigenvalue (N.frobeniusEnd.dualMap) α := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_dualMap,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hα
  obtain ⟨f, hf⟩ := hT.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hf
  have hf' (b : N.carrier) : f (N.frobenius b) = α * f b :=
    congrArg (fun φ : Module.Dual K N.carrier ↦ φ b) hf.1
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm f) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨e.injective ?_, (map_ne_zero_iff _ e.symm.injective).2 hf.2⟩
  refine LinearMap.ext fun b ↦ ?_
  obtain ⟨b, rfl⟩ := N.frobenius.surjective b
  change e (D.frobenius (e.symm f)) (N.frobenius b) = e ((c / α) • e.symm f) (N.frobenius b)
  rw [he, map_smul, LinearEquiv.apply_symm_apply, LinearMap.smul_apply, hf', smul_eq_mul]
  field_simp

/-- *Weight gap.* Let `M` have weights at most `w` and let `N` be dual, up to the twist by `q`,
to a module `D` of weights at most `-w`: `e : D ≃ N^∨` with `e (F a) (F b) = q · e a b`. Then
`N ≅ D^∨(-1)` has weights at least `w + 2`, and for `q > 1` every Frobenius-equivariant linear
map `g : M → N` vanishes: an eigenvalue `λ` of its image satisfies both `|ι λ|² ≤ q^w` and
`|ι λ|² ≥ q^{w+2}`. -/
theorem eq_zero_of_hasWeightsAtMost_of_dual [IsAlgClosed K] {M N : FrobeniusModule.{u, v} K}
    {D : FrobeniusModule.{t, v} K} (g : M.carrier →ₗ[K] N.carrier)
    (hg : ∀ x, g (M.frobenius x) = N.frobenius (g x)) {ι : K →+* ℂ} {q : ℕ} (hq : 1 < q)
    {w : ℝ} (hM : M.HasWeightsAtMost ι q w) (e : D.carrier ≃ₗ[K] Module.Dual K N.carrier)
    (he : ∀ a b, e (D.frobenius a) (N.frobenius b) = (q : K) * e a b)
    (hD : D.HasWeightsAtMost ι q (-w)) : g = 0 := by
  by_contra hne
  obtain ⟨α, hαM, hαN⟩ := exists_hasEigenvalue_of_ne_zero g hg hne
  obtain ⟨hα₀, hαD⟩ := hasEigenvalue_div_of_dual e (q : K) he hαN
  have h₁ := hM α hαM
  have h₂ := hD _ hαD
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (zero_lt_one.trans hq)
  have hια : 0 < ‖ι α‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hα₀)
  rw [map_div₀, norm_div, map_natCast, Complex.norm_natCast, div_le_iff₀ hια, neg_div,
    Real.rpow_neg hq₀.le] at h₂
  have h₃ : (q : ℝ) ≤ 1 := by
    calc (q : ℝ) ≤ ((q : ℝ) ^ (w / 2))⁻¹ * ‖ι α‖ := h₂
      _ ≤ ((q : ℝ) ^ (w / 2))⁻¹ * (q : ℝ) ^ (w / 2) :=
        mul_le_mul_of_nonneg_left h₁ (inv_nonneg.2 (Real.rpow_nonneg hq₀.le _))
      _ = 1 := inv_mul_cancel₀ (Real.rpow_pos_of_pos hq₀ _).ne'
  exact absurd h₃ (not_le.2 (by exact_mod_cast hq))

end FrobeniusModule

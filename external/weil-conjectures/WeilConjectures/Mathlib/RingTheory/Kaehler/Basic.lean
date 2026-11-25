/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.Defs

/-!
# Kähler differentials of a localization

## Main results

- `KaehlerDifferential.span_range_D_algebraMap_eq_top`: if `K` is a localization of `A`, then
  `Ω[K⁄R]` is spanned over `K` by the differentials of elements of `A`.
- `KaehlerDifferential.exists_span_D_algebraMap_eq_top`: if moreover `K` is a field and
  `Ω[K⁄R]` is one-dimensional, it is spanned by the differential of a single element of `A`.
-/

@[expose] public section

namespace KaehlerDifferential

variable {R A K : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- If `K` is a localization of `A`, then `Ω[K⁄R]` is spanned over `K` by the differentials
`d a` of elements `a : A`: `d (a / s) = s⁻¹ • (d a - (a / s) • d s)`. -/
theorem span_range_D_algebraMap_eq_top [CommRing K] [Algebra A K] [Algebra R K]
    [IsScalarTower R A K] (M : Submonoid A) [IsLocalization M K] :
    Submodule.span K (Set.range fun a : A ↦ D R K (algebraMap A K a)) = ⊤ := by
  rw [eq_top_iff, ← span_range_derivation, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  have hs := IsLocalization.map_units K s
  have key : algebraMap A K s • D R K (IsLocalization.mk' K a s) =
      D R K (algebraMap A K a) - IsLocalization.mk' K a s • D R K (algebraMap A K s) := by
    rw [eq_sub_iff_add_eq, ← Derivation.leibniz, mul_comm, IsLocalization.mk'_spec]
  have : D R K (IsLocalization.mk' K a s) =
      ((hs.unit⁻¹ : Kˣ) : K) • (algebraMap A K s • D R K (IsLocalization.mk' K a s)) := by
    rw [smul_smul, IsUnit.val_inv_mul, one_smul]
  rw [SetLike.mem_coe, this, key]
  exact Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span ⟨a, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)))

/-- If a field `K` is a localization of `A` and `Ω[K⁄R]` is one-dimensional over `K`, then
`Ω[K⁄R]` is spanned by `d a` for a single `a : A`. -/
theorem exists_span_D_algebraMap_eq_top [Field K] [Algebra A K] [Algebra R K]
    [IsScalarTower R A K] (M : Submonoid A) [IsLocalization M K]
    (h : Module.finrank K Ω[K⁄R] = 1) :
    ∃ a : A, Submodule.span K {D R K (algebraMap A K a)} = ⊤ := by
  obtain ⟨a, ha⟩ : ∃ a : A, D R K (algebraMap A K a) ≠ 0 := by
    by_contra! H
    have := span_range_D_algebraMap_eq_top (R := R) (K := K) M
    rw [show (fun a : A ↦ D R K (algebraMap A K a)) = fun _ ↦ 0 from funext H, Set.range_const,
      Submodule.span_zero_singleton] at this
    rw [← finrank_top, ← this, finrank_bot] at h
    exact zero_ne_one h
  exact ⟨a, (finrank_eq_one_iff_of_nonzero _ ha).mp h⟩

end KaehlerDifferential

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Extensions of perfect fields are separable; perfect closures in an algebraic closure

* `Algebra.isSeparableExtension_of_perfectField`: every field extension of a perfect field is
  separable in the sense of `Algebra.IsSeparableExtension` (Stacks 030W).
* `perfectClosure_subset_perfectClosure_algebraicClosure`: for `K ⊆ L` and
  `Ω := AlgebraicClosure L`, the perfect closure of `K` in `Ω` is contained in the perfect
  closure of `L` in `Ω`; `perfectClosureAlgebraicClosureHom` is the resulting `K`-algebra map.
-/

@[expose] public section

universe u v

/-- Every field extension of a perfect field is separable (Stacks 030W): every finitely
generated intermediate field is separably generated. -/
theorem Algebra.isSeparableExtension_of_perfectField (k : Type u) (K : Type v) [Field k]
    [Field K] [Algebra k K] [PerfectField k] : Algebra.IsSeparableExtension k K := by
  intro F hF
  have : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  exact ⟨(s : Set F), hs, hsep⟩

section PerfectClosure

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]

/-- The perfect closure of `K` inside `Ω := AlgebraicClosure L` is a perfect field. -/
theorem perfectField_perfectClosure_algebraicClosure :
    PerfectField (perfectClosure K (AlgebraicClosure L)) :=
  inferInstance

/-- For fields `K ⊆ L` and `Ω := AlgebraicClosure L`, the perfect closure of `K` in `Ω` is
contained (as a subset of `Ω`) in the perfect closure of `L` in `Ω`. -/
theorem perfectClosure_subset_perfectClosure_algebraicClosure :
    (perfectClosure K (AlgebraicClosure L) : Set (AlgebraicClosure L)) ⊆
      perfectClosure L (AlgebraicClosure L) := by
  intro x hx
  obtain ⟨q, hq⟩ := ExpChar.exists K
  have : ExpChar L q := expChar_of_injective_algebraMap (algebraMap K L).injective q
  rw [SetLike.mem_coe, mem_perfectClosure_iff_pow_mem q] at hx ⊢
  obtain ⟨n, y, hy⟩ := hx
  exact ⟨n, algebraMap K L y, by
    rw [← hy, IsScalarTower.algebraMap_apply K L (AlgebraicClosure L)]⟩

/-- The `K`-algebra map from the perfect closure of `K` in `Ω := AlgebraicClosure L` to the
perfect closure of `L` in `Ω`, given by the inclusion of subsets of `Ω`. -/
noncomputable def perfectClosureAlgebraicClosureHom :
    perfectClosure K (AlgebraicClosure L) →ₐ[K] perfectClosure L (AlgebraicClosure L) where
  toFun x := ⟨x.1, perfectClosure_subset_perfectClosure_algebraicClosure K L x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := Subtype.ext (IsScalarTower.algebraMap_apply K L (AlgebraicClosure L) _).symm

@[simp]
theorem perfectClosureAlgebraicClosureHom_apply (x : perfectClosure K (AlgebraicClosure L)) :
    (perfectClosureAlgebraicClosureHom K L x : AlgebraicClosure L) = x :=
  rfl

end PerfectClosure

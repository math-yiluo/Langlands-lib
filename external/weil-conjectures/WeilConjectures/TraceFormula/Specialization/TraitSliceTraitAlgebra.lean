/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitCompositumMap
public import WeilConjectures.RingTheory.DiscreteValuationRing.SeparablyClosedFractionField

/-!

# The change of trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` as a change of traits with geometric generic points

Let `K / k'` be a field extension, `R₁ = k'⟦t⟧`, `R = K⟦t⟧` with the coefficientwise map, and
`Ω = (Frac k'⟦t⟧)^alg`, `Ω_K = (Frac K⟦t⟧)^alg` with the embedding `Ω ⟶ Ω_K`
(`AlgebraicGeometry.traitGenericFieldMap`, as the local instance
`AlgebraicGeometry.traitGenericFieldAlgebra`). This file records the remaining facts under which
the general theory of `AlgebraicGeometry.traitTensorCompositum` applies:

* `K⟦t⟧ ⟶ Ω_K` is injective and algebraic
  (`AlgebraicGeometry.faithfulSMul_powerSeries_traitGenericField`,
  `AlgebraicGeometry.isAlgebraic_powerSeries_traitGenericField`);
* `Spec(Ω ⊗_{k'⟦t⟧} K⟦t⟧)` is a single point when `k'` is separably closed and `K` is algebraically
  closed of transcendence degree `≤ 1` over `k'`
  (`AlgebraicGeometry.subsingleton_primeSpectrum_traitGenericField_tensorProduct_powerSeries`):
  `Ω ⊗_{k'⟦t⟧} K⟦t⟧ = Ω ⊗_{k'((t))} K((t))`, as `K((t))` is obtained from `K⟦t⟧` by inverting
  `t`, and `k'((t))` is separably closed in `K((t))`
  (`AlgebraicGeometry.mem_range_traitLaurentFieldMap_of_isSeparable`).

-/

@[expose] public section

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- `K⟦t⟧ ⟶ Ω_K` is injective. -/
instance faithfulSMul_powerSeries_traitGenericField :
    FaithfulSMul (PowerSeries K) (traitGenericField K) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    rw [IsScalarTower.algebraMap_eq (PowerSeries K) (FractionRing (PowerSeries K))
      (traitGenericField K)]
    exact (algebraMap (FractionRing (PowerSeries K)) (traitGenericField K)).injective.comp
      (IsFractionRing.injective _ _)

/-- `Ω_K` is algebraic over `K⟦t⟧`. -/
instance isAlgebraic_powerSeries_traitGenericField :
    Algebra.IsAlgebraic (PowerSeries K) (traitGenericField K) :=
  have : Algebra.IsAlgebraic (PowerSeries K) (FractionRing (PowerSeries K)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  Algebra.IsAlgebraic.trans (PowerSeries K) (FractionRing (PowerSeries K)) _

variable {K} [IsSepClosed k'] [IsAlgClosed K]

/-- **`Spec(Ω ⊗_{k'⟦t⟧} K⟦t⟧)` has at most one point**, for `k'` separably closed and `K`
algebraically closed of transcendence degree `≤ 1` over `k'`: `Ω ⊗_{k'⟦t⟧} K⟦t⟧` is
`Ω ⊗_{k'((t))} K((t))`, and `k'((t))` is separably closed in `K((t))`. -/
theorem subsingleton_primeSpectrum_traitGenericField_tensorProduct_powerSeries
    (htr : Algebra.trdeg k' K ≤ 1) :
    Subsingleton (PrimeSpectrum (traitGenericField k' ⊗[PowerSeries k'] PowerSeries K)) := by
  let R₁ := PowerSeries k'
  let R := PowerSeries K
  let F₁ := FractionRing R₁
  let F := FractionRing R
  let : Algebra F₁ F := (traitLaurentFieldMap k' K).toAlgebra
  have : IsScalarTower R₁ F₁ F := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply R₁ R F]
    exact (traitLaurentFieldMap_algebraMap k' K a).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors R₁)) F :=
    IsDiscreteValuationRing.isLocalization_map_nonZeroDivisors
      (maximalIdeal_powerSeries_eq_map k' K)
  have : Algebra.IsPushout R₁ F₁ R F :=
    (Algebra.isPushout_of_isLocalization (nonZeroDivisors R₁) (A := F₁) (T := R) (B := F)).symm
  have := PrimeSpectrum.subsingleton_tensorProduct_of_forall_mem_range
    (M := traitGenericField k') (F := F₁) (E := F)
    (fun c hc ↦ mem_range_traitLaurentFieldMap_of_isSeparable htr c hc)
  let e : traitGenericField k' ⊗[F₁] F ≃ₐ[F₁] traitGenericField k' ⊗[R₁] R :=
    (Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.IsPushout.equiv R₁ F₁ R F).symm).trans
      (Algebra.TensorProduct.cancelBaseChange R₁ F₁ F₁ (traitGenericField k') R)
  exact (PrimeSpectrum.comap_injective_of_surjective e.toRingHom e.surjective).subsingleton

end AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- The image of `Frac K⟦t⟧` in `Ω_K` lies in the compositum `L = Ω(K⟦t⟧)`. -/
lemma algebraMap_fractionRing_mem_traitTensorCompositum (a : FractionRing (PowerSeries K)) :
    algebraMap (FractionRing (PowerSeries K)) (traitGenericField K) a ∈
      traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K) := by
  obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries K) a
  rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact IntermediateField.div_mem _ (IntermediateField.subset_adjoin _ _ ⟨r, rfl⟩)
    (IntermediateField.subset_adjoin _ _ ⟨s, rfl⟩)

end AlgebraicGeometry

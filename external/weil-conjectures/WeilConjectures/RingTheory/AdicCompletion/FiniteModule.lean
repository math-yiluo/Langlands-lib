/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Finite modules over adically complete rings

We prove two standard facts about modules over adically complete rings.

* If `A` is `I`-adically complete, `M` is `I`-adically Hausdorff and `M / IM` is finite, then
  any lifts of generators of `M / IM`  `M`; in particular `M` is finite
  (Stacks, Lemma 031D).
* If `R` is Noetherian and `J`-adically complete, every finite `R`-module is `J`-adically
  complete (Stacks, Lemma 00MA).

## Main results

- `IsPrecomplete.pi`
- `Submodule.span_range_eq_top_of_isPrecomplete`
- `Module.finite_and_span_eq_top_of_isAdicComplete`
- `AdicCompletion.of_bijective_of_isAdicComplete`
- `isAdicComplete_of_finite_of_isNoetherianRing`

## References

- Stacks Project, Lemma 10.96.12, <https://stacks.math.columbia.edu/tag/031D>
- Stacks Project, Lemma 10.97.1, <https://stacks.math.columbia.edu/tag/00MA>
-/

@[expose] public section

open Submodule TensorProduct

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- A finite product of copies of an `I`-adically precomplete ring is precomplete. -/
theorem IsPrecomplete.pi (ι : Type*) [Finite ι] [IsPrecomplete I A] :
    IsPrecomplete I (ι → A) := by
  cases nonempty_fintype ι
  classical
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  choose a ha using fun j ↦ AdicCompletion.of_surjective I A
    (AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ A) y j)
  refine ⟨a, (AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ A)).injective ?_⟩
  ext1 j
  rw [AdicCompletion.piEquivOfFintype_apply, ← ha j]
  simp [AdicCompletion.pi, AdicCompletion.map_of]

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- If `A` is `I`-adically precomplete and `M` is `I`-adically Hausdorff, then finitely many
elements of `M` whose images generate `M / IM` generate `M`. -/
theorem Submodule.span_range_eq_top_of_isPrecomplete [IsPrecomplete I A] [IsHausdorff I M]
    {r : ℕ} (x : Fin r → M)
    (hx : span A (Set.range ((I • ⊤ : Submodule A M).mkQ ∘ x)) = ⊤) :
    span A (Set.range x) = ⊤ := by
  have := IsPrecomplete.pi I (Fin r)
  rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
  apply surjective_of_mkQ_comp_surjective (I := I)
  rw [← LinearMap.range_eq_top, LinearMap.range_comp, Fintype.range_linearCombination,
    Submodule.map_span, ← hx, ← Set.range_comp]

/-- Let `A` be `I`-adically complete and `M` an `A`-module with `⋂ₙ IⁿM = 0` such that
`M / IM` is finitely generated. Then any `x₁, …, xᵣ ∈ M` whose images generate `M / IM`
generate `M`; in particular `M` is a finite `A`-module.
(blueprint: `lem-weil-pbc-finite-over-complete-ring`) -/
theorem Module.finite_and_span_eq_top_of_isAdicComplete [IsAdicComplete I A] [IsHausdorff I M]
    [Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))] :
    Module.Finite A M ∧ ∀ (r : ℕ) (x : Fin r → M),
      span A (Set.range ((I • ⊤ : Submodule A M).mkQ ∘ x)) = ⊤ →
        span A (Set.range x) = ⊤ := by
  classical
  refine ⟨?_, fun r x hx ↦ Submodule.span_range_eq_top_of_isPrecomplete I x hx⟩
  obtain ⟨r, y, hy⟩ :=
    Module.Finite.exists_fin (R := A) (M := M ⧸ (I • ⊤ : Submodule A M))
  choose x hx using fun i ↦ (I • ⊤ : Submodule A M).mkQ_surjective (y i)
  have hxy : (I • ⊤ : Submodule A M).mkQ ∘ x = y := funext hx
  refine ⟨⟨Finset.univ.image x, ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine Submodule.span_range_eq_top_of_isPrecomplete I x ?_
  rw [hxy]
  exact hy

section Noetherian

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R) [IsAdicComplete J R]
variable (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- Let `R` be a Noetherian ring which is `J`-adically complete and `N` a finite `R`-module.
Then the canonical map `N → lim N / JⁿN` is bijective.
(blueprint: `lem-weil-pbc-finite-module-complete-over-complete-noetherian`) -/
theorem AdicCompletion.of_bijective_of_isAdicComplete :
    Function.Bijective (AdicCompletion.of J N) := by
  let e : R ≃ₗ[R] AdicCompletion J R :=
    LinearEquiv.ofBijective (AdicCompletion.of J R) (AdicCompletion.of_bijective_iff.mpr ‹_›)
  have h : (AdicCompletion.of J N : N → AdicCompletion J N) =
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J N).restrictScalars R ∘
        LinearEquiv.rTensor N e ∘ (TensorProduct.lid R N).symm := by
    funext x
    have h1 : AdicCompletion.of J R 1 = 1 := by
      simpa using (AdicCompletion.algebraMap_apply (S := R) J (1 : R)).symm
    simp [e, h1]
  rw [h]
  exact (LinearEquiv.bijective _).comp ((LinearEquiv.bijective _).comp (LinearEquiv.bijective _))

/-- A finite module over a Noetherian `J`-adically complete ring is `J`-adically complete. -/
theorem isAdicComplete_of_finite_of_isNoetherianRing : IsAdicComplete J N :=
  AdicCompletion.of_bijective_iff.mp (AdicCompletion.of_bijective_of_isAdicComplete J N)

end Noetherian

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.WeilObjectComparisonDevissage

/-!
# The local comparison of Weil complexes with Weil objects

`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison ι K` asks for a Weil object `K'` whose
global traces (through `ι`) are the compactly supported Frobenius traces of `K` and whose local
traces are the trace function of `K`. By the trace formula for Weil objects
(`ProEtale.CondensedRing.weilTraceFormula`), the global clause follows from the local clause as
soon as `K` satisfies the Grothendieck–Lefschetz formula of the zeta-function chapter, and
conversely.

## Main definitions

- `AlgebraicGeometry.WeilComplex.HasLocalWeilObjectComparison`: the trace function of `K` is the
  local trace function of a Weil object, through `ι`.
- `AlgebraicGeometry.WeilComplex.SatisfiesLefschetz`: `K` satisfies the Grothendieck–Lefschetz
  formula (blueprint `theorem-grothendieck-lefschetz-trace-formula--8`).

## Main results

- `AlgebraicGeometry.WeilComplex.hasWeilObjectComparison_iff`: the comparison is the local
  comparison together with the Grothendieck–Lefschetz formula.
- Closure of both properties under isomorphisms, shifts and extensions.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] fact_ringChar_prime_of_finite
  ProEtale.CondensedRing.fintypeFrobeniusFixedPoints

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

open ProEtale.CondensedRing

/-- A Weil complex `K` on `X₀` *has a local Weil object comparison along* `ι` if there is a Weil
object `K'` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity of `X₀` such that, for every `n` and every
`𝔽_{q^{n+1}}`-rational point `y` of `X₀`, `ι` of the local trace of `K'` at `y` is the trace
function `t_K(y)` of `K` in degree `n + 1`. This is the second clause of
`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`. -/
def HasLocalWeilObjectComparison
    (ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l)
    (K : WeilComplex k₀ l X) : Prop :=
  ∃ K' : WeilBoundedConstructible l (Iso.refl (overSpec (k₀ := k₀) X)).hom,
    ∀ (n : ℕ)
      (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))),
      ι (weilStalkTraceAlternatingSum l (n + 1) _
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2 K') =
        K.traceFunction (n + 1) y

/-- A Weil complex `K` on `X₀` *satisfies the Grothendieck–Lefschetz formula* if, for every `n`,
`∑ᵢ (-1)ⁱ Tr(F^{n+1} | H_cⁱ(X, K)) = ∑_{y ∈ X₀(𝔽_{q^{n+1}})} t_K(y)`
(blueprint `theorem-grothendieck-lefschetz-trace-formula--8`). -/
def SatisfiesLefschetz (K : WeilComplex k₀ l X) : Prop :=
  ∀ n : ℕ, ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
      ((K.compactlySupportedCohomology i).frobeniusEnd ^ (n + 1)) =
    ∑ᶠ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)),
      K.traceFunction (n + 1) y

variable {ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l}

/-- The rational points of `X₀` over a finite extension of `k₀` form a finite set. -/
instance finite_fieldPoints (n : ℕ) :
    Finite ((X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :=
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  Scheme.Hom.finite_fieldPoints _ _

/-- If the local traces of a Weil object `K'` are, through `ι`, the trace function of `K`, then
`ι` of the global trace of `K'` in degree `n + 1` is the sum of the trace function of `K` over the
`𝔽_{q^{n+1}}`-rational points, by the trace formula `weilTraceFormula` for `e = 𝟙`. -/
theorem map_weilStalkTraceAlternatingSum_eq_finsum_traceFunction (K : WeilComplex k₀ l X)
    (K' : WeilBoundedConstructible l (Iso.refl (overSpec (k₀ := k₀) X)).hom)
    (hloc : ∀ (n : ℕ)
      (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))),
      ι (weilStalkTraceAlternatingSum l (n + 1) _
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2 K') =
        K.traceFunction (n + 1) y) (n : ℕ) :
    ι (weilStalkTraceAlternatingSum l (n + 1) (specAlgebraicClosure k₀)
        (specAlgebraicClosure_comp_pow (n + 1))
        ((weilCompactSupportCohomology l (Iso.refl _)).obj K')) =
      ∑ᶠ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)),
        K.traceFunction (n + 1) y := by
  set eqv := (fieldPointsEquivFrobeniusFixedPointsRefl (X := overSpec (k₀ := k₀) X) n).symm
  have heqv : ∀ x, ι (weilStalkTraceAlternatingSum l (n + 1) x.1 x.2.2 K') =
      K.traceFunction (n + 1) (eqv x) := by
    intro x
    obtain ⟨y, rfl⟩ := (fieldPointsEquivFrobeniusFixedPointsRefl n).surjective x
    exact (hloc n y).trans (congrArg (K.traceFunction (n + 1))
      ((fieldPointsEquivFrobeniusFixedPointsRefl n).symm_apply_apply y).symm)
  rw [weilTraceFormula l (Iso.refl (overSpec (k₀ := k₀) X)) ⟨1, Nat.one_pos, Iso.pow_refl 1⟩ K'
    (n + 1), map_sum, ← finsum_eq_sum_of_fintype]
  exact (finsum_congr heqv).trans (finsum_comp_equiv eqv)

/-- **The comparison is the local comparison plus the Grothendieck–Lefschetz formula.** By the
trace formula for Weil objects, the global clause of the comparison is equivalent, given the
local clause, to the Grothendieck–Lefschetz formula for `K`. -/
theorem hasWeilObjectComparison_iff (K : WeilComplex k₀ l X) :
    HasWeilObjectComparison ι K ↔ HasLocalWeilObjectComparison ι K ∧ SatisfiesLefschetz K := by
  refine ⟨fun ⟨K', hglob, hloc⟩ ↦ ⟨⟨K', hloc⟩, fun n ↦ ?_⟩, fun ⟨⟨K', hloc⟩, hK⟩ ↦
    ⟨K', fun n ↦ ?_, hloc⟩⟩
  · rw [← hglob n, map_weilStalkTraceAlternatingSum_eq_finsum_traceFunction K K' hloc]
  · rw [map_weilStalkTraceAlternatingSum_eq_finsum_traceFunction K K' hloc, hK n]

/-- A Weil complex with a comparison has a local comparison. -/
theorem HasWeilObjectComparison.hasLocalWeilObjectComparison {K : WeilComplex k₀ l X}
    (hK : HasWeilObjectComparison ι K) : HasLocalWeilObjectComparison ι K :=
  ((hasWeilObjectComparison_iff K).1 hK).1

/-- A Weil complex with a comparison satisfies the Grothendieck–Lefschetz formula. -/
theorem HasWeilObjectComparison.satisfiesLefschetz {K : WeilComplex k₀ l X}
    (hK : HasWeilObjectComparison ι K) : SatisfiesLefschetz K :=
  ((hasWeilObjectComparison_iff K).1 hK).2

namespace HasLocalWeilObjectComparison

/-- The local comparison only depends on the Weil complex up to isomorphism. -/
theorem of_iso {K L : WeilComplex k₀ l X} (e : K ≅ L) (hK : HasLocalWeilObjectComparison ι K) :
    HasLocalWeilObjectComparison ι L := by
  obtain ⟨K', hloc⟩ := hK
  exact ⟨K', fun n y ↦ (hloc n y).trans (traceFunction_eq_of_iso e (n + 1) y)⟩

/-- The local comparison for `K` gives the local comparison for every shift `K[a]`. -/
theorem shift {K : WeilComplex k₀ l X} (hK : HasLocalWeilObjectComparison ι K) (a : ℤ) :
    HasLocalWeilObjectComparison ι (K⟦a⟧) := by
  obtain ⟨K', hloc⟩ := hK
  rcases Int.even_or_odd a with ha | ha
  · refine ⟨K', fun n y ↦ ?_⟩
    rw [traceFunction_shift, Int.negOnePow_even a ha, Units.val_one, one_smul, hloc]
  · obtain ⟨C, hCloc, -⟩ :=
      WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_neg l
        (Iso.refl (overSpec (k₀ := k₀) X)) K'
    refine ⟨C, fun n y ↦ ?_⟩
    rw [traceFunction_shift, Int.negOnePow_odd a ha, Units.val_neg, Units.val_one,
      neg_smul, one_smul, hCloc, map_neg, hloc]

/-- The local comparison is stable under extensions. -/
theorem of_distTriang (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _)
    (h₁ : HasLocalWeilObjectComparison ι T.obj₁) (h₃ : HasLocalWeilObjectComparison ι T.obj₃) :
    HasLocalWeilObjectComparison ι T.obj₂ := by
  obtain ⟨K₁, hloc₁⟩ := h₁
  obtain ⟨K₃, hloc₃⟩ := h₃
  obtain ⟨B, hBloc, -⟩ :=
    WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_add l
      (Iso.refl (overSpec (k₀ := k₀) X)) K₁ K₃
  refine ⟨B, fun n y ↦ ?_⟩
  rw [traceFunction_eq_add_of_distTriang T hT, hBloc, map_add, hloc₁, hloc₃]

end HasLocalWeilObjectComparison

namespace SatisfiesLefschetz

/-- The Grothendieck–Lefschetz formula only depends on the Weil complex up to isomorphism. -/
theorem of_iso {K L : WeilComplex k₀ l X} (e : K ≅ L) (hK : SatisfiesLefschetz K) :
    SatisfiesLefschetz L := fun n ↦ by
  rw [← finsum_trace_compactlySupportedCohomology_congr e (n + 1), hK n]
  exact finsum_congr fun y ↦ traceFunction_eq_of_iso e (n + 1) y

/-- The Grothendieck–Lefschetz formula for `K` gives it for every shift `K[a]`: both sides are
multiplied by `(-1)ᵃ`. -/
theorem shift {K : WeilComplex k₀ l X} (hK : SatisfiesLefschetz K) (a : ℤ) :
    SatisfiesLefschetz (K⟦a⟧) := fun n ↦ by
  rw [finsum_trace_compactlySupportedCohomology_shift, hK n, smul_finsum]
  exact finsum_congr fun y ↦ (traceFunction_shift K a (n + 1) y).symm

/-- The Grothendieck–Lefschetz formula is stable under extensions. -/
theorem of_distTriang (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _)
    (h₁ : SatisfiesLefschetz T.obj₁) (h₃ : SatisfiesLefschetz T.obj₃) :
    SatisfiesLefschetz T.obj₂ := fun n ↦ by
  rw [finsum_trace_compactlySupportedCohomology_eq_add_of_distTriang T hT, h₁ n, h₃ n,
    ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun y ↦ (traceFunction_eq_add_of_distTriang T hT (n + 1) y).symm

end SatisfiesLefschetz

end WeilComplex

end AlgebraicGeometry

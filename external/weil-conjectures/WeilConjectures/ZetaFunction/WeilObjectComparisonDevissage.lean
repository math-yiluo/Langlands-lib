/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv
public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.TraceFormula.WeilTraceSplitTriangle
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.ShiftedSheaf
public import WeilConjectures.WeilSheaf.TraceFunctionOps
public import WeilConjectures.WeilSheaf.TraceTriangleAdditivity
public import WeilConjectures.WeilSheaf.VerdierDualFinite

/-!
# Dévissage for the comparison of Weil complexes with Weil objects

The zeta-function chapter works with the Weil complexes `AlgebraicGeometry.WeilComplex` on a
scheme `X₀` over a finite field `k₀`, the trace formula chapter with the Weil objects
`ProEtale.CondensedRing.WeilBoundedConstructible` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity of `X₀`.
Given an additive map `ι : End (𝟙 Mod_{Spec k̄}) ⟶ ℚ̄_ℓ`, a Weil complex `K` *has a Weil object
comparison along `ι`* (`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`) if some Weil
object `K'` has, through `ι`, the compactly supported Frobenius traces and the trace function
of `K`.

Both sides of the comparison are additive in distinguished triangles and change sign under the
shift. Hence the Weil complexes with a comparison along a fixed `ι` contain every Weil complex
as soon as they contain the Weil sheaves placed in degree `0`
(`AlgebraicGeometry.WeilComplex.hasWeilObjectComparison_of_toComplex`): by induction on the
amplitude, along the truncation triangles of the canonical t-structure.

## Main definitions

- `AlgebraicGeometry.WeilComplex.overSpec`: `X₀` as an object of `Over (Spec k₀)`.
- `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`: the traces of `K` are those of a
  Weil object, through `ι`.

## Main results

- `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison.of_iso`,
  `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison.shift`,
  `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison.of_distTriang`: the comparison is
  invariant under isomorphisms and shifts and stable under extensions.
- `AlgebraicGeometry.WeilComplex.hasWeilObjectComparison_of_toComplex`: dévissage to Weil
  sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The ring characteristic of a finite field is prime. -/
lemma fact_ringChar_prime_of_finite : Fact (ringChar k₀).Prime :=
  ⟨CharP.char_is_prime k₀ (ringChar k₀)⟩

attribute [local instance] fact_ringChar_prime_of_finite

/-- The scheme `X₀` over `Spec k₀` as an object of `Over (Spec k₀)`. -/
noncomputable abbrev WeilComplex.overSpec (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Over (Spec (.of k₀)) :=
  Over.mk (X ↘ Spec (CommRingCat.of k₀))

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    LocallyOfFiniteType (WeilComplex.overSpec (k₀ := k₀) X).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))

instance [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    QuasiCompact (WeilComplex.overSpec (k₀ := k₀) X).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))

instance [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    IsSeparated (WeilComplex.overSpec (k₀ := k₀) X).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

open ProEtale.CondensedRing

/-- A Weil complex `K` on `X₀` *has a Weil object comparison along* an additive map
`ι : End (𝟙_ Mod_{Spec k̄}) ⟶ ℚ̄_ℓ` if there is a Weil object `K'` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the
identity of `X₀` such that, for every `n`,
* `ι` of the global trace of `K'` in degree `n + 1` is
  `∑ᵢ (-1)ⁱ Tr(F^{n+1} | H_c^i(X₀ ⊗ k̄, K))`, and
* for every `𝔽_{q^{n+1}}`-rational point `y` of `X₀`, `ι` of the local trace of `K'` at `y`
  is the trace function `t_K(y)` of `K` in degree `n + 1`. -/
def HasWeilObjectComparison
    (ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l)
    (K : WeilComplex k₀ l X) : Prop :=
  ∃ K' : WeilBoundedConstructible l (Iso.refl (overSpec (k₀ := k₀) X)).hom,
    (∀ n : ℕ, ι (weilStalkTraceAlternatingSum l (n + 1) (specAlgebraicClosure k₀)
        (specAlgebraicClosure_comp_pow (n + 1))
        ((weilCompactSupportCohomology l (Iso.refl _)).obj K')) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ (n + 1))) ∧
    ∀ (n : ℕ)
      (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))),
      ι (weilStalkTraceAlternatingSum l (n + 1) _
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2 K') =
        K.traceFunction (n + 1) y

end WeilComplex

namespace WeilComplex

open ProEtale.CondensedRing

variable {ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l}

namespace HasWeilObjectComparison

/-- The comparison only depends on the Weil complex up to isomorphism. -/
theorem of_iso {K L : WeilComplex k₀ l X} (e : K ≅ L) (hK : HasWeilObjectComparison ι K) :
    HasWeilObjectComparison ι L := by
  obtain ⟨K', hglob, hloc⟩ := hK
  exact ⟨K', fun n ↦ (hglob n).trans (finsum_trace_compactlySupportedCohomology_congr e (n + 1)),
    fun n y ↦ (hloc n y).trans (traceFunction_eq_of_iso e (n + 1) y)⟩

/-- The comparison for `K` gives the comparison for every shift `K[a]`: the traces of `K[a]` are
those of `K` multiplied by `(-1)ᵃ`, which are those of `K'` or of a Weil object with the negated
traces. -/
theorem shift {K : WeilComplex k₀ l X} (hK : HasWeilObjectComparison ι K) (a : ℤ) :
    HasWeilObjectComparison ι (K⟦a⟧) := by
  obtain ⟨K', hglob, hloc⟩ := hK
  rcases Int.even_or_odd a with ha | ha
  · refine ⟨K', fun n ↦ ?_, fun n y ↦ ?_⟩
    · rw [finsum_trace_compactlySupportedCohomology_shift, Int.negOnePow_even a ha, Units.val_one,
        one_smul, hglob]
    · rw [traceFunction_shift, Int.negOnePow_even a ha, Units.val_one, one_smul, hloc]
  · obtain ⟨C, hCloc, hCglob⟩ :=
      WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_neg l
        (Iso.refl (overSpec (k₀ := k₀) X)) K'
    refine ⟨C, fun n ↦ ?_, fun n y ↦ ?_⟩
    · rw [finsum_trace_compactlySupportedCohomology_shift, Int.negOnePow_odd a ha, Units.val_neg,
        Units.val_one, neg_smul, one_smul, hCglob, map_neg, hglob]
    · rw [traceFunction_shift, Int.negOnePow_odd a ha, Units.val_neg, Units.val_one,
        neg_smul, one_smul, hCloc, map_neg, hloc]

/-- The comparison is stable under extensions: for a distinguished triangle
`K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]`, comparisons for `K₁` and `K₃` give one for `K₂`, through a Weil object
whose traces are the sums. -/
theorem of_distTriang (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _)
    (h₁ : HasWeilObjectComparison ι T.obj₁) (h₃ : HasWeilObjectComparison ι T.obj₃) :
    HasWeilObjectComparison ι T.obj₂ := by
  obtain ⟨K₁, hglob₁, hloc₁⟩ := h₁
  obtain ⟨K₃, hglob₃, hloc₃⟩ := h₃
  obtain ⟨B, hBloc, hBglob⟩ :=
    WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_add l
      (Iso.refl (overSpec (k₀ := k₀) X)) K₁ K₃
  refine ⟨B, fun n ↦ ?_, fun n y ↦ ?_⟩
  · rw [finsum_trace_compactlySupportedCohomology_eq_add_of_distTriang T hT, hBglob, map_add,
      hglob₁, hglob₃]
  · rw [traceFunction_eq_add_of_distTriang T hT, hBloc, map_add, hloc₁, hloc₃]

end HasWeilObjectComparison

/-- A zero Weil complex has a comparison along `ι` as soon as the Weil sheaves in degree `0` do:
it is isomorphic to the zero Weil sheaf placed in degree `0`. -/
theorem hasWeilObjectComparison_of_isZero
    (h : ∀ G : WeilSheaf k₀ l X, HasWeilObjectComparison ι (WeilSheaf.toComplex.obj G))
    {K : WeilComplex k₀ l X} (hK : IsZero K) : HasWeilObjectComparison ι K :=
  open ZeroObject in (h 0).of_iso ((WeilSheaf.toComplex.map_isZero (isZero_zero _)).iso hK)

/-- **Dévissage of the comparison to Weil sheaves, by the amplitude.** If every Weil sheaf placed
in degree `0` has a comparison along `ι`, then so does every Weil complex concentrated in degrees
`[a, a + n - 1]`, by induction on `n` along the truncation triangles. -/
theorem hasWeilObjectComparison_of_isGE_of_isLE
    (h : ∀ G : WeilSheaf k₀ l X, HasWeilObjectComparison ι (WeilSheaf.toComplex.obj G))
    (n : ℕ) : ∀ (a : ℤ) (K : WeilComplex k₀ l X), (tStructure k₀ l X).IsGE K a →
      (tStructure k₀ l X).IsLE K (a + n - 1) → HasWeilObjectComparison ι K := by
  set t := tStructure k₀ l X
  induction n with
  | zero =>
    intro a K _ hK
    have : t.IsLE K (a - 1) := t.isLE_of_le K (a + ((0 : ℕ) : ℤ) - 1) _ (by push_cast; lia)
    exact hasWeilObjectComparison_of_isZero h (t.isZero K (a - 1) a (by lia))
  | succ n ih =>
    intro a K _ hK
    have : t.IsLE K (a + n) := t.isLE_of_le K (a + ((n + 1 : ℕ) : ℤ) - 1) _ (by push_cast; lia)
    set T := (t.triangleLEGE (a + n - 1) (a + n) (by lia)).obj K
    have hT : T ∈ distTriang _ := t.triangleLEGE_distinguished _ _ _ K
    have h₁ : t.IsGE T.obj₁ a := inferInstanceAs (t.IsGE ((t.truncLE (a + n - 1)).obj K) a)
    have h₁' : t.IsLE T.obj₁ (a + n - 1) :=
      inferInstanceAs (t.IsLE ((t.truncLE (a + n - 1)).obj K) (a + n - 1))
    have : t.IsGE T.obj₃ (a + n) := inferInstanceAs (t.IsGE ((t.truncGE (a + n)).obj K) (a + n))
    have : t.IsLE T.obj₃ (a + n) := inferInstanceAs (t.IsLE ((t.truncGE (a + n)).obj K) (a + n))
    obtain ⟨e⟩ := nonempty_iso_shift_toComplex_homologySheaf T.obj₃ (a + n)
    exact HasWeilObjectComparison.of_distTriang T hT (ih a T.obj₁ h₁ h₁')
      (((h _).shift _).of_iso e.symm)

/-- **Dévissage of the comparison to Weil sheaves.** If every Weil sheaf placed in degree `0` has
a comparison along `ι`, then so does every Weil complex. -/
theorem hasWeilObjectComparison_of_toComplex
    (h : ∀ G : WeilSheaf k₀ l X, HasWeilObjectComparison ι (WeilSheaf.toComplex.obj G))
    (K : WeilComplex k₀ l X) : HasWeilObjectComparison ι K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ := K.property
  have : (tStructure k₀ l X).IsGE K a := (tStructure_isGE_iff K a).2 ha
  have : (tStructure k₀ l X).IsLE K b := (tStructure_isLE_iff K b).2 hb
  have : (tStructure k₀ l X).IsLE K (a + (b - a + 1).toNat - 1) :=
    (tStructure k₀ l X).isLE_of_le K b _ (by lia)
  exact hasWeilObjectComparison_of_isGE_of_isLE h (b - a + 1).toNat a K inferInstance inferInstance

end WeilComplex

end AlgebraicGeometry

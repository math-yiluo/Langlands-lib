/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.TraceFunctionCongr
public import WeilConjectures.ZetaFunction.WeilObjectComparison

/-!
# The Grothendieck–Lefschetz trace formula and point counts

Let `X₀` be a separated scheme of finite type over the finite field `k₀ = 𝔽_q` and let `K` be a
Weil complex on `X₀`. The Grothendieck–Lefschetz trace formula says that for every `m ≥ 1`

`∑ᵢ (-1)ⁱ Tr(Fᵐ | H_c^i(X₀ ⊗ k̄, K)) = ∑_{y ∈ X₀(𝔽_{qᵐ})} t_K(y)`,

where `t_K` is the trace function of `K` (`AlgebraicGeometry.WeilComplex.traceFunction`). For
the constant Weil sheaf `ℚ̄_ℓ` every local trace is `1`, and the right hand side is the number
`N_m = #X₀(𝔽_{qᵐ})` of `𝔽_{qᵐ}`-rational points. If `X₀` is proper, compactly supported
cohomology is ordinary cohomology.

The trace formula over `ℚ̄_ℓ` itself is the blueprint node
`theorem-grothendieck-lefschetz-trace-formula--8` of the trace formula chapter (subsection
`theorem-trace-formula-euler-product`); it is stated here for the Weil complexes of this repository,
whose compactly supported cohomology is
`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`, and is proved in that chapter.

## Main statements

- `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq`: the trace
  formula over `ℚ̄_ℓ` (`theorem-grothendieck-lefschetz-trace-formula--8`).
- `AlgebraicGeometry.WeilSheaf.traceFunction_adicConstant`: the trace function of the constant
  Weil sheaf is `1`.
- `AlgebraicGeometry.WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.pointCount_eq_finsum_trace_cohomology`: the point-counting
  trace formula (`corollary-point-counting-zeta-function--2`).
- `AlgebraicGeometry.WeilComplex.sum_traceFunction_eq_finsum_trace` and
  `AlgebraicGeometry.WeilSheaf.pointCount_eq_sum_trace_cohomology`: the Grothendieck–Lefschetz
  trace formula and its every-iterate form for a smooth proper variety
  (`theorem-grothendieck-lefschetz-trace-formula--8`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Separated

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--8` (Grothendieck–Lefschetz formula over
`ℚ̄_ℓ`, subsection `theorem-trace-formula-euler-product` of the trace formula chapter): for a Weil
complex `K` on a separated `k₀`-scheme `X₀` of finite type and every `m ≥ 1`,

`∑ᵢ (-1)ⁱ Tr(F^m | H_c^i(X₀ ⊗ k̄, K)) = ∑_{y ∈ X₀(𝔽_{qᵐ})} ∑ⱼ (-1)ʲ Tr(F_{y,m} | 𝓗ʲ(K)_ȳ)`.

The inner sum on the right is the trace function `t_K(y)` of `K`; both sums are finite
(`AlgebraicGeometry.WeilComplex.exists_subsingleton_compactlySupportedCohomology`,
`AlgebraicGeometry.Scheme.Hom.finite_fieldPoints`). It is deduced from the trace formula for
Weil objects `ProEtale.CondensedRing.weilTraceFormula`
(`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq_of_comparison`). -/
theorem WeilComplex.finsum_trace_compactlySupportedCohomology_eq (K : WeilComplex k₀ l X)
    {m : ℕ} (hm : 1 ≤ m) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
        K.traceFunction m y :=
  K.finsum_trace_compactlySupportedCohomology_eq_of_comparison hm

end Separated

section Stalks

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Isomorphic Weil sheaves have stalks with the same Frobenius trace. -/
theorem WeilSheaf.trace_frobeniusEnd_stalkAt_congr {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    LinearMap.trace (PadicAlgCl l) _ (G.stalkAt s m hs).frobeniusEnd =
      LinearMap.trace (PadicAlgCl l) _ (F.stalkAt s m hs).frobeniusEnd := by
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_stalkAt_of_iso s m hs e
  simpa only [pow_one] using E.trace_frobeniusEnd_pow 1

variable (k₀ l) in
/-- The stalks `Γ(Spec k̄, s^* ℚ̄_ℓ)` of the constant Weil sheaf are one-dimensional: the unit
section `ℚ̄_ℓ ⟶ Γ(Spec k̄, s^* ℚ̄_ℓ)` is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_unitSection`). -/
theorem WeilSheaf.finrank_stalkAt_adicConstant
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).stalkAt s m hs).carrier =
      1 := by
  let e₁ : (WeilCoefficients.toModuleCat l).obj (𝟙_ (WeilCoefficients.{u} l)) ≃ₗ[PadicAlgCl l]
      PadicAlgCl l :=
    { toFun x := ULift.down (x : ULift.{u + 1} (PadicAlgCl l))
      invFun x := (ULift.up x : ULift.{u + 1} (PadicAlgCl l))
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  exact (WeilCoefficients.linearEquivOfIso (asIso (ProEtale.unitSection l s)).symm).finrank_eq.trans
    (e₁.finrank_eq.trans (Module.finrank_self _))

variable (k₀ l) in
/-- The Frobenius of every stalk of the constant Weil sheaf has trace `1`. -/
theorem WeilSheaf.trace_frobeniusEnd_stalkAt_adicConstant
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    LinearMap.trace (PadicAlgCl l) _ ((WeilSheaf.adicConstant k₀ l X).stalkAt s m hs).frobeniusEnd =
      1 := by
  rw [FrobeniusModule.frobeniusEnd, WeilSheaf.adicConstant_stalkAt_frobenius,
    LinearEquiv.refl_toLinearMap, LinearMap.trace_id,
    WeilSheaf.finrank_stalkAt_adicConstant k₀ l s m hs, Nat.cast_one]

end Stalks

section Constant

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace function of the constant Weil sheaf `ℚ̄_ℓ` is `1`: its stalks are one-dimensional
and every local Frobenius is the identity
(`AlgebraicGeometry.WeilSheaf.adicConstant_stalkAt_frobenius`). -/
theorem WeilSheaf.traceFunction_adicConstant (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (WeilSheaf.adicConstant k₀ l X).traceFunction n y = 1 :=
  WeilSheaf.trace_frobeniusEnd_stalkAt_adicConstant k₀ l _ _ _

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprints `corollary-point-counting-zeta-function--2` and
`theorem-grothendieck-lefschetz-trace-formula--8` (constant-sheaf clause) (point-counting trace
formula, subsection `theorem-trace-formula-euler-product` of the trace formula chapter), compactly
supported form: for a separated `k₀`-scheme `X₀` of finite type and every `m ≥ 1`,

`#X₀(𝔽_{qᵐ}) = ∑ᵢ (-1)ⁱ Tr(Fᵐ | H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ))`.

It is the trace formula
`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq` for the constant
Weil sheaf, whose trace function is `1`. -/
theorem WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology {m : ℕ}
    (hm : 1 ≤ m) :
    ((X ↘ Spec (CommRingCat.of k₀)).pointCount m : PadicAlgCl l) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l X).compactlySupportedCohomology i).frobeniusEnd ^ m) := by
  have : Finite (FiniteField.galoisExtension k₀ m) := Module.finite_of_finite k₀
  have := (X ↘ Spec (CommRingCat.of k₀)).finite_fieldPoints (FiniteField.galoisExtension k₀ m)
  let _ := Fintype.ofFinite
    ((X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m))
  have h := (WeilSheaf.toComplex.obj
    (WeilSheaf.adicConstant k₀ l X)).finsum_trace_compactlySupportedCohomology_eq hm
  simp only [WeilComplex.traceFunction_toComplex, WeilSheaf.traceFunction_adicConstant] at h
  have h1 : (∑ᶠ _ : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
      (1 : PadicAlgCl l)) = ((X ↘ Spec (CommRingCat.of k₀)).pointCount m : PadicAlgCl l) := by
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_one,
      Scheme.Hom.pointCount, Nat.card_eq_fintype_card]
  rw [h1] at h
  exact h.symm

end Constant

section Proper

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprints `corollary-point-counting-zeta-function--2` and
`theorem-grothendieck-lefschetz-trace-formula--8` (proper clause) (point-counting trace formula),
proper form: for a proper `k₀`-scheme `X₀` and every `m ≥ 1`,

`#X₀(𝔽_{qᵐ}) = ∑ᵢ (-1)ⁱ Tr(Fᵐ | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))`,

compactly supported cohomology being ordinary cohomology
(`AlgebraicGeometry.WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology`). -/
theorem WeilSheaf.pointCount_eq_finsum_trace_cohomology {m : ℕ} (hm : 1 ≤ m) :
    ((X ↘ Spec (CommRingCat.of k₀)).pointCount m : PadicAlgCl l) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd ^ m) := by
  rw [WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology k₀ l X hm]
  refine finsum_congr fun i ↦ ?_
  obtain ⟨e⟩ := WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) i
  exact congrArg _ (e.trace_frobeniusEnd_pow m).symm

/-- Blueprints `theorem-grothendieck-lefschetz-trace-formula--8` and
`theorem-grothendieck-lefschetz-trace-formula--8` (general clause) (Grothendieck–Lefschetz trace
formula): for a Weil complex `K` on a separated `k₀`-scheme `Y₀` of finite type and `m ≥ 1`, the sum
over `y ∈ Y₀(𝔽_{qᵐ})` of the local alternating traces `t_K(y)` is the alternating trace of `Fᵐ` on
`H_c^•(Y₀ ⊗ k̄, K)`; for `K = ℚ̄_ℓ` and a proper `X₀` this specializes to
`#X₀(𝔽_{qᵐ}) = ∑ᵢ (-1)ⁱ Tr(Fᵐ | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))`. -/
theorem WeilComplex.finsum_traceFunction_eq_and_pointCount_eq {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l Y) {m : ℕ}
    (hm : 1 ≤ m) :
    ∑ᶠ y : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
        K.traceFunction m y =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) ∧
    ((X ↘ Spec (CommRingCat.of k₀)).pointCount m : PadicAlgCl l) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd ^ m) :=
  ⟨(K.finsum_trace_compactlySupportedCohomology_eq hm).symm,
    WeilSheaf.pointCount_eq_finsum_trace_cohomology k₀ l X hm⟩

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--8` (every-iterate
Grothendieck–Lefschetz identity), smooth proper case: for `X₀` smooth and proper of pure dimension
`d` and every `n ≥ 1`,

`N_n(X₀) = ∑_{i = 0}^{2d} (-1)ⁱ Tr(Fⁿ | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))`,

the cohomology vanishing outside `[0, 2d]`
(`AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant`). The general identity for
a Weil complex on a separated scheme of finite type is
`AlgebraicGeometry.WeilComplex.finsum_traceFunction_eq_and_pointCount_eq`. -/
theorem WeilSheaf.pointCount_eq_sum_trace_cohomology (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {n : ℕ} (hn : 1 ≤ n) :
    ((X ↘ Spec (CommRingCat.of k₀)).pointCount n : PadicAlgCl l) =
      ∑ i ∈ Finset.range (2 * d + 1), (-1) ^ i * LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd ^ n) := by
  rw [WeilSheaf.pointCount_eq_finsum_trace_cohomology k₀ l X hn,
    finsum_eq_sum_of_support_subset (s := (Finset.range (2 * d + 1)).map Nat.castEmbedding) _ ?_,
    Finset.sum_map]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Nat.castEmbedding_apply, Int.coe_negOnePow_natCast, zsmul_eq_mul]
    push_cast
    rfl
  · intro i hi
    by_contra h
    have hi' : i < 0 ∨ 2 * (d : ℤ) < i := by
      by_contra hc
      exact h (Finset.mem_map.2 ⟨i.toNat, Finset.mem_range.2 (by omega),
        by rw [Nat.castEmbedding_apply, Int.toNat_of_nonneg (by omega)]⟩)
    have := WeilSheaf.subsingleton_cohomology_adicConstant k₀ l X d hi'
    exact hi (by
      dsimp only
      rw [Subsingleton.elim (((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd ^ n) 0,
        map_zero, smul_zero])

end Proper

end AlgebraicGeometry

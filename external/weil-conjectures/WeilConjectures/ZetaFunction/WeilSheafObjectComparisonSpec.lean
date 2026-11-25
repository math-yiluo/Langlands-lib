/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.TraceFormula.WeilScalarUnit
public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilSheaf.PointTraceComparison
public import WeilConjectures.ZetaFunction.WeilObjectComparisonDevissage

/-!
# Weil sheaves on `Spec k₀` have the traces of Weil objects

The comparison of the Weil sheaves of the zeta-function chapter with the Weil objects of the
trace formula chapter (`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`) holds on the
base `Spec k₀`, through the canonical identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`
(`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_spec`). A Weil sheaf `G` on
`Spec k₀` is a finite-dimensional `ℚ̄_ℓ`-vector space `V = Γ(Spec k̄, G)` with an automorphism
`F`, and both of its traces in degree `m ≥ 1` are `Tr(Fᵐ | V) = ∑ λᵐ`, the sum running over the
eigenvalues `λ` of `F` with multiplicity
(`AlgebraicGeometry.WeilSheaf.finsum_trace_compactlySupportedCohomology_spec`,
`AlgebraicGeometry.WeilSheaf.traceFunction_toComplex_spec_eq_trace_globalSections`). The Weil
object is the direct sum of the units twisted by the eigenvalues
(`ProEtale.CondensedRing.weilScalarUnit`), whose local traces are `λᵐ`.

## Main results

- `ProEtale.CondensedRing.exists_weilBoundedConstructible_trace_eq_sum_pow`: for a multiset `s`
  of units of `ℚ̄_ℓ`, a Weil object for the identity whose local traces in degree `m` are
  `∑_{c ∈ s} cᵐ`.
- `AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_spec`: the comparison on
  `Spec k₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Weil objects with prescribed traces.** For a multiset `s` of units of `ℚ̄_ℓ` there is a
Weil object `K` for the identity of `X`, the direct sum of the units twisted by the elements of
`s`, whose local traces in degree `n + 1` are `∑_{c ∈ s} c^{n+1}` and whose global trace is
`∑_{c ∈ s} c^{n+1}` times the number of points of degree `n + 1`. -/
theorem exists_weilBoundedConstructible_trace_eq_sum_pow (s : Multiset (_root_.PadicAlgCl ℓ)ˣ) :
    ∃ K : WeilBoundedConstructible ℓ (Iso.refl X).hom,
      (∀ (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
        (hx : x ≫ ((Iso.refl X).pow (n + 1)).hom.left =
          ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x),
        endTensorUnitRingEquiv ℓ (AlgebraicClosure k)
            (weilStalkTraceAlternatingSum ℓ (n + 1) x hx K) =
          (s.map fun c : (_root_.PadicAlgCl ℓ)ˣ ↦ (c : _root_.PadicAlgCl ℓ) ^ (n + 1)).sum) ∧
      ∀ n : ℕ, endTensorUnitRingEquiv ℓ (AlgebraicClosure k)
          (weilStalkTraceAlternatingSum ℓ (n + 1) (specAlgebraicClosure k)
            (specAlgebraicClosure_comp_pow (n + 1))
            ((weilCompactSupportCohomology ℓ (Iso.refl X)).obj K)) =
        (s.map fun c : (_root_.PadicAlgCl ℓ)ˣ ↦ (c : _root_.PadicAlgCl ℓ) ^ (n + 1)).sum *
          Nat.card (frobeniusFixedPoints (Iso.refl X) (n + 1)) := by
  have he : ∃ m > 0, (Iso.refl X).pow m = Iso.refl X := ⟨1, Nat.one_pos, Iso.pow_refl 1⟩
  induction s using Multiset.induction_on with
  | empty =>
    obtain ⟨Z, -, -, -, hZ, -⟩ :=
      WeilBoundedConstructible.exists_isDistTriang_isZero ℓ (weilScalarUnit ℓ (Iso.refl X) 1)
    refine ⟨Z, fun n x hx ↦ ?_, fun n ↦ ?_⟩
    · rw [weilStalkTraceAlternatingSum_eq_zero_of_isZero ℓ n x hx hZ, map_zero,
        Multiset.map_zero, Multiset.sum_zero]
    · rw [weilStalkTraceAlternatingSum_weilCompactSupportCohomology_eq_zero_of_isZero ℓ _ n hZ,
        map_zero, Multiset.map_zero, Multiset.sum_zero, zero_mul]
  | cons c s ih =>
    obtain ⟨K, hl, hg⟩ := ih
    obtain ⟨B, hBl, hBg⟩ := WeilBoundedConstructible.exists_weilStalkTraceAlternatingSum_eq_add ℓ
      (Iso.refl X) (weilScalarUnit ℓ (Iso.refl X) c) K
    refine ⟨B, fun n x hx ↦ ?_, fun n ↦ ?_⟩
    · rw [hBl, map_add, endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit, hl,
        Multiset.map_cons, Multiset.sum_cons]
    · rw [hBg, map_add, endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit ℓ _ he,
        hg, Multiset.map_cons, Multiset.sum_cons, add_mul]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] fact_ringChar_prime_of_finite

open ProEtale.CondensedRing in
/-- **Weil sheaves on `Spec k₀` have the traces of Weil objects**: the comparison
`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison` holds on the base `Spec k₀`, through the
canonical identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`. Both traces of `G` in degree `m ≥ 1` are
`Tr(Fᵐ | Γ(Spec k̄, G)) = ∑ λᵐ` over the eigenvalues `λ` of the Frobenius `F`, and those are the
traces of the direct sum of the units twisted by the `λ`. -/
theorem hasWeilObjectComparison_toComplex_spec (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) :
    WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom (toComplex.obj G) := by
  set f := G.globalSections.frobeniusEnd
  have hdet : IsUnit (LinearMap.det f) := LinearEquiv.isUnit_det' G.globalSections.frobenius
  let s : Multiset (_root_.PadicAlgCl l)ˣ := f.charpoly.roots.pmap (fun a ha ↦ Units.mk0 a ha)
    fun a ha h0 ↦ LinearMap.zero_notMem_roots_charpoly hdet (h0 ▸ ha)
  have hs (m : ℕ) : (s.map fun c : (_root_.PadicAlgCl l)ˣ ↦ (c : _root_.PadicAlgCl l) ^ m).sum =
      LinearMap.trace (_root_.PadicAlgCl l) _ (f ^ m) := by
    rw [LinearMap.trace_pow_eq_sum_pow_roots_charpoly, Multiset.map_pmap]
    exact congrArg Multiset.sum (Multiset.pmap_eq_map _ _ _ _)
  obtain ⟨K, hl, hg⟩ := exists_weilBoundedConstructible_trace_eq_sum_pow l
    (X := WeilComplex.overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀))) s
  have hcard (n : ℕ) : Nat.card (frobeniusFixedPoints
      (Iso.refl (WeilComplex.overSpec (k₀ := k₀) (Spec (CommRingCat.of k₀)))) (n + 1)) = 1 :=
    (Nat.card_congr (fieldPointsEquivFrobeniusFixedPointsRefl n).symm).trans
      (Nat.card_eq_one_iff_unique.2
        ⟨inferInstanceAs (Subsingleton ((Spec (CommRingCat.of k₀) ↘
          Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)))),
          inferInstanceAs (Nonempty ((Spec (CommRingCat.of k₀) ↘
          Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))))⟩)
  refine ⟨K, fun n ↦ ?_, fun n y ↦ ?_⟩
  · change endTensorUnitRingEquiv l (AlgebraicClosure k₀) _ = _
    rw [hg, hcard, Nat.cast_one, mul_one, hs, finsum_trace_compactlySupportedCohomology_spec]
  · change endTensorUnitRingEquiv l (AlgebraicClosure k₀) _ = _
    rw [hl, hs, traceFunction_toComplex_spec_eq_trace_globalSections G (n + 1) (by omega) y]

end AlgebraicGeometry.WeilSheaf

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkExact
public import WeilConjectures.LinearAlgebra.TraceLongExactSequenceFinsum
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map
public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.CohomologyShift
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.TraceFunction

/-!
# Additivity of the two sides of the Grothendieck–Lefschetz formula

For a Weil complex `K` on a separated `k₀`-scheme `X` of finite type, both sides of the
Grothendieck–Lefschetz trace formula,

* the global side `∑ᵢ (-1)ⁱ Tr(Fᵐ | H_cⁱ(X ⊗ k̄, K))`, and
* the local side, the trace function `t_K(y) = ∑ⱼ (-1)ʲ Tr(F_y | 𝓗ʲ(K)_ȳ)`,

are additive in distinguished triangles: both come from long exact sequences of finite-dimensional
spaces with compatible Frobenius endomorphisms (the long exact sequence of compactly supported
cohomology, resp. the stalks of the long exact sequence of cohomology sheaves), along which the
alternating sum of traces is additive
(`LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact`). The global side moreover
changes by `(-1)ᵃ` under the shift `[a]` and is invariant under isomorphisms.

## Main results

- `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq_add_of_distTriang`:
  the global side is additive in distinguished triangles.
- `AlgebraicGeometry.WeilComplex.traceFunction_eq_add_of_distTriang`: the trace function is
  additive in distinguished triangles.
- `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_shift`: the global side
  of `K[a]` is `(-1)ᵃ` times that of `K`.
- `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_congr`: the global side
  is invariant under isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section Global

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The compactly supported cohomology of a Weil complex vanishes outside a finite set of
degrees. -/
theorem exists_finset_subsingleton_compactlySupportedCohomology (K : WeilComplex k₀ l X) :
    ∃ s : Finset ℤ, ∀ r ∉ s, Subsingleton (K.compactlySupportedCohomology r).carrier := by
  obtain ⟨a, b, h⟩ := exists_subsingleton_compactlySupportedCohomology K
  refine ⟨Finset.Icc a b, fun r hr ↦ h r ?_⟩
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hr
  exact hr

/-- **Additivity of the global side of the Grothendieck–Lefschetz formula.** For a distinguished
triangle `K₁ → K₂ → K₃ → K₁[1]` of Weil complexes, the alternating sum of the traces of `Fᵐ` on
compactly supported cohomology is additive, by the long exact sequence of compactly supported
cohomology. -/
theorem finsum_trace_compactlySupportedCohomology_eq_add_of_distTriang
    (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _) (m : ℕ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((T.obj₂.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((T.obj₁.compactlySupportedCohomology i).frobeniusEnd ^ m) +
        ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((T.obj₃.compactlySupportedCohomology i).frobeniusEnd ^ m) := by
  obtain ⟨s₁, h₁⟩ := exists_finset_subsingleton_compactlySupportedCohomology T.obj₁
  obtain ⟨s₂, h₂⟩ := exists_finset_subsingleton_compactlySupportedCohomology T.obj₂
  obtain ⟨s₃, h₃⟩ := exists_finset_subsingleton_compactlySupportedCohomology T.obj₃
  exact LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact
    (fun i ↦ (T.obj₁.compactlySupportedCohomology i).carrier)
    (fun i ↦ (T.obj₂.compactlySupportedCohomology i).carrier)
    (fun i ↦ (T.obj₃.compactlySupportedCohomology i).carrier)
    (fun i ↦ compactlySupportedCohomologyMap T.mor₁ i)
    (fun i ↦ compactlySupportedCohomologyMap T.mor₂ i)
    (compactlySupportedCohomologyδ T)
    (fun i ↦ exact_compactlySupportedCohomologyMap T i hT)
    (fun i i' h ↦ exact_compactlySupportedCohomologyδ_left T i i' h hT)
    (fun i i' h ↦ exact_compactlySupportedCohomologyδ_right T i i' h hT)
    _ _ _
    (fun i ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (compactlySupportedCohomologyMap_frobenius T.mor₁ i) m)
    (fun i ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (compactlySupportedCohomologyMap_frobenius T.mor₂ i) m)
    (fun i i' h ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (compactlySupportedCohomologyδ_frobenius T i i' h) m)
    (s₁ ∪ s₂ ∪ s₃)
    (fun i hi ↦ h₁ i fun h ↦ hi (by simp [h]))
    (fun i hi ↦ h₂ i fun h ↦ hi (by simp [h]))
    (fun i hi ↦ h₃ i fun h ↦ hi (by simp [h]))

/-- **The global side of the Grothendieck–Lefschetz formula under shifts.** The alternating sum
of the traces of `Fᵐ` on the compactly supported cohomology of `K[a]` is `(-1)ᵃ` times that of
`K`, since `H_cⁱ(K[a]) ≅ H_c^{a+i}(K)`. -/
theorem finsum_trace_compactlySupportedCohomology_shift (K : WeilComplex k₀ l X) (a : ℤ)
    (m : ℕ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((K⟦a⟧).compactlySupportedCohomology i).frobeniusEnd ^ m) =
      (a.negOnePow : ℤ) • ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) := by
  conv_rhs => rw [← finsum_comp_equiv (Equiv.addLeft a)]
  rw [smul_finsum]
  refine finsum_congr fun i ↦ ?_
  rw [← (compactlySupportedCohomologyShiftEquiv K a i (Equiv.addLeft a i)
    rfl).trace_frobeniusEnd_pow, smul_smul, ← Units.val_mul, Equiv.coe_addLeft,
    ← Int.negOnePow_add, ← add_assoc, ← two_mul, Int.negOnePow_add, Int.negOnePow_two_mul,
    one_mul]

/-- **The global side of the Grothendieck–Lefschetz formula is invariant under isomorphisms.** -/
theorem finsum_trace_compactlySupportedCohomology_congr {K L : WeilComplex k₀ l X} (e : K ≅ L)
    (m : ℕ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((L.compactlySupportedCohomology i).frobeniusEnd ^ m) :=
  finsum_congr fun i ↦ by
    rw [(compactlySupportedCohomologyEquivOfIso e i).trace_frobeniusEnd_pow]

end Global

section Local

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- For a distinguished triangle `K₁ → K₂ → K₃ → K₁[1]` of Weil complexes and a closed point `x`,
the alternating sum over `j` of the traces of a power of the local Frobenius on the stalks
`𝓗ʲ(Kᵢ)_x̄` is additive, by the stalks of the long exact sequence of cohomology sheaves. -/
theorem finsum_trace_stalk_homologySheaf_eq_add_of_distTriang
    (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _) (x : X.finitePoints) (p : ℕ) :
    ∑ᶠ j : ℤ, (j.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((((homologySheaf j).obj T.obj₂).stalk x).frobeniusEnd ^ p) =
      ∑ᶠ j : ℤ, (j.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((((homologySheaf j).obj T.obj₁).stalk x).frobeniusEnd ^ p) +
        ∑ᶠ j : ℤ, (j.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((((homologySheaf j).obj T.obj₃).stalk x).frobeniusEnd ^ p) := by
  obtain ⟨s₁, h₁⟩ := T.obj₁.exists_finset_isZero_homologySheaf
  obtain ⟨s₂, h₂⟩ := T.obj₂.exists_finset_isZero_homologySheaf
  obtain ⟨s₃, h₃⟩ := T.obj₃.exists_finset_isZero_homologySheaf
  have hs := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  exact LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact
    (fun j ↦ (((homologySheaf j).obj T.obj₁).stalk x).carrier)
    (fun j ↦ (((homologySheaf j).obj T.obj₂).stalk x).carrier)
    (fun j ↦ (((homologySheaf j).obj T.obj₃).stalk x).carrier)
    (fun j ↦ WeilSheaf.stalkAtMap _ _ hs ((homologySheaf j).map T.mor₁))
    (fun j ↦ WeilSheaf.stalkAtMap _ _ hs ((homologySheaf j).map T.mor₂))
    (fun j j' h ↦ WeilSheaf.stalkAtMap _ _ hs (homologySheafδ T j j' h))
    (fun j ↦ LinearMap.exact_iff.2 (WeilSheaf.range_stalkAtMap_eq_ker
      (homologySheaf_exact₂ T j hT) _ _ hs).symm)
    (fun j j' h ↦ LinearMap.exact_iff.2 (WeilSheaf.range_stalkAtMap_eq_ker
      (homologySheaf_exact₃ T j j' hT h) _ _ hs).symm)
    (fun j j' h ↦ LinearMap.exact_iff.2 (WeilSheaf.range_stalkAtMap_eq_ker
      (homologySheaf_exact₁ T j j' hT h) _ _ hs).symm)
    _ _ _
    (fun j ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (WeilSheaf.stalkAtMap_frobenius _ _ hs ((homologySheaf j).map T.mor₁)) p)
    (fun j ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (WeilSheaf.stalkAtMap_frobenius _ _ hs ((homologySheaf j).map T.mor₂)) p)
    (fun j j' h ↦ FrobeniusModule.frobeniusEnd_pow_comp _
      (WeilSheaf.stalkAtMap_frobenius _ _ hs (homologySheafδ T j j' h)) p)
    (s₁ ∪ s₂ ∪ s₃)
    (fun j hj ↦ WeilSheaf.subsingleton_stalk_of_isZero (h₁ j fun h ↦ hj (by simp [h])) x)
    (fun j hj ↦ WeilSheaf.subsingleton_stalk_of_isZero (h₂ j fun h ↦ hj (by simp [h])) x)
    (fun j hj ↦ WeilSheaf.subsingleton_stalk_of_isZero (h₃ j fun h ↦ hj (by simp [h])) x)

/-- **Additivity of the trace function in distinguished triangles.** For a distinguished triangle
`K₁ → K₂ → K₃ → K₁[1]` of Weil complexes, `t_{K₂} = t_{K₁} + t_{K₃}`. -/
theorem traceFunction_eq_add_of_distTriang (T : Triangle (WeilComplex k₀ l X))
    (hT : T ∈ distTriang _) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    T.obj₂.traceFunction n y = T.obj₁.traceFunction n y + T.obj₃.traceFunction n y := by
  simp only [traceFunction, WeilSheaf.traceFunction_eq_trace]
  exact finsum_trace_stalk_homologySheaf_eq_add_of_distTriang T hT _ _

end Local

end AlgebraicGeometry.WeilComplex

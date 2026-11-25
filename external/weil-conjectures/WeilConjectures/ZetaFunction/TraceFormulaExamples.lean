/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.CohomologicalFamily
public import WeilConjectures.ZetaFunction.Examples
public import WeilConjectures.ZetaFunction.SmoothProper

/-!
# Examples for the trace formula: genus-one curves and the projective line

*Genus-one curves.* Let `C₀` be a smooth, proper, geometrically connected curve over `k₀ = 𝔽_q`
with `dim H¹(C₀ ⊗ k̄, ℚ̄_ℓ) = 2`. Geometric Frobenius acts on `H⁰` by `1`; by Poincaré duality it
acts on the line `H²` by `q`, and on the plane `H¹` by an endomorphism `F` with `det F = q`, the
cup-product pairing on `H¹` being alternating with similitude factor `q`
(`LinearMap.BilinForm.det_eq_of_isAlt_of_finrank_eq_two`); both facts are derived from
`AlgebraicGeometry.WeilSheaf.poincareDuality`. The trace formula `N_m = 1 - Tr(Fᵐ | H¹) + qᵐ` and
Cayley–Hamilton for `F` show that `P₁ = det(1 - T F | H¹) = 1 - (1 + q - N₁) T + q T²` and that
`N₁` determines every `N_m`. For `q = 3`, `N₁ = 4` (the running example `y² = x³ - x` over `𝔽₃`)
this gives `P₁ = 1 + 3T²`, `N₂ = 16`, `N₃ = 28` and `Z(C₀, T) = (1 + 3T²) / ((1 - T)(1 - 3T))`.

*The projective line.* `Z(ℙ¹, T) = 1 / ((1 - T)(1 - qT))` satisfies
`Z(ℙ¹, 1/(qT)) = q T² Z(ℙ¹, T)`.

## Main statements

- `LinearMap.charpolyRev_eq_of_finrank_eq_two`, `LinearMap.trace_pow_add_two_of_finrank_eq_two`,
  `LinearMap.BilinForm.det_eq_of_isAlt_of_finrank_eq_two`: linear algebra in dimension two.
- `AlgebraicGeometry.Scheme.frobeniusCharpolyRev_one_of_finrank_eq_two`,
  `AlgebraicGeometry.Scheme.pointCount_eq_of_pointCount_one_eq`,
  `AlgebraicGeometry.Scheme.runningExample_trace_formula`: blueprint
  `example-running-example-trace-formula`.
- `AlgebraicGeometry.projectiveLine_functional_equation`: blueprint
  `example-functional-equation-projective-line`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The reverse characteristic polynomial of an endomorphism `F` of a plane is
`det(1 - T F) = 1 - Tr(F) T + det(F) T²`. -/
theorem charpolyRev_eq_of_finrank_eq_two (hV : Module.finrank K V = 2) (F : Module.End K V) :
    F.charpolyRev = 1 - C (trace K V F) * X + C (LinearMap.det F) * X ^ 2 := by
  let b := Module.finBasisOfFinrankEq K V hV
  rw [← charpolyRev_toMatrix b, Matrix.charpolyRev, Matrix.det_fin_two,
    trace_eq_matrix_trace K b, ← det_toMatrix b, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul]
  simp only [Fin.isValue, ↓reduceIte, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, Fin.one_eq_zero_iff,
    zero_sub, C_add, C_mul, C_sub]
  ring

/-- **Cayley–Hamilton in dimension two.** For an endomorphism `F` of a plane, the traces
`sₘ = Tr(Fᵐ)` satisfy `s_{m+2} = Tr(F) s_{m+1} - det(F) sₘ`. -/
theorem trace_pow_add_two_of_finrank_eq_two (hV : Module.finrank K V = 2) (F : Module.End K V)
    (m : ℕ) :
    trace K V (F ^ (m + 2)) =
      trace K V F * trace K V (F ^ (m + 1)) - LinearMap.det F * trace K V (F ^ m) := by
  let b := Module.finBasisOfFinrankEq K V hV
  have hcp : F.charpoly = X ^ 2 - C (trace K V F) * X + C (LinearMap.det F) := by
    rw [← charpoly_toMatrix F b, Matrix.charpoly_fin_two, trace_eq_matrix_trace K b,
      ← det_toMatrix b]
  have h := aeval_self_charpoly F
  rw [hcp] at h
  simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow,
    Algebra.algebraMap_eq_smul_one] at h
  have h2 : F ^ 2 = trace K V F • F - LinearMap.det F • 1 := by
    rw [smul_mul_assoc, one_mul] at h
    rw [← sub_eq_zero, sub_sub_eq_add_sub, ← h]
    abel
  have : F ^ (m + 2) = trace K V F • F ^ (m + 1) - LinearMap.det F • F ^ m := by
    rw [pow_add, h2, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, ← pow_succ]
  rw [this, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The determinant of a similitude of an alternating form on a plane: if `B` is a nonzero
alternating bilinear form on a plane `V` and `B (F x) (F y) = c B(x, y)` for all `x, y`, then
`det F = c`. -/
theorem BilinForm.det_eq_of_isAlt_of_finrank_eq_two (hV : Module.finrank K V = 2)
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hB0 : B ≠ 0) {F : Module.End K V} {c : K}
    (hF : ∀ x y, B (F x) (F y) = c * B x y) : LinearMap.det F = c := by
  let b := Module.finBasisOfFinrankEq K V hV
  set M := LinearMap.toMatrix b b F
  have hFb (j : Fin 2) : F (b j) = ∑ i, M i j • b i := by
    simp only [M, LinearMap.toMatrix_apply]
    exact (b.sum_repr (F (b j))).symm
  have hsym : B (b 1) (b 0) = -B (b 0) (b 1) := (hB.neg_eq (b 0) (b 1)).symm
  have hne : B (b 0) (b 1) ≠ 0 := by
    intro h0
    refine hB0 (LinearMap.BilinForm.ext_basis b fun i j ↦ ?_)
    fin_cases i <;> fin_cases j <;> simp [hB.self_eq_zero, h0, hsym]
  have key := hF (b 0) (b 1)
  rw [hFb 0, hFb 1] at key
  simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hB.self_eq_zero, hsym, mul_zero, zero_add, add_zero] at key
  rw [← det_toMatrix b, Matrix.det_fin_two]
  refine mul_right_cancel₀ hne ?_
  rw [← key]
  ring

end LinearMap

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace Scheme

section GenusOne

variable (k₀) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (C : Scheme.{u})
  [C.Over (Spec (CommRingCat.of k₀))] [IsProper (C ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]

omit [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] in
/-- On a geometrically connected curve, Frobenius on `H⁰(C ⊗ k̄, ℚ̄_ℓ)` is the identity of a
line. -/
theorem trace_frobeniusEnd_cohomology_zero_pow_of_curve (m : ℕ) :
    LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l C).cohomology ((0 : ℕ) : ℤ)).frobeniusEnd ^ m) = 1 := by
  have h : ((WeilSheaf.adicConstant k₀ l C).cohomology 0).frobeniusEnd = 1 := by
    rw [FrobeniusModule.frobeniusEnd, WeilSheaf.frobenius_cohomology_zero_adicConstant]
    rfl
  rw [Nat.cast_zero, h, one_pow, LinearMap.trace_one,
    WeilSheaf.finrank_cohomology_zero_adicConstant, Nat.cast_one]

/-- On a smooth proper geometrically connected curve, `H²(C ⊗ k̄, ℚ̄_ℓ)` is a line on which
Frobenius acts by `q` (Poincaré duality,
`AlgebraicGeometry.Scheme.exists_linearEquiv_cohomology_endpoints`). -/
theorem finrank_cohomology_two_and_frobeniusEnd_of_curve :
    Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l C).cohomology 2).carrier = 1 ∧
      ((WeilSheaf.adicConstant k₀ l C).cohomology 2).frobeniusEnd =
        (Nat.card k₀ : PadicAlgCl l) • 1 := by
  obtain ⟨-, e, he⟩ := exists_linearEquiv_cohomology_endpoints k₀ C 1 l
  have h2 : (2 : ℤ) = 2 * ((1 : ℕ) : ℤ) := by norm_num
  rw [h2]
  refine ⟨by rw [e.finrank_eq, Module.finrank_self], LinearMap.ext fun z ↦ e.injective ?_⟩
  rw [LinearMap.smul_apply, Module.End.one_apply, map_smul,
    ← pow_one (Nat.card k₀ : PadicAlgCl l), smul_eq_mul, ← he z]
  rfl

/-- On a smooth proper geometrically connected curve with `dim H¹(C ⊗ k̄, ℚ̄_ℓ) = 2`, Frobenius on
`H¹` has determinant `q`: by Poincaré duality (`AlgebraicGeometry.WeilSheaf.poincareDuality`) the
cup-product pairing on `H¹` is perfect, alternating and multiplied by `q` under Frobenius. -/
theorem det_frobeniusEnd_cohomology_one_of_finrank_eq_two
    (hg : Module.finrank (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l C).cohomology 1).carrier = 2) :
    LinearMap.det ((WeilSheaf.adicConstant k₀ l C).cohomology 1).frobeniusEnd = Nat.card k₀ := by
  obtain ⟨T, -, -, -, hpair, -, hsim, -⟩ := WeilSheaf.poincareDuality k₀ l C 1
  have h : (1 : ℤ) + 1 = 2 * ((1 : ℕ) : ℤ) := by norm_num
  obtain ⟨hperf, hcomm⟩ := hpair 1 1 h
  let B : LinearMap.BilinForm (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l C).cohomology 1).carrier := T.pairing 1 1 h
  have hB : B.IsAlt := fun x ↦ by
    have hx := hcomm x x
    rw [Int.negOnePow_one, Units.neg_smul, one_smul] at hx
    have : (2 : PadicAlgCl l) * T.pairing 1 1 h x x = 0 := by
      rw [two_mul]
      nth_rewrite 1 [hx]
      exact neg_add_cancel _
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have hB0 : B ≠ 0 := by
    intro h0
    have hinj := (LinearMap.IsPerfPair.bijective_left B).1
    have : Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k₀ l C).cohomology 1).carrier = 0 := by
      rw [Module.finrank_zero_iff]
      refine ⟨fun x y ↦ hinj ?_⟩
      simp [B, h0]
    omega
  have := LinearMap.BilinForm.det_eq_of_isAlt_of_finrank_eq_two hg hB hB0
    (F := ((WeilSheaf.adicConstant k₀ l C).cohomology 1).frobeniusEnd)
    (c := (Nat.card k₀ : PadicAlgCl l) ^ 1) fun x y ↦ hsim 1 1 h x y
  rwa [pow_one] at this

variable {k₀ l C}

/-- The trace formula on a smooth proper geometrically connected curve `C₀`,
`H²(C₀ ⊗ k̄, ℚ̄_ℓ)` being a line on which Frobenius acts by `q` (Poincaré duality):
`N_m = 1 - Tr(Fᵐ | H¹(C₀ ⊗ k̄, ℚ̄_ℓ)) + qᵐ` for every `m ≥ 1`. -/
theorem pointCount_eq_one_sub_trace_add_of_curve {m : ℕ} (hm : 1 ≤ m) :
    ((C ↘ Spec (CommRingCat.of k₀)).pointCount m : PadicAlgCl l) =
      1 - LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l C).cohomology 1).frobeniusEnd ^ m) +
        (Nat.card k₀ : PadicAlgCl l) ^ m := by
  obtain ⟨hH2, hF2⟩ := finrank_cohomology_two_and_frobeniusEnd_of_curve k₀ l C
  have h2 : LinearMap.trace (PadicAlgCl l) _
      (((WeilSheaf.adicConstant k₀ l C).cohomology ((2 : ℕ) : ℤ)).frobeniusEnd ^ m) =
        (Nat.card k₀ : PadicAlgCl l) ^ m := by
    rw [Nat.cast_ofNat, hF2, _root_.smul_pow, one_pow, map_smul, LinearMap.trace_one, hH2,
      smul_eq_mul, Nat.cast_one, mul_one]
  rw [WeilSheaf.pointCount_eq_sum_trace_cohomology k₀ l C 1 hm, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, trace_frobeniusEnd_cohomology_zero_pow_of_curve,
    h2]
  norm_num
  rw [← sub_eq_add_neg]
  rfl

/-- Blueprint `example-running-example-trace-formula` (genus-one curves): let `C₀` be a smooth
proper geometrically connected curve over `k₀ = 𝔽_q` with `dim H¹(C₀ ⊗ k̄, ℚ̄_ℓ) = 2`. By Poincaré
duality `H²` is a line on which Frobenius acts by `q`, and `det(F | H¹) = q`
(`AlgebraicGeometry.Scheme.det_frobeniusEnd_cohomology_one_of_finrank_eq_two`). Then

* `P₁ = det(1 - T F | H¹) = 1 - (1 + q - N₁) T + q T²`;
* `sₘ = 1 + qᵐ - Nₘ = Tr(Fᵐ | H¹)` satisfies `s₂ = s₁² - 2q` and
  `s_{m+2} = s₁ s_{m+1} - q sₘ` for `m ≥ 1`,

so that `N₁` determines every `Nₘ`
(`AlgebraicGeometry.Scheme.pointCount_eq_of_pointCount_one_eq`). -/
theorem frobeniusCharpolyRev_one_of_finrank_eq_two
    (hg : Module.finrank (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l C).cohomology 1).carrier = 2) :
    frobeniusCharpolyRev k₀ l C 1 =
      1 - Polynomial.C ((1 + Nat.card k₀ - (C ↘ Spec (CommRingCat.of k₀)).pointCount 1 : ℤ) :
        PadicAlgCl l) * X + Polynomial.C (Nat.card k₀ : PadicAlgCl l) * X ^ 2 ∧
    (1 + (Nat.card k₀ : ℤ) ^ 2 - (C ↘ Spec (CommRingCat.of k₀)).pointCount 2 =
      (1 + Nat.card k₀ - (C ↘ Spec (CommRingCat.of k₀)).pointCount 1) ^ 2 - 2 * Nat.card k₀) ∧
    ∀ m, 1 ≤ m →
      1 + (Nat.card k₀ : ℤ) ^ (m + 2) - (C ↘ Spec (CommRingCat.of k₀)).pointCount (m + 2) =
        (1 + Nat.card k₀ - (C ↘ Spec (CommRingCat.of k₀)).pointCount 1) *
          (1 + (Nat.card k₀ : ℤ) ^ (m + 1) -
            (C ↘ Spec (CommRingCat.of k₀)).pointCount (m + 1)) -
          Nat.card k₀ *
            (1 + (Nat.card k₀ : ℤ) ^ m - (C ↘ Spec (CommRingCat.of k₀)).pointCount m) := by
  have hdet := det_frobeniusEnd_cohomology_one_of_finrank_eq_two k₀ l C hg
  set F := ((WeilSheaf.adicConstant k₀ l C).cohomology 1).frobeniusEnd
  set N := fun m ↦ (C ↘ Spec (CommRingCat.of k₀)).pointCount m
  set q := Nat.card k₀
  -- `Tr(Fᵐ) = 1 + qᵐ - Nₘ`, as an identity of integers cast to `ℚ̄_ℓ`
  have htr (m : ℕ) (hm : 1 ≤ m) :
      LinearMap.trace (PadicAlgCl l) _ (F ^ m) = ((1 + (q : ℤ) ^ m - N m : ℤ) : PadicAlgCl l) := by
    have := pointCount_eq_one_sub_trace_add_of_curve (k₀ := k₀) (l := l) (C := C) hm
    push_cast
    simp only [N, q, F] at this ⊢
    rw [this]
    ring
  have hinj : Function.Injective (Int.cast : ℤ → PadicAlgCl l) := Int.cast_injective
  have h1 := htr 1 le_rfl
  rw [pow_one] at h1
  refine ⟨?_, ?_, fun m hm ↦ ?_⟩
  · rw [frobeniusCharpolyRev_def, FrobeniusModule.localPolynomial,
      LinearMap.charpolyRev_eq_of_finrank_eq_two hg, hdet]
    rw [h1, pow_one]
  · apply hinj
    have h2 := LinearMap.trace_pow_add_two_of_finrank_eq_two hg F 0
    rw [zero_add, pow_zero, LinearMap.trace_one, hg, hdet, htr 2 (by norm_num),
      pow_one, h1] at h2
    rw [h2]
    push_cast
    ring
  · apply hinj
    have h2 := LinearMap.trace_pow_add_two_of_finrank_eq_two hg F m
    rw [hdet, htr (m + 2) (by omega), htr (m + 1) (by omega), htr m hm, h1] at h2
    rw [h2]
    push_cast
    ring

/-- Blueprint `example-running-example-trace-formula` (the number `N₁` determines every `Nₘ`):
two smooth proper geometrically connected curves `C₀`, `C₀'` over `k₀` with `dim H¹ = 2`
(genus one) and with the same number
of `k₀`-points have the same number of `𝔽_{qᵐ}`-points for every `m ≥ 1`. -/
theorem pointCount_eq_of_pointCount_one_eq {C' : Scheme.{u}}
    [C'.Over (Spec (CommRingCat.of k₀))] [IsProper (C' ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C' ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C' ↘ Spec (CommRingCat.of k₀))]
    (hg : Module.finrank (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l C).cohomology 1).carrier = 2)
    (hg' : Module.finrank (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l C').cohomology 1).carrier = 2)
    (h1 : (C ↘ Spec (CommRingCat.of k₀)).pointCount 1 =
      (C' ↘ Spec (CommRingCat.of k₀)).pointCount 1) (m : ℕ) (hm : 1 ≤ m) :
    (C ↘ Spec (CommRingCat.of k₀)).pointCount m = (C' ↘ Spec (CommRingCat.of k₀)).pointCount m := by
  obtain ⟨-, h2, hrec⟩ := frobeniusCharpolyRev_one_of_finrank_eq_two hg
  obtain ⟨-, h2', hrec'⟩ := frobeniusCharpolyRev_one_of_finrank_eq_two hg'
  set N := fun m ↦ (C ↘ Spec (CommRingCat.of k₀)).pointCount m
  set N' := fun m ↦ (C' ↘ Spec (CommRingCat.of k₀)).pointCount m
  suffices h : ∀ m, (N (m + 1) : ℤ) = N' (m + 1) ∧ (N (m + 2) : ℤ) = N' (m + 2) by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hm
    exact_mod_cast (h n).1
  intro m
  induction m with
  | zero =>
    refine ⟨by exact_mod_cast h1, ?_⟩
    have e1 : ((C ↘ Spec (CommRingCat.of k₀)).pointCount 1 : ℤ) =
        (C' ↘ Spec (CommRingCat.of k₀)).pointCount 1 := by exact_mod_cast h1
    simp only [N, N']
    rw [e1] at h2
    linarith
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e1 : ((C ↘ Spec (CommRingCat.of k₀)).pointCount 1 : ℤ) =
        (C' ↘ Spec (CommRingCat.of k₀)).pointCount 1 := by exact_mod_cast h1
    have r := hrec (n + 1) (by omega)
    have r' := hrec' (n + 1) (by omega)
    simp only [N, N'] at ih ⊢
    rw [e1, ih.1, ih.2] at r
    linarith

/-- Blueprint `example-running-example-trace-formula` (the running example): for a smooth proper
geometrically connected curve `C₀` over a field `k₀` with `3` elements, with
`dim H¹(C₀ ⊗ k̄, ℚ̄_ℓ) = 2` and `N₁ = 4` (as for `y² = x³ - x` over `𝔽₃`):

* `Tr(F | H¹) = 0` and `det(1 - T F | H¹) = 1 + 3T²`;
* `N₂ = 16` and `N₃ = 28`;
* `Z(C₀, T) (1 - T)(1 - 3T) = 1 + 3T²`, i.e. `Z(C₀, T) = (1 + 3T²) / ((1 - T)(1 - 3T))`.

The curve `y² = x³ - x` itself, and the count `N₁ = 4` of its `𝔽₃`-points, are not constructed
in the library; the genus and `N₁ = 4` are hypotheses here. -/
theorem runningExample_trace_formula (hq : Nat.card k₀ = 3)
    (hg : Module.finrank (PadicAlgCl l)
      ((WeilSheaf.adicConstant k₀ l C).cohomology 1).carrier = 2)
    (h1 : (C ↘ Spec (CommRingCat.of k₀)).pointCount 1 = 4) :
    LinearMap.trace (PadicAlgCl l) _ ((WeilSheaf.adicConstant k₀ l C).cohomology 1).frobeniusEnd =
      0 ∧
    frobeniusCharpolyRev k₀ l C 1 = 1 + Polynomial.C 3 * X ^ 2 ∧
    (C ↘ Spec (CommRingCat.of k₀)).pointCount 2 = 16 ∧
    (C ↘ Spec (CommRingCat.of k₀)).pointCount 3 = 28 ∧
    (C ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        ((1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X)) =
      1 + PowerSeries.C 3 * PowerSeries.X ^ 2 := by
  obtain ⟨hH2, hF2⟩ := finrank_cohomology_two_and_frobeniusEnd_of_curve k₀ l C
  obtain ⟨hP, h2, hrec⟩ := frobeniusCharpolyRev_one_of_finrank_eq_two hg
  have htr1 := pointCount_eq_one_sub_trace_add_of_curve (k₀ := k₀) (l := l) (C := C) (m := 1) le_rfl
  have h2' : frobeniusCharpolyRev k₀ l C 2 = 1 - Polynomial.C 3 * X := by
    rw [frobeniusCharpolyRev_def, FrobeniusModule.localPolynomial, hF2,
      LinearMap.charpolyRev_smul_one, hH2, pow_one, hq, Nat.cast_ofNat]
  rw [hq, h1] at h2
  rw [hq, h1] at hP
  rw [hq] at htr1
  rw [h1] at htr1
  have hN2 : (C ↘ Spec (CommRingCat.of k₀)).pointCount 2 = 16 := by
    have : ((C ↘ Spec (CommRingCat.of k₀)).pointCount 2 : ℤ) = 16 := by
      push_cast at h2
      linarith
    exact_mod_cast this
  have hN3 : (C ↘ Spec (CommRingCat.of k₀)).pointCount 3 = 28 := by
    have r := hrec 1 le_rfl
    rw [hq, h1, hN2] at r
    have : ((C ↘ Spec (CommRingCat.of k₀)).pointCount 3 : ℤ) = 28 := by
      push_cast at r
      linarith
    exact_mod_cast this
  have hP' : frobeniusCharpolyRev k₀ l C 1 = 1 + Polynomial.C 3 * X ^ 2 := by
    rw [hP]
    norm_num
  refine ⟨?_, hP', hN2, hN3, ?_⟩
  · rw [pow_one] at htr1
    push_cast at htr1
    linear_combination htr1
  · -- the trace-to-determinant identity in `ℚ̄_ℓ⟦T⟧`, descended to `ℚ⟦T⟧`
    have hZ := map_zetaSeries_mul_evenFrobeniusProduct k₀ l C 1
    have he : (Finset.range (2 * 1 + 1)).filter Even = {0, 2} := by decide
    have ho : (Finset.range (2 * 1 + 1)).filter Odd = {1} := by decide
    have h0 := frobeniusCharpolyRev_zero k₀ l C
    rw [evenFrobeniusProduct, oddFrobeniusProduct, he, ho, Finset.prod_pair (by decide),
      Finset.prod_singleton] at hZ
    simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at hZ
    rw [h2', h0, hP'] at hZ
    apply PowerSeries.map_injective (algebraMap ℚ (PadicAlgCl l))
      (algebraMap ℚ (PadicAlgCl l)).injective
    rw [map_mul]
    convert hZ using 2
    · simp only [map_mul, map_sub, map_one, PowerSeries.map_X, PowerSeries.map_C, eq_ratCast,
        Rat.cast_ofNat, coe_mul, coe_sub, coe_one, coe_X, coe_C]
    · simp only [map_add, map_one, map_mul, PowerSeries.map_C, eq_ratCast, Rat.cast_ofNat, map_pow,
        PowerSeries.map_X, coe_add, coe_one, coe_mul, coe_C, coe_pow, coe_X]

end GenusOne

end Scheme

section ProjectiveLine

/-- The rational function `Z(ℙ¹, t) = 1 / ((1 - t)(1 - qt))` satisfies
`Z(ℙ¹, 1/(qt)) = q t² Z(ℙ¹, t)` at every `t ≠ 0` of a field in which `q ≠ 0` (both sides being
`0` at the poles `t = 1`, `t = 1/q`). -/
theorem projectiveLine_functional_equation_eval {K : Type*} [Field K] {q : K} (hq : q ≠ 0)
    {t : K} (ht : t ≠ 0) :
    ((1 - (q * t)⁻¹) * (1 - q * (q * t)⁻¹))⁻¹ = q * t ^ 2 * ((1 - t) * (1 - q * t))⁻¹ := by
  have h : (1 - (q * t)⁻¹) * (1 - q * (q * t)⁻¹) = ((1 - t) * (1 - q * t)) * (q * t ^ 2)⁻¹ := by
    field_simp
    ring
  rw [h, mul_inv, inv_inv, mul_comm]

/-- Blueprint `example-functional-equation-projective-line`: for `X₀ = ℙ¹` over `k = 𝔽_q`,
`Z(ℙ¹, T) (1 - T)(1 - qT) = 1`, so `Z(ℙ¹, T)` is the rational function `1 / ((1 - T)(1 - qT))`,
and this rational function satisfies `Z(ℙ¹, 1/(qT)) = q T² Z(ℙ¹, T)` at every `t ≠ 0` of every
field of characteristic zero. -/
theorem projectiveLine_functional_equation (k : Type u) [Field k] [Finite k] :
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).zetaSeries *
        ((1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℚ) * PowerSeries.X)) = 1 ∧
    ∀ (K : Type) [Field K] [CharZero K] (t : K), t ≠ 0 →
      ((1 - ((Nat.card k : K) * t)⁻¹) * (1 - (Nat.card k : K) * ((Nat.card k : K) * t)⁻¹))⁻¹ =
        (Nat.card k : K) * t ^ 2 * ((1 - t) * (1 - (Nat.card k : K) * t))⁻¹ :=
  ⟨zetaSeries_projectiveLine k, fun _ _ _ _ ht ↦
    projectiveLine_functional_equation_eval (Nat.cast_ne_zero.2 Nat.card_pos.ne') ht⟩

end ProjectiveLine

end AlgebraicGeometry

end

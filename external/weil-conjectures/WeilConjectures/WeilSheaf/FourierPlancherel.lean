/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierTrace
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.TraceFunctionCongr

/-!
# Trace energies of Weil complexes and the Plancherel identity

For a Weil complex `K` on a scheme `X₀` over `k₀ = 𝔽_q` and an embedding `ι : ℚ̄_ℓ ↪ ℂ`, the
*trace energy* at level `n` is the squared `L²`-norm of the trace function of `K` on the
`𝔽_{qⁿ}`-points,

`‖f_K‖²_n = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_K(x)|²`.

The trace function, hence the trace energy, only depends on `K` up to isomorphism, and the shift
`[1]` of a sheaf placed in degree `0` changes the sign of the trace function without changing
the trace energy. The Plancherel identity says that the Fourier transform multiplies the trace
energy at level `n` by `qⁿ`; more generally, the Fourier transform on the affine space `𝔸^ι`
with `r = #ι` (`AlgebraicGeometry.affineSpaceFourierTransform`) multiplies it by `q^{nr}`:

`∑_{y ∈ 𝔽_{qⁿ}^ι} |ι t_{FT_ψ(K)}(y)|² = q^{nr} ∑_{x ∈ 𝔽_{qⁿ}^ι} |ι t_K(x)|²`.

It follows from the Fourier trace formula on `𝔸^ι`
(`AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform`), the sign `(-1)^r`
having absolute value one, and the classical Plancherel identity on `𝔽_{qⁿ}^ι`
(`FiniteField.sum_norm_sq_fourierTransformPi`). The affine line is the case `ι = PUnit`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.traceFunction_shift_toComplex`: `t_{F[1]} = -t_F`.
- `AlgebraicGeometry.WeilComplex.traceEnergy`: the trace energy of a Weil complex.
- `AlgebraicGeometry.WeilComplex.traceEnergy_affineSpaceFourierTransform`: the Plancherel
  identity on `𝔸^ι`, and `AlgebraicGeometry.WeilComplex.traceEnergy_fourierTransform`, its case
  `ι = PUnit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace function of a Weil sheaf placed in degree `0` and shifted by one is the negative
of the trace function of the sheaf: the only cohomology sheaf is `𝓗⁻¹(F[1]) ≅ F`, in odd
degree. -/
theorem WeilSheaf.traceFunction_shift_toComplex (F : WeilSheaf k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((toComplex.obj F)⟦(1 : ℤ)⟧).traceFunction n x = -F.traceFunction n x := by
  rw [WeilComplex.traceFunction_eq_sum _ {-1}
      (fun j hj ↦ isZero_homologySheaf_shift_toComplex F (Finset.notMem_singleton.1 hj)),
    Finset.sum_singleton, traceFunction_congr (homologySheafShiftToComplexIso F 1)]
  simp

/-- The trace energy `‖f_K‖²_n = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_K(x)|²` of a Weil complex at level
`n`, the squared `L²`-norm of its trace function on the `𝔽_{qⁿ}`-points, with junk value `0` if
`X₀` has infinitely many `𝔽_{qⁿ}`-points. (blueprint: `definition-growth-squared-traces`) -/
noncomputable def WeilComplex.traceEnergy (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X)
    (n : ℕ) : ℝ :=
  ∑ᶠ x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n),
    ‖ι (K.traceFunction n x)‖ ^ 2

/-- The trace energy is nonnegative, as a sum of squares. -/
theorem WeilComplex.traceEnergy_nonneg (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X)
    (n : ℕ) : 0 ≤ K.traceEnergy ι n :=
  finsum_nonneg fun _ ↦ sq_nonneg _

/-- Isomorphic Weil complexes have the same trace energy. -/
theorem WeilComplex.traceEnergy_congr (ι : PadicAlgCl l →+* ℂ) {K L : WeilComplex k₀ l X}
    (e : K ≅ L) (n : ℕ) : K.traceEnergy ι n = L.traceEnergy ι n := by
  simp only [traceEnergy, traceFunction_congr e]

end

section AffineSpace

variable {ι : Type u} [Fintype ι]

/-- **Plancherel identity on `𝔸^ι`.** For a nontrivial additive character `ψ`, every Weil
complex `K` on the affine space `𝔸^ι` with `r = #ι` and every `n ≥ 1`, the Fourier transform
multiplies the trace energy at level `n` by `q^{nr}`:

`∑_{y ∈ 𝔽_{qⁿ}^ι} |j t_{FT_ψ(K)}(y)|² = q^{nr} ∑_{x ∈ 𝔽_{qⁿ}^ι} |j t_K(x)|²`.

The nontriviality of `ψ` is needed for the orthogonality of the characters `y ↦ ψ(Tr⟨x, y⟩)`.
(blueprint: `corollary-plancherel--1`, subsection `corollary-plancherel`) -/
theorem WeilComplex.traceEnergy_affineSpaceFourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) (j : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)))
    {n : ℕ} (hn : 1 ≤ n) :
    ((affineSpaceFourierTransform ι ψ).obj K).traceEnergy j n =
      (Nat.card k₀ : ℝ) ^ (n * Fintype.card ι) * K.traceEnergy j n := by
  classical
  have hn' : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  let := Fintype.ofFinite (FiniteField.galoisExtension k₀ n)
  have h (L : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) :
      L.traceEnergy j n = ∑ x, ‖j (L.affineSpaceTraceFunction n x)‖ ^ 2 := by
    rw [traceEnergy, ← finsum_comp_equiv (AffineSpace.fieldPointsEquivPi ι k₀ _).symm,
      finsum_eq_sum_of_fintype]
    rfl
  rw [h, h]
  simp_rw [traceFunction_affineSpaceFourierTransform ψ K hn', map_mul, norm_mul, map_pow,
    map_neg, map_one, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [FiniteField.sum_norm_sq_fourierTransformPi j hψ,
    ← Nat.card_eq_fintype_card (α := FiniteField.galoisExtension k₀ n),
    FiniteField.nat_card_galoisExtension k₀ n hn', pow_mul]
  push_cast
  rfl

end AffineSpace

/-- **Plancherel identity.** For a nontrivial additive character `ψ`, every Weil complex `K` on
the affine line and every `n ≥ 1`, the Fourier transform multiplies the trace energy at level `n`
by `qⁿ`:

`∑_{y ∈ 𝔽_{qⁿ}} |ι t_{FT_ψ(K)}(y)|² = qⁿ ∑_{x ∈ 𝔽_{qⁿ}} |ι t_K(x)|²`.

The nontriviality of `ψ`, implicit in the blueprint, is needed for the orthogonality of the
characters `y ↦ ψ(Tr(xy))`. It is the case `ι = PUnit` of
`AlgebraicGeometry.WeilComplex.traceEnergy_affineSpaceFourierTransform`.
(blueprint: `corollary-plancherel--1`, subsection `corollary-plancherel`) -/
theorem WeilComplex.traceEnergy_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : 1 ≤ n) :
    ((fourierTransform ψ).obj K).traceEnergy ι n = (Nat.card k₀ : ℝ) ^ n * K.traceEnergy ι n := by
  have h := traceEnergy_affineSpaceFourierTransform (ι := PUnit.{u + 1}) ψ hψ ι K hn
  rw [Fintype.card_punit, mul_one] at h
  exact h

end AlgebraicGeometry

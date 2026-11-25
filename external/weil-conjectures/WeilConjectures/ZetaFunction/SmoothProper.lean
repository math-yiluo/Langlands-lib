/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.ZetaFunction.CohomologicalFamily
public import WeilConjectures.ZetaFunction.Weights
public import WeilConjectures.ZetaFunction.WeilFactorization
public import WeilConjectures.ZetaLinearAlgebra.FunctionalEquation
public import WeilConjectures.ZetaLinearAlgebra.UniversalPurity

/-!
# The Weil conjectures for a smooth proper variety

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over the
finite field `k₀ = 𝔽_q`. This file assembles the three cohomological inputs — the trace formula
(`AlgebraicGeometry.Scheme.exists_traceDatum`), Poincaré duality
(`AlgebraicGeometry.WeilSheaf.poincareDuality`) and the weight estimate
(`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_cohomology_adicConstant`) — with the zeta
linear algebra of `WeilConjectures.ZetaLinearAlgebra` into the Weil conjectures for `X₀`: there
are integer polynomials `P₀, …, P_{2d}` giving a Weil factorization of `Z(X₀, T)` and satisfying
the functional equation and the Riemann hypothesis, and `Pᵢ` realizes the determinant factor
`P_{i,ℓ}` for every prime `ℓ ≠ p`.

## Main statements

- `AlgebraicGeometry.Scheme.frobeniusCharpolyRev_zero`,
  `AlgebraicGeometry.Scheme.frobeniusCharpolyRev_two_mul`: the endpoint factors
  `P_{0,ℓ} = 1 - T` and `P_{2d,ℓ} = 1 - qᵈ T` (`theorem-weil-conjectures-smooth-proper-schemes`).
- `AlgebraicGeometry.Scheme.isPureOfWeight_map_frobeniusCharpolyRev`: root purity
  (`theorem-weil-conjectures-smooth-proper-schemes`,
  `corollary-purity-cohomology-smooth-proper-variety--1`).
- `AlgebraicGeometry.Scheme.isUniversallyPureOfWeight_map_frobeniusCharpolyRev`: the reciprocal
  roots of `P_{i,ℓ}` are `q`-Weil numbers of weight `i`, under every embedding of their number
  fields.
- `AlgebraicGeometry.Scheme.exists_isWeilFactorization_of_smoothProper`: the Weil conjectures
  for `X₀`, with the realization of the factors for every `ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace Scheme

section Endpoints

variable (k₀) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k₀))]

/-- The degree-zero endpoint of `theorem-weil-conjectures-smooth-proper-schemes`: for `X₀`
geometrically connected, `H⁰(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ` with trivial Frobenius
(`AlgebraicGeometry.WeilSheaf.finrank_cohomology_zero_adicConstant`,
`AlgebraicGeometry.WeilSheaf.frobenius_cohomology_zero_adicConstant`), so `P_{0,ℓ} = 1 - T`. -/
theorem frobeniusCharpolyRev_zero [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    frobeniusCharpolyRev k₀ l X 0 = 1 - Polynomial.X := by
  have h : ((WeilSheaf.adicConstant k₀ l X).cohomology 0).frobeniusEnd = 1 := by
    rw [FrobeniusModule.frobeniusEnd, WeilSheaf.frobenius_cohomology_zero_adicConstant]
    rfl
  rw [frobeniusCharpolyRev_def, FrobeniusModule.localPolynomial, h, LinearMap.charpolyRev_one,
    WeilSheaf.finrank_cohomology_zero_adicConstant, pow_one]

/-- The top-degree endpoint of `theorem-weil-conjectures-smooth-proper-schemes`: for `X₀` smooth,
proper and geometrically connected of pure dimension `d`, the trace
`H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-d)` of Poincaré duality is a Frobenius-equivariant isomorphism onto a
line on which Frobenius acts by `qᵈ`, so `P_{2d,ℓ} = 1 - qᵈ T`. -/
theorem frobeniusCharpolyRev_two_mul (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    frobeniusCharpolyRev k₀ l X (2 * d) =
      1 - C ((Nat.card k₀ : PadicAlgCl l) ^ d) * Polynomial.X := by
  obtain ⟨T, htr, -, -, -, hF, -⟩ := WeilSheaf.poincareDuality k₀ l X d
  set M := (WeilSheaf.adicConstant k₀ l X).cohomology (2 * d)
  have hfin : Module.finrank (PadicAlgCl l) M.carrier = 1 :=
    (LinearEquiv.ofBijective T.trace htr).finrank_eq.trans (Module.finrank_self _)
  have hfrob : M.frobeniusEnd = (Nat.card k₀ : PadicAlgCl l) ^ d • 1 := by
    refine LinearMap.ext fun z ↦ htr.1 ?_
    rw [LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_eq_mul]
    exact hF z
  rw [frobeniusCharpolyRev_def, FrobeniusModule.localPolynomial, hfrob,
    LinearMap.charpolyRev_smul_one, hfin, pow_one]

/-- Blueprint `theorem-weil-conjectures-smooth-proper-schemes` and
`corollary-purity-cohomology-smooth-proper-variety--1` (reciprocal roots have the weight-`i`
absolute value): for `X₀` smooth, proper and geometrically connected of pure dimension `d` and every
field embedding `ι : ℚ̄_ℓ → ℂ`, every reciprocal root `α` of `P_{i,ℓ}` satisfies `|ι α| = q^{i/2}`;
equivalently, `ι P_{i,ℓ}` is pure of weight `i`. The reciprocal roots are the Frobenius eigenvalues
(`prose-19-08`), which have this absolute value by
`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_cohomology_adicConstant`. -/
theorem isPureOfWeight_map_frobeniusCharpolyRev (d : ℕ)
    [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ) (i : ℕ) :
    ((frobeniusCharpolyRev k₀ l X i).map ι).IsPureOfWeight (Nat.card k₀) i := by
  set M := (WeilSheaf.adicConstant k₀ l X).cohomology i
  have hpure := WeilSheaf.isPureOfWeightOver_cohomology_adicConstant k₀ l X d ι i
  refine ⟨by rw [Polynomial.coeff_map, coeff_zero_frobeniusCharpolyRev, map_one], fun z hz ↦ ?_⟩
  rw [frobeniusCharpolyRev_def, FrobeniusModule.localPolynomial,
    LinearMap.roots_map_charpolyRev_eq_map_inv ι M.frobeniusEnd
      (LinearEquiv.isUnit_det' M.frobenius),
    (IsAlgClosed.splits M.frobeniusEnd.charpoly).roots_map ι, Multiset.map_map,
    Multiset.mem_map] at hz
  obtain ⟨α, hα, rfl⟩ := hz
  have hα' : M.frobeniusEnd.HasEigenvalue α :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2
      (Polynomial.isRoot_of_mem_roots hα)
  have hnorm := hpure α hα'
  have hq : (0 : ℝ) < Nat.card k₀ := by exact_mod_cast Nat.card_pos
  rw [Function.comp_apply, norm_inv, hnorm, ← Real.rpow_neg hq.le, Int.cast_natCast, neg_div]

/-- Universal purity of the determinant factors: for `X₀` smooth, proper and geometrically
connected of pure dimension `d`, a field embedding `ι : ℚ̄_ℓ → ℂ` and `0 ≤ i ≤ 2d`, every root `z`
of `ι P_{i,ℓ}` is algebraic over `ℚ` and every conjugate of `z` over `ℚ` has absolute value
`q^{-i/2}`; equivalently every reciprocal root `α` of `ι P_{i,ℓ}` satisfies `|τ(α)| = q^{i/2}` for
every embedding `τ : ℚ(α) → ℂ`. Every embedding of the number field `ℚ(α) ⊆ ℚ̄_ℓ` into `ℂ` extends
to `ℚ̄_ℓ` (`PadicAlgCl.exists_ringHom_complex_apply_eq`), and purity holds for every extension
(`AlgebraicGeometry.Scheme.isPureOfWeight_map_frobeniusCharpolyRev`); the roots are algebraic
because `Z(X₀, T)` has integer coefficients. -/
theorem isUniversallyPureOfWeight_map_frobeniusCharpolyRev (d : ℕ)
    [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ) {i : ℕ}
    (hi : i ≤ 2 * d) :
    ((frobeniusCharpolyRev k₀ l X i).map ι).IsUniversallyPureOfWeight (Nat.card k₀) i := by
  obtain ⟨D, -, hDP, hN⟩ := exists_traceDatum k₀ l X d
  have hZ : PowerSeries.map (algebraMap ℚ (PadicAlgCl l))
      (X ↘ Spec (CommRingCat.of k₀)).zetaSeries = D.zeta :=
    D.map_zetaSeries _ hN
  have hq : 1 < Nat.card k₀ := Finite.one_lt_card
  have h := D.isUniversallyPureOfWeight_map_P hq
    (fun _ _ hβ hz ↦ PadicAlgCl.exists_ringHom_complex_apply_eq l hβ hz)
    (fun ι' j ↦ by rw [hDP]; exact isPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι' j) hZ
    (X ↘ Spec (CommRingCat.of k₀)).exists_int_zetaSeries ι ⟨i, by omega⟩
  rw [hDP] at h
  exact h

/-- The Weil conjectures for `X₀` at the prime `ℓ`: the factorization, the functional equation
and the Riemann hypothesis for integer polynomials `Pᵢ` with `Pᵢ^{(ℓ)} = P_{i,ℓ}`. -/
theorem exists_isWeilFactorization_of_prime (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      IsWeilFactorization (Nat.card k₀) d (X ↘ Spec (CommRingCat.of k₀)).zetaSeries P ∧
      WeilFunctionalEquation (Nat.card k₀) d P ∧
      WeilRiemannHypothesis (Nat.card k₀) d P ∧
      ∀ i : Fin (2 * d + 1),
        (P i).map (Int.castRingHom (PadicAlgCl l)) = frobeniusCharpolyRev k₀ l X (i : ℕ) := by
  have hq : 1 < Nat.card k₀ := Finite.one_lt_card
  -- the smooth-proper cohomological family as a trace datum
  let H := (WeilSheaf.adicConstant k₀ l X).cohomology
  let D : TraceDatum.{0, u + 1} (PadicAlgCl l) (2 * d) :=
    { V := fun i ↦ (H (i : ℕ)).carrier
      F := fun i ↦ (H (i : ℕ)).frobeniusEnd
      N := fun n ↦ ((X ↘ Spec (CommRingCat.of k₀)).pointCount n : ℤ)
      trace_eq := fun n hn ↦ by
        rw [Int.cast_natCast, WeilSheaf.pointCount_eq_sum_trace_cohomology k₀ l X d hn,
          Finset.sum_range] }
  have hDP (i : Fin (2 * d + 1)) : D.P i = frobeniusCharpolyRev k₀ l X (i : ℕ) := rfl
  -- Poincaré duality: the self-duality of the trace datum
  obtain ⟨T, -, -, -, hpair, -, hsim, -, -⟩ := WeilSheaf.poincareDuality k₀ l X d
  have hrev (i : Fin (2 * d + 1)) : ((i : ℕ) : ℤ) + ((i.rev : ℕ) : ℤ) = 2 * (d : ℤ) := by
    have := i.isLt
    rw [Fin.val_rev]
    omega
  let p : ∀ i : Fin (2 * d + 1), D.V i →ₗ[PadicAlgCl l] D.V i.rev →ₗ[PadicAlgCl l] PadicAlgCl l :=
    fun i ↦ T.pairing (i : ℕ) (i.rev : ℕ) (hrev i)
  have hp (i : Fin (2 * d + 1)) : (p i).IsPerfPair := (hpair _ _ (hrev i)).1
  have hFG (i : Fin (2 * d + 1)) (v : D.V i) (w : D.V i.rev) :
      p i (D.F i v) (D.F i.rev w) = (Nat.card k₀ : PadicAlgCl l) ^ d * p i v w :=
    hsim _ _ (hrev i) v w
  -- integrality and the comparison of the counting series
  have hZ : PowerSeries.map (algebraMap ℚ (PadicAlgCl l))
      (X ↘ Spec (CommRingCat.of k₀)).zetaSeries = D.zeta :=
    D.map_zetaSeries _ fun _ ↦ rfl
  have hint := (X ↘ Spec (CommRingCat.of k₀)).exists_int_zetaSeries
  -- purity for every embedding, hence universal purity
  obtain ⟨ι⟩ := PadicAlgCl.nonempty_ringHom_complex l
  have hpure (ι' : PadicAlgCl l →+* ℂ) (i : Fin (2 * d + 1)) :
      ((D.P i).map ι').IsPureOfWeight (Nat.card k₀) i.1 :=
    isPureOfWeight_map_frobeniusCharpolyRev k₀ l X d ι' i
  have hupure := D.isUniversallyPureOfWeight_map_P hq
    (fun _ _ hβ hz ↦ PadicAlgCl.exists_ringHom_complex_apply_eq l hβ hz) hpure hZ hint ι
  -- the endpoint factors
  have hzero : (D.P 0).map ι = 1 - Polynomial.X := by
    rw [hDP, Fin.val_zero, Nat.cast_zero, frobeniusCharpolyRev_zero, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_X]
  have hlast : (D.P (Fin.last (2 * d))).map ι =
      1 - Polynomial.C ((Nat.card k₀ : ℂ) ^ d) * Polynomial.X := by
    rw [hDP, Fin.val_last, Nat.cast_mul, Nat.cast_two, frobeniusCharpolyRev_two_mul,
      Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, map_pow, map_natCast]
  obtain ⟨P, hfact, hfe, hrh, hPι⟩ :=
    D.exists_isWeilFactorization_and_functionalEquation_and_riemannHypothesis hq ι hupure hzero
      hlast hp hFG hZ hint
  refine ⟨P, hfact, hfe, hrh, fun i ↦ Polynomial.map_injective ι ι.injective ?_⟩
  rw [Polynomial.map_map, ← hDP, ← hPι i]
  congr 1
  exact RingHom.ext_int _ _

end Endpoints

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- **The Weil conjectures for a smooth proper variety.** For `X₀` smooth, proper and
geometrically connected of pure dimension `d` over `k₀ = 𝔽_q` there are integer polynomials
`P₀, …, P_{2d}` which give a Weil factorization `Z(X₀, T) = ∏ᵢ Pᵢ(T)^{(-1)^{i+1}}` and satisfy the
functional equation and the Riemann hypothesis, and which are integral realization-independent
factors: `Pᵢ^{(ℓ)} = P_{i,ℓ} = det(1 - T F | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))` for every prime `ℓ ≠ p`.

For one prime `ℓ₀ ≠ p` the factors come from
`AlgebraicGeometry.Scheme.exists_isWeilFactorization_of_prime`; for any other `ℓ` the same
theorem gives factors realizing the `P_{i,ℓ}`, and they agree with the first ones by the
uniqueness of Weil factorizations satisfying the Riemann hypothesis
(`AlgebraicGeometry.IsWeilFactorization.unique`). -/
theorem exists_isWeilFactorization_of_smoothProper :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      IsWeilFactorization (Nat.card k₀) d (X ↘ Spec (CommRingCat.of k₀)).zetaSeries P ∧
      WeilFunctionalEquation (Nat.card k₀) d P ∧
      WeilRiemannHypothesis (Nat.card k₀) d P ∧
      ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i) := by
  have hq : 1 < Nat.card k₀ := Finite.one_lt_card
  obtain ⟨l₀, hl₀, hne⟩ : ∃ l : ℕ, l.Prime ∧ ringChar k₀ ≠ l := by
    by_cases h : ringChar k₀ = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, h⟩
  have : Fact l₀.Prime := ⟨hl₀⟩
  have : Fact (ringChar k₀ ≠ l₀) := ⟨hne⟩
  obtain ⟨P, hfact, hfe, hrh, -⟩ := exists_isWeilFactorization_of_prime k₀ l₀ X d
  refine ⟨P, hfact, hfe, hrh, fun i l _ _ ↦ ?_⟩
  obtain ⟨P', hfact', -, hrh', hP'⟩ := exists_isWeilFactorization_of_prime k₀ l X d
  rw [← IsWeilFactorization.unique hq hfact' hfact hrh' hrh]
  exact hP' i

end Scheme

end AlgebraicGeometry

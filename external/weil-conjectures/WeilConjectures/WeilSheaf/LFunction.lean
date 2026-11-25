/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.LocalFrobenius
public import WeilConjectures.ZetaFunction.TraceFormula
public import WeilConjectures.ZetaLinearAlgebra.AlternatingEulerProduct
public import WeilConjectures.ZetaLinearAlgebra.DetTrace

/-!
# The Euler-product form of the trace formula for Weil complexes

Let `X₀` be a separated scheme of finite type over the finite field `k₀`, `X = X₀ ⊗ k̄` and `K`
a Weil complex on `X₀`. For a closed point `x` of degree `e_x` the local factor of the
`L`-function of `K` at `x` is the inverse of the alternating determinant

`det (1 - T ^ {e_x} F_x ∣ K_x̄) = ∏_j det (1 - T ^ {e_x} F_x ∣ 𝓗ʲ(K)_x̄) ^ ((-1) ^ j)`

(`LinearMap.alternatingCharpolyRevProd`), and the Euler-product form of the
Grothendieck–Lefschetz trace formula says

`L (X₀, K, T) = ∏_x det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹`
`  = ∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`

in `1 + T ℚ̄_ℓ⟦T⟧`, the product over the closed points being locally finite for the `T`-adic
topology (`AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk`).
For a Weil sheaf placed in degree zero, the stalk cohomology is the stalk itself
(`AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk`).

## Main statements

- `AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk`
  (`theorem-trace-formula-euler-product`): the Euler-product form of the trace formula.
- `AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk`: its form for a Weil
  sheaf.

## Implementation notes

*Local finiteness.* The `L`-function is an infinite product over the closed points. Instead of
choosing a topology on `ℚ̄_ℓ⟦T⟧` in which it converges, the statement is coefficientwise: the
coefficient of `T ^ n` of the finite product over any finite set of closed points containing
all points of degree at most `n` is the coefficient of `T ^ n` of the cohomological side. This
is the `T`-adic local finiteness of item (1) of the blueprint theorem, together with item (2).
Item (3), the curve case, is obtained from it with the vanishing of `H_cⁱ` outside `[0, 2]`,
and item (4), the transport along `ι : ℚ̄_ℓ → ℂ`, by applying `ι` coefficientwise.

*Degrees.* The finite products over the cohomological degrees run over finite sets `S` and `T`
of integers outside of which the compactly supported cohomology, respectively the cohomology
sheaves, vanish; such sets exist by finiteness
(`AlgebraicGeometry.WeilComplex.exists_subsingleton_compactlySupportedCohomology` and
`AlgebraicGeometry.WeilComplex.exists_finset_isZero_homologySheaf`), and enlarging them does
not change the alternating determinants, the added factors being `1`.

*Hypotheses.* The blueprint theorem is stated for a Weil complex satisfying the finite-level
hypotheses of the trace formula with `E`-coefficients (étale-origin witnesses and compactification
admissibility for the reductions of a lattice of a representative). The Weil complexes of this
repository are constructible `ℚ̄_ℓ`-complexes on the pro-étale site of `X`, built directly from
pro-étale sheaves with no chosen lattice; those hypotheses are properties of the integral
models used in the proof, and are not part of the statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits PowerSeries

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

/-- Isomorphic Weil sheaves have the same characteristic polynomial of the local Frobenius at a
closed point. -/
theorem charpoly_frobeniusEnd_stalk_of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (x : X.finitePoints) :
    (F.stalk x).frobeniusEnd.charpoly = (G.stalk x).frobeniusEnd.charpoly :=
  let ⟨E⟩ := nonempty_equiv_stalk_of_iso e x
  E.charpoly_frobeniusEnd.symm

end WeilSheaf

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- Blueprint `theorem-trace-formula-euler-product`: Euler-product form of the trace formula.

Let `X₀` be a separated scheme of finite type over `k₀ = 𝔽_q` and `K` a Weil complex on `X₀`
with coefficients in `ℚ̄_ℓ`, `ℓ ≠ p`. Write `F` for the global geometric Frobenius on
`H_cⁱ(X, K)` and, for a closed point `x` of degree `e_x`, `F_x` for the local Frobenius on the
stalks `𝓗ʲ(K)_x̄`. Then

`L (X₀, K, T) = ∏_x det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹`
`  = ∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`

as formal power series over `ℚ̄_ℓ`, the product over the closed points being locally finite:
for every `n`, the coefficient of `T ^ n` of the finite product over any finite set `s` of
closed points containing those of degree at most `n` is the coefficient of `T ^ n` of the
right-hand side. Here `S` and `T` are finite sets of degrees outside of which `H_cⁱ(X, K)`,
respectively the cohomology sheaves `𝓗ʲ(K)`, vanish. This is assertion (2) of the blueprint
node, for `Λ = ℚ̄_ℓ`, with the local finiteness of assertion (1). -/
theorem coeff_prod_inv_alternatingCharpolyRevProd_stalk (K : WeilComplex k₀ l X)
    {S T : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (WeilComplex.compactlySupportedCohomology K i).carrier)
    (hT : ∀ j ∉ T, IsZero ((homologySheaf j).obj K)) (n : ℕ) (s : Finset X.finitePoints)
    (hs : ∀ x : X.finitePoints, (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (LinearMap.alternatingCharpolyRevProd T
        (fun j ↦ (WeilComplex.stalk K j x).frobeniusEnd)
          ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))⁻¹) =
      coeff n (LinearMap.alternatingCharpolyRevProd S
        (fun i ↦ (WeilComplex.compactlySupportedCohomology K i).frobeniusEnd) 1)⁻¹ := by
  classical
  have hd (x : X.finitePoints) : (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≠ 0 :=
    (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have hL := PowerSeries.X_mul_derivative_prod s fun x _ ↦
    LinearMap.X_mul_derivative_inv_alternatingCharpolyRevProd T
      (fun j ↦ (WeilComplex.stalk K j x).frobeniusEnd) (hd x)
  have hR := LinearMap.X_mul_derivative_inv_alternatingCharpolyRevProd S
    (fun i ↦ (WeilComplex.compactlySupportedCohomology K i).frobeniusEnd) one_ne_zero
  refine PowerSeries.coeff_eq_of_X_mul_derivative_eq hL hR ?_ ?_ (m := n) ?_ n le_rfl
  · rw [map_prod, PowerSeries.constantCoeff_inv,
      LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ one_ne_zero, inv_one]
    refine Finset.prod_eq_one fun x _ ↦ ?_
    rw [PowerSeries.constantCoeff_inv,
      LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ (hd x), inv_one]
  · simp
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    have hsupp : (Function.support fun j : ℤ ↦ (j.negOnePow : ℤ) •
        LinearMap.trace (PadicAlgCl l) _
          ((WeilComplex.compactlySupportedCohomology K j).frobeniusEnd ^ i)) ⊆ S := by
      intro j hj
      by_contra h
      have := hS j h
      have h0 : (WeilComplex.compactlySupportedCohomology K j).frobeniusEnd ^ i = 0 :=
        LinearMap.ext fun _ ↦ Subsingleton.elim _ _
      rw [Function.mem_support, h0, map_zero, smul_zero] at hj
      exact hj rfl
    have htr := K.finsum_trace_compactlySupportedCohomology_eq hi0
    rw [finsum_eq_sum_of_support_subset _ hsupp,
      (X ↘ Spec (CommRingCat.of k₀)).finsum_fieldPoints_eq_sum hi0.ne' _
        (fun x ↦ ∑ j ∈ T, (j.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((WeilComplex.stalk K j x).frobeniusEnd ^
            (i / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1)))
        (fun y x hx ↦ by
          rw [K.traceFunction_eq_sum T hT]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow _ i y x hx]
          rfl)
        (fun x hx ↦ hs x ((Nat.le_of_dvd hi0 hx).trans hi))] at htr
    simp only [map_sum, PowerSeries.coeff_mk]
    rw [ite_eq_left ⟨hi0.ne', one_dvd i⟩, Nat.cast_one, one_mul, Nat.div_one, htr,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [hi0.ne', nsmul_eq_mul]

end WeilComplex

namespace WeilSheaf

/-- The Euler-product form of the trace formula for a Weil sheaf `F` placed in degree zero:
for every `n` and every finite set `s` of closed points containing those of degree at most `n`,

`coeff_n ∏_{x ∈ s} det (1 - T ^ {e_x} F_x ∣ F_x̄)⁻¹`
`  = coeff_n ∏_i det (1 - T F ∣ H_cⁱ(X, F)) ^ ((-1) ^ (i + 1))`,

for a finite set `S` of degrees outside of which `H_cⁱ(X, F)` vanishes. This is
`AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk` for the Weil
complex `F[0]`, whose only cohomology sheaf is `𝓗⁰ = F`. -/
theorem coeff_prod_inv_localPolynomial_stalk (F : WeilSheaf k₀ l X) {S : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (F.compactlySupportedCohomology i).carrier) (n : ℕ)
    (s : Finset X.finitePoints)
    (hs : ∀ x : X.finitePoints, (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (((F.stalk x).localPolynomial.comp
        (Polynomial.X ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial _) :
          (PadicAlgCl l)⟦X⟧)⁻¹) =
      coeff n (LinearMap.alternatingCharpolyRevProd S
        (fun i ↦ (F.compactlySupportedCohomology i).frobeniusEnd) 1)⁻¹ := by
  have h := WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk (toComplex.obj F)
    (T := {0}) hS
    (fun j hj ↦ WeilComplex.isZero_homologySheaf_singleComplex (Finset.notMem_singleton.1 hj) F)
    n s hs
  refine Eq.trans (congrArg (coeff n) (Finset.prod_congr rfl fun x _ ↦ ?_)) h
  refine congrArg Inv.inv ?_
  rw [LinearMap.alternatingCharpolyRevProd, Finset.prod_singleton, ite_eq_left Even.zero,
    FrobeniusModule.localPolynomial, LinearMap.charpolyRev, LinearMap.charpolyRev]
  have h2 : (WeilComplex.stalk (toComplex.obj F) 0 x).frobeniusEnd.charpoly =
      (F.stalk x).frobeniusEnd.charpoly :=
    charpoly_frobeniusEnd_stalk_of_iso
      ((toComplexCompHomologySheafIso (k₀ := k₀) (l := l) (X := X)).app F) x
  rw [h2]

end WeilSheaf

end AlgebraicGeometry

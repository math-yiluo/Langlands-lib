/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.TraceFunctionLowerShriek
public import WeilConjectures.ZetaFunction.TraceFormula

/-!
# The trace function of the direct image along the squaring map

Let `k₀` be a finite field of odd characteristic and `f₀ : 𝔸¹ ⟶ 𝔸¹`, `x ↦ x²`, the squaring map.
The fibre of `f₀` over `y ∈ 𝔽_{qⁿ}` has `1 + χ(y)` rational points, `χ` the quadratic character
of `𝔽_{qⁿ}` (with `χ(0) = 0`), so the trace function of `Rf₀! ℚ̄_ℓ` is `1 + χ`: it is not
constant, although the sheaf pushed forward is. Summing over `y` gives `qⁿ`, the number of
rational points of the source.

## Main statements

- `quadraticChar_natCard_sq_eq`: `#{x : x² = a} = 1 + χ(a)` in a finite field of odd
  characteristic.
- `sum_one_add_quadraticChar`: `∑_a (1 + χ(a)) = #F`.
- `AlgebraicGeometry.affineLine.squaring`: the squaring map of the affine line.
- `AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerShriek_squaring`:
  `t_{Rf₀! ℚ̄_ℓ, n}(y) = 1 + χ(y)`.
- `AlgebraicGeometry.WeilComplex.finsum_traceFunction_derivedLowerShriek_squaring`:
  `∑_y t_{Rf₀! ℚ̄_ℓ, n}(y) = qⁿ`.

## Blueprint

`example-trace-function-squaring`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

section Arithmetic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Blueprint `example-trace-function-squaring` (arithmetic part): in a finite field of odd
characteristic, the number of square roots of `a` is `1 + χ(a)`, `χ` the quadratic character. -/
theorem quadraticChar_natCard_sq_eq (hF : ringChar F ≠ 2) (a : F) :
    (Nat.card {x : F // x ^ 2 = a} : ℤ) = 1 + quadraticChar F a := by
  classical
  rw [add_comm, ← quadraticChar_card_sqrts hF a, Nat.card_eq_fintype_card, Set.toFinset_card]
  exact congrArg Nat.cast (Fintype.card_congr (Equiv.refl _))

/-- Blueprint `example-trace-function-squaring` (arithmetic part): the function `1 + χ` sums to
the number of elements of the finite field, `χ` taking the values `±1` equally often on `F^×`. -/
theorem sum_one_add_quadraticChar (hF : ringChar F ≠ 2) :
    ∑ a : F, (1 + quadraticChar F a) = Fintype.card F := by
  rw [Finset.sum_add_distrib, quadraticChar_sum_zero hF, add_zero, Finset.sum_const,
    Finset.card_univ, nsmul_one]

end Arithmetic

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable (k₀) in
/-- The squaring map `x ↦ x²` of the affine line over `k₀`. -/
noncomputable def affineLine.squaring : affineLine k₀ ⟶ affineLine k₀ :=
  affineLine.homOfSection k₀ (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit ^ 2)

instance : (affineLine.squaring k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  inferInstanceAs ((affineLine.homOfSection k₀ _).IsOver (Spec (CommRingCat.of k₀)))

omit [Finite k₀] in
/-- The squaring map squares the coordinate of a rational point. -/
theorem affineLine.fieldPointsEquiv_mapFieldPoints_squaring (L : Type u) [Field L]
    [Algebra k₀ L] (x : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints L) :
    AffineSpace.fieldPointsEquiv k₀ L ((affineLine.squaring k₀).mapFieldPoints L x) =
      AffineSpace.fieldPointsEquiv k₀ L x ^ 2 := by
  rw [AffineSpace.fieldPointsEquiv_apply, AffineSpace.fieldPointsEquiv_apply,
    Scheme.Hom.mapFieldPoints_coe, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineLine.squaring, affineLine.homOfSection, AffineSpace.homOfVector_appTop_coord,
    map_pow, map_pow]

instance affineLine.isSeparated_squaring : IsSeparated (affineLine.squaring k₀) := by
  have : IsSeparated (affineLine.squaring k₀ ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    rw [comp_over]
    infer_instance
  exact IsSeparated.of_comp _ (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

instance affineLine.locallyOfFiniteType_squaring :
    LocallyOfFiniteType (affineLine.squaring k₀) := by
  have : LocallyOfFiniteType
      (affineLine.squaring k₀ ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    rw [comp_over]
    infer_instance
  exact locallyOfFiniteType_of_comp _ (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

instance affineLine.quasiCompact_squaring : QuasiCompact (affineLine.squaring k₀) := by
  have : QuasiCompact (affineLine.squaring k₀ ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    rw [comp_over]
    infer_instance
  exact QuasiCompact.of_comp _ (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

namespace WeilComplex

/-- **The trace function of the direct image along the squaring map**
(blueprint `example-trace-function-squaring`): for `k₀` of odd characteristic, `n ≥ 1` and
`y ∈ 𝔸¹(𝔽_{qⁿ}) = 𝔽_{qⁿ}`, the trace function of `Rf₀! ℚ̄_ℓ` along the squaring map
`f₀ : x ↦ x²` is `t(y) = 1 + χ(y)`, `χ` the quadratic character of `𝔽_{qⁿ}`. -/
theorem traceFunction_derivedLowerShriek_squaring (hq : ringChar k₀ ≠ 2) {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] [DecidableEq (FiniteField.galoisExtension k₀ n)]
    (y : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n)) :
    ((derivedLowerShriek k₀ l (affineLine.squaring k₀)).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀)))).traceFunction
          n y =
      ((1 + quadraticChar (FiniteField.galoisExtension k₀ n)
        (AffineSpace.fieldPointsEquiv k₀ _ y) : ℤ) : PadicAlgCl l) := by
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have hL : ringChar (FiniteField.galoisExtension k₀ n) ≠ 2 := by
    rwa [← Algebra.ringChar_eq k₀ (FiniteField.galoisExtension k₀ n)]
  rw [traceFunction_derivedLowerShriek _ _ hn]
  simp_rw [traceFunction_toComplex, WeilSheaf.traceFunction_adicConstant]
  let E := AffineSpace.fieldPointsEquiv k₀ (FiniteField.galoisExtension k₀ n)
  let e : {x // (affineLine.squaring k₀).mapFieldPoints _ x = y} ≃ {a // a ^ 2 = E y} :=
    E.subtypeEquiv fun x ↦ by
      rw [← affineLine.fieldPointsEquiv_mapFieldPoints_squaring, E.injective.eq_iff]
  have : Finite {x // (affineLine.squaring k₀).mapFieldPoints _ x = y} := .of_equiv _ e.symm
  have := Fintype.ofFinite {x // (affineLine.squaring k₀).mapFieldPoints _ x = y}
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    Nat.card_congr e, nsmul_one]
  exact_mod_cast quadraticChar_natCard_sq_eq hL _

/-- Blueprint `example-trace-function-squaring`: summing the trace function `1 + χ` of
`Rf₀! ℚ̄_ℓ` over `𝔸¹(𝔽_{qⁿ})` gives the number `qⁿ` of rational points of the source, as
the Grothendieck–Lefschetz formula predicts. -/
theorem finsum_traceFunction_derivedLowerShriek_squaring (hq : ringChar k₀ ≠ 2) {n : ℕ}
    (hn : n ≠ 0) :
    ∑ᶠ y, ((derivedLowerShriek k₀ l (affineLine.squaring k₀)).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀)))).traceFunction
          n y =
      (Nat.card k₀ ^ n : ℕ) := by
  classical
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  have := Fintype.ofFinite (FiniteField.galoisExtension k₀ n)
  have hL : ringChar (FiniteField.galoisExtension k₀ n) ≠ 2 := by
    rwa [← Algebra.ringChar_eq k₀ (FiniteField.galoisExtension k₀ n)]
  let χ : FiniteField.galoisExtension k₀ n → PadicAlgCl l :=
    fun a ↦ ((1 + quadraticChar (FiniteField.galoisExtension k₀ n) a : ℤ) : PadicAlgCl l)
  calc _ = ∑ᶠ y, χ (AffineSpace.fieldPointsEquiv k₀ _ y) :=
        finsum_congr fun y ↦ traceFunction_derivedLowerShriek_squaring hq hn y
    _ = ∑ᶠ a, χ a := finsum_comp_equiv (AffineSpace.fieldPointsEquiv k₀ _)
    _ = _ := by
      rw [finsum_eq_sum_of_fintype, ← Int.cast_sum, sum_one_add_quadraticChar hL,
        ← Nat.card_eq_fintype_card, FiniteField.nat_card_galoisExtension k₀ n hn,
        Int.cast_natCast]

end WeilComplex

end AlgebraicGeometry

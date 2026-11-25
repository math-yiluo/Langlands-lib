/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkConstantTwist
public import WeilConjectures.WeilSheaf.Tensor

/-!
# Pure lisse Weil sheaves are realizable

Let `F` be a lisse Weil sheaf, punctually `ι`-pure of weight `w`, and let `c` be a unit of `ℚ̄_ℓ`
with `ι c = q ^ w`. Then `F ⊕ (F^∨ ⊗ 𝓑_c)`, the sum of `F` and of the constant Weil twist by `c`
of its dual, is `ι`-real: at a closed point of degree `m` a local eigenvalue `α` of `F` gives the
eigenvalue `cᵐ α⁻¹` of the second summand, and `ι (cᵐ α⁻¹) = |ι α|² / ι α = conj (ι α)`.
The projection onto the first summand exhibits `F` as `ι`-realizable.

The eigenvalue computation is
`FrobeniusModule.IsPureOfWeight.isReal_prod_rescale_dual`; the stalks of a direct sum, of a dual
and of a constant twist are described by `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_biprod`,
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_dual` and
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_constantTwist`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.isReal_biprod_constantTwist_dual`: the
  sum `F ⊕ (F^∨ ⊗ 𝓑_c)` is `ι`-real.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.isRealizable`: `F` is `ι`-realizable.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- At a closed point `x` of degree `m`, the local polynomial of `F ⊕ (F^∨ ⊗ 𝓑_c)` is that of
`F_x̄ ⊕ (F_x̄)^∨(cᵐ)`, the sum of the stalk and of its dual with the Frobenius rescaled by
`cᵐ`. -/
theorem localPolynomial_stalk_biprod_constantTwist_dual {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) (c : (PadicAlgCl l)ˣ) (x : X.finitePoints) :
    ((F ⊞ (F.dual hF).constantTwist c).stalk x).localPolynomial =
      ((F.stalk x).prod ((F.stalk x).dual.rescale
        ((c : PadicAlgCl l) ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))).localPolynomial := by
  obtain ⟨e₁⟩ := F.nonempty_equiv_stalk_biprod ((F.dual hF).constantTwist c) x
  obtain ⟨e₂⟩ := (F.dual hF).nonempty_equiv_stalk_constantTwist c x
  obtain ⟨e₃⟩ := nonempty_equiv_stalk_dual hF x
  rw [e₁.localPolynomial_eq, FrobeniusModule.localPolynomial_prod,
    FrobeniusModule.localPolynomial_prod, e₂.localPolynomial_eq, (e₃.rescale _).localPolynomial_eq]

/-- **A pure lisse sheaf has a real envelope.** If `F` is lisse and punctually `ι`-pure of
weight `w`, and `ι c = q ^ w`, then `F ⊕ (F^∨ ⊗ 𝓑_c)` is `ι`-real: at a closed point of degree
`m`, with `q_x = qᵐ`, the stalk of `F` is pure of weight `w` relative to `q_x` and
`ι (cᵐ) = q_x ^ w`, so `FrobeniusModule.IsPureOfWeight.isReal_prod_rescale_dual` applies.
(blueprint: `proposition-twisting-weight-zero-adding-dual`) -/
theorem IsPunctuallyPureOfWeight.isReal_biprod_constantTwist_dual {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w)
    {c : (PadicAlgCl l)ˣ} (hc : ι c = (((Nat.card k₀ : ℝ) ^ w : ℝ) : ℂ)) :
    (F ⊞ (F.dual hF).constantTwist c).IsReal ι := by
  intro x
  refine FrobeniusModule.IsReal.of_localPolynomial_eq ?_
    (localPolynomial_stalk_biprod_constantTwist_dual hF c x)
  refine (h x).isReal_prod_rescale_dual (pow_pos Nat.card_pos _) ?_
  have hq : (0 : ℝ) ≤ Nat.card k₀ := Nat.cast_nonneg _
  change _ = ((((Nat.card k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 : ℕ) : ℝ) ^ w : ℝ) :
    ℂ)
  rw [map_pow, hc, ← Complex.ofReal_pow, Nat.cast_pow, ← Real.rpow_mul_natCast hq, mul_comm,
    Real.rpow_natCast_mul hq]

/-- **A pure lisse sheaf is realizable.** A lisse Weil sheaf `F` which is punctually `ι`-pure of
weight `w` is a direct summand of the `ι`-real lisse sheaf `F ⊕ (F^∨ ⊗ 𝓑_c)`, for any `c` with
`ι c = q ^ w`. (blueprint: `proposition-twisting-weight-zero-adding-dual`) -/
theorem IsPunctuallyPureOfWeight.isRealizable {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) {c : (PadicAlgCl l)ˣ}
    (hc : ι c = (((Nat.card k₀ : ℝ) ^ w : ℝ) : ℂ)) :
    F.IsRealizable ι :=
  ⟨_, biprod.inl, biprod.fst, hF.biprod (isLisse_constantTwist.2 hF.dual),
    h.isReal_biprod_constantTwist_dual hF hc, biprod.inl_fst⟩

end AlgebraicGeometry.WeilSheaf

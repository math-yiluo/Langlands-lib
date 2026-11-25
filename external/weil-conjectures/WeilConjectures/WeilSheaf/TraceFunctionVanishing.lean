/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.ZetaLinearAlgebra.TracePowVanishing

/-!
# Weil sheaves with vanishing trace function

A Weil sheaf on a `k₀`-scheme locally of finite type whose trace function vanishes at every
`𝔽_{qⁿ}`-rational point, `n ≥ 1`, is zero. At a closed point `x` of degree `e`, the
`𝔽_{q^{e j}}`-rational points over `x` show that all powers `Fₓʲ`, `j ≥ 1`, of the local
Frobenius on the stalk have trace zero
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow`); `Fₓ` being
invertible, the stalk is zero (`LinearMap.finrank_eq_zero_of_trace_pow_eq_zero`), and the
stalks at the closed points detect zero Weil sheaves
(`AlgebraicGeometry.WeilSheaf.exists_nontrivial_stalk_of_not_isZero`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_fieldPoints_base_eq_of_degreeOver_dvd`
- `AlgebraicGeometry.WeilSheaf.isZero_of_traceFunction_eq_zero`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A point `x` of a scheme over a finite field `k` with finite residue field is the image of
an `𝔽_{qⁿ}`-rational point as soon as its degree divides `n ≠ 0`: the residue field then
embeds into the extension of degree `n`. -/
theorem Scheme.Hom.exists_fieldPoints_base_eq_of_degreeOver_dvd {X : Scheme.{u}} {k : Type u}
    [Field k] [Finite k] (f : X.Hom (Spec (.of k))) {n : ℕ} (hn : n ≠ 0) {x : X}
    (hx : x ∈ X.finitePoints) (hdvd : f.degreeOver x ∣ n) :
    ∃ p : f.fieldPoints (FiniteField.galoisExtension k n),
      p.1.base (IsLocalRing.closedPoint _) = x := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have : Finite (X.residueField x) := X.mem_finitePoints.mp hx
  have : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  have h : Nonempty (X.residueField x →ₐ[k] FiniteField.galoisExtension k n) := by
    rw [FiniteField.nonempty_algHom_iff_finrank_dvd, FiniteField.finrank_galoisExtension k n hn]
    exact hdvd
  obtain ⟨φ⟩ := h
  obtain ⟨p, hp⟩ := (f.exists_fieldPoints_base_eq_iff (FiniteField.galoisExtension k n) x).2
    ⟨CommRingCat.ofHom φ.toRingHom, RingHom.ext fun c ↦ φ.commutes c⟩
  exact ⟨p, (congrArg p.1.base (Subsingleton.elim _ _)).trans hp⟩

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- **A Weil sheaf with vanishing trace function is zero.** If the trace function `t_{F,n}` of
a Weil sheaf `F` on a `k₀`-scheme locally of finite type vanishes at all `𝔽_{qⁿ}`-rational
points for all `n ≥ 1`, then `F = 0`: the powers of the local Frobenius at a closed point all
have trace zero, which forces the stalk to vanish, the Frobenius being invertible and `ℚ̄_ℓ`
of characteristic zero. -/
theorem isZero_of_traceFunction_eq_zero [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l X)
    (h : ∀ (n : ℕ), n ≠ 0 → ∀ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n), F.traceFunction n y = 0) :
    IsZero F := by
  by_contra hF
  obtain ⟨x, hx⟩ := F.exists_nontrivial_stalk_of_not_isZero hF
  have he := (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have key (j : ℕ) (hj : j ≠ 0) :
      LinearMap.trace (PadicAlgCl l) _ ((F.stalk x).frobeniusEnd ^ j) = 0 := by
    obtain ⟨y, hy⟩ := (X ↘ Spec (CommRingCat.of k₀)).exists_fieldPoints_base_eq_of_degreeOver_dvd
      (mul_ne_zero he hj) x.2 (dvd_mul_right _ j)
    rw [← Nat.mul_div_cancel_left j (Nat.pos_of_ne_zero he),
      ← F.traceFunction_eq_trace_frobeniusEnd_stalk_pow _ y x hy]
    exact h _ (mul_ne_zero he hj) y
  have h0 := LinearMap.finrank_eq_zero_of_trace_pow_eq_zero _
    (LinearEquiv.isUnit_det' (F.stalk x).frobenius) key
  exact (Module.finrank_pos (R := PadicAlgCl l) (M := (F.stalk x).carrier)).ne' h0

end WeilSheaf

end AlgebraicGeometry

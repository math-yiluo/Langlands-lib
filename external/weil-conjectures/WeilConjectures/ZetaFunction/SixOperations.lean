/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Package

/-!
# The six operations over the algebraic closure of a finite field

The Weil conjectures use the six operations for schemes of finite type over the algebraic
closure `k = k̄₀` of the finite field `k₀`, with finite coefficient rings `Λ` of `ℓ`-power order
for a prime `ℓ` different from the characteristic. This file records that the six-operations
package (`AlgebraicGeometry.Etale.sixOperationsPackage`, blueprint `sk-thm-sf-package`) applies in
this setting: the exponent `ℓⁿ` of `Λ` is invertible on `Spec k`.

## Main statements

- `AlgebraicGeometry.Etale.hasInvertibleExponent_spec_algebraicClosure`: `ℓⁿ` is invertible on
  `Spec k̄₀` for `ℓ ≠ p`.
- `AlgebraicGeometry.Etale.sixOperationsPackage_algebraicClosure`: blueprint
  `thm-weil-six-operations`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Etale

variable (k₀ : Type u) [Field k₀] [Finite k₀]

/-- For a prime `ℓ` different from the characteristic of the finite field `k₀`, a coefficient
ring `Λ` killed by `ℓⁿ` has invertible exponent on `Spec k̄₀`. -/
theorem hasInvertibleExponent_spec_algebraicClosure (Λ : Type*) [CommRing Λ] {l : ℕ}
    (hl : l.Prime) (hne : ringChar k₀ ≠ l) {n : ℕ} (hΛ : ((l ^ n : ℕ) : Λ) = 0) :
    HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀))) := by
  have hp : (ringChar k₀).Prime := CharP.char_is_prime k₀ (ringChar k₀)
  have : CharP (AlgebraicClosure k₀) (ringChar k₀) :=
    charP_of_injective_algebraMap (algebraMap k₀ (AlgebraicClosure k₀)).injective _
  have hk : ((l ^ n : ℕ) : AlgebraicClosure k₀) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure k₀) (ringChar k₀)]
    exact fun h ↦ hne ((Nat.prime_dvd_prime_iff_eq hp hl).1 (hp.dvd_of_dvd_pow h))
  refine ⟨l ^ n, pow_pos hl.pos n, hΛ, ?_⟩
  simpa using (Ne.isUnit hk).map (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of (AlgebraicClosure k₀)))
  [HasCompactification f] [QuasiCompact f] [IsSeparated f] [IsSeparated aY]
  [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
  [HasCompactification (f ≫ aY)]

/-- Blueprint `thm-weil-six-operations` (the six operations for the finite-field datum): the
clauses of the six-operations package (`sk-thm-sf-package`, `prop-functor-package`) hold for the
global finite-field datum, i.e. for separated morphisms `f : X ⟶ Y` of schemes of finite type
over the algebraic closure `k̄₀` of the finite field `k₀`, with coefficients in a finite ring `Λ`
killed by `ℓⁿ` for a prime `ℓ` different from the characteristic, carrying a normalized Tate
twist datum. This is the finite coefficient stage `A_{E,n}` of the package; the clauses are
those of `AlgebraicGeometry.Etale.SixOperationsPackage`. -/
theorem sixOperationsPackage_algebraicClosure {l : ℕ} (hl : l.Prime) (hne : ringChar k₀ ≠ l)
    {n : ℕ} (hΛ : ((l ^ n : ℕ) : Λ) = 0) :
    SixOperationsPackage Λ (AlgebraicClosure k₀) f aY :=
  have := hasInvertibleExponent_spec_algebraicClosure k₀ Λ hl hne hΛ
  sixOperationsPackage Λ (AlgebraicClosure k₀) f aY

end Etale

end AlgebraicGeometry

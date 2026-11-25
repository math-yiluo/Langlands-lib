/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Kähler differentials of a localization of a polynomial ring

If `T` is a localization of the polynomial ring `R[X_k : k ∈ σ]`, then `Ω[T⁄R]` is free over `T`
with basis the differentials `d X_k`.
-/

@[expose] public section

open Module

namespace KaehlerDifferential

variable (R : Type*) [CommRing R] (σ : Type*) (T : Type*) [CommRing T] [Algebra R T]
  [Algebra (MvPolynomial σ R) T] [IsScalarTower R (MvPolynomial σ R) T]
  (M : Submonoid (MvPolynomial σ R)) [IsLocalization M T]

/-- **Kähler differentials of a localization of a polynomial ring**: if `T` is a localization of
`R[X_k : k ∈ σ]`, then `Ω[T⁄R]` is free over `T` with basis the differentials of the variables
(`KaehlerDifferential.basisOfIsLocalizationMvPolynomial_apply`). -/
noncomputable def basisOfIsLocalizationMvPolynomial : Basis σ T Ω[T⁄R] :=
  (mvPolynomialBasis R σ).ofIsLocalizedModule T M (map R R (MvPolynomial σ R) T)

@[simp]
lemma basisOfIsLocalizationMvPolynomial_apply (k : σ) :
    basisOfIsLocalizationMvPolynomial R σ T M k =
      D R T (algebraMap (MvPolynomial σ R) T (MvPolynomial.X k)) := by
  have h : mvPolynomialBasis R σ k = D R (MvPolynomial σ R) (MvPolynomial.X k) :=
    (mvPolynomialBasis R σ).repr.injective (by
      rw [Basis.repr_self, mvPolynomialBasis_repr_D_X])
  rw [basisOfIsLocalizationMvPolynomial, Basis.ofIsLocalizedModule_apply, h, map_D]

end KaehlerDifferential

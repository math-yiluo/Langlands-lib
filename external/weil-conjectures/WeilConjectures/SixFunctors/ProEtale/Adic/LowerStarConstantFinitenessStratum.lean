/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFiniteness
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisseComponents

/-!
# Finiteness for the constant `ℓ`-adic sheaf, up to the semilinearity of the identifications

For `g : T ⟶ Y` quasi-compact and quasi-separated between schemes of finite type over a field,
`Y` quasi-compact, with `ℓ` invertible on `T`, the uniform stratification of `Y` for the torsion
direct images (`AlgebraicGeometry.ProEtale.exists_stratification_flcProperty_integers`, for
`E = ℚ_ℓ`) is one on whose strata all the `Rⁱg_* ℚ̄_ℓ,T` are lisse
(`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_upperStar_adicRightDerivedLowerStarUnit`), as soon
as the integral identifications are semilinear
(`AlgebraicGeometry.ProEtale.IntegralLatticeSemilinear`). Hence `Rg_* ℚ̄_ℓ,T` is bounded with
constructible cohomology sheaves
(`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_unit_of_integralLatticeSemilinear`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl TopologicalSpace

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {k : Type u} [Field k] {T Y : Scheme.{u}} (g : T ⟶ Y)
  [QuasiCompact g] [QuasiSeparated g] (aT : T ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aT] [QuasiCompact aT] [LocallyOfFiniteType aY] [QuasiCompact aY]
  (hg : g ≫ aY = aT)

variable (l)

include hg in
omit [QuasiCompact aT] in
/-- **The strata of the uniform stratification are lisse strata**: for `g : T ⟶ Y` between
schemes of finite type over a field, `Y` quasi-compact and `ℓ` invertible on `T`, there is a
stratification of `Y` on whose strata all the `Rⁱg_* ℚ̄_ℓ,T` are lisse, provided the integral
identifications are semilinear. -/
theorem exists_stratification_isAdicLisseSheaf_adicRightDerivedLowerStarUnit
    [HasInvertibleExponent (integersShrink.{u} l (finiteIntermediateFieldBot l).1 ⧸
      integersShrinkIdeal.{u} l (finiteIntermediateFieldBot l).1) T]
    (hψι : ∀ i, IntegralLatticeSemilinear l g i (finiteIntermediateFieldBot l)) :
    ∃ R : Scheme.Stratification Y, ∀ (i : ℕ) m, IsAdicLisseSheaf
      ((R.immersion m)^*ᵃ[l].obj (adicRightDerivedLowerStarUnit l g i)) := by
  obtain ⟨R, hR⟩ := exists_stratification_flcProperty_integers l
    (finiteIntermediateFieldBot l).1 g aT aY hg
  refine ⟨R, fun i m ↦ ?_⟩
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  have : NoetherianSpace (R.immersion m).coborderRange :=
    inferInstanceAs (NoetherianSpace ((R.immersion m).coborderRange : Set Y))
  rw [← Scheme.Hom.liftCoborder_ι (R.immersion m)]
  exact isAdicLisseSheaf_upperStar_adicRightDerivedLowerStarUnit l _ g _ _ (hR m) i
    (surjective_integersPadicIntHom_bot l) (hψι i)

variable (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞))

include hg hd in
/-- **Finiteness for the constant `ℓ`-adic sheaf, up to semilinearity.** Let `g : T ⟶ Y` be
quasi-compact and quasi-separated between schemes of finite type over a field, with `dim T ≤ d`,
and `ℓ` invertible on `T`. If the integral identifications are semilinear, then `Rg_* ℚ̄_ℓ,T` is
bounded with constructible cohomology sheaves. -/
theorem finiteLowerStar_singleFunctor_unit_of_integralLatticeSemilinear
    [HasInvertibleExponent (integersShrink.{u} l (finiteIntermediateFieldBot l).1 ⧸
      integersShrinkIdeal.{u} l (finiteIntermediateFieldBot l).1) T]
    (hψι : ∀ i, IntegralLatticeSemilinear l g i (finiteIntermediateFieldBot l)) :
    finiteLowerStar l g ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l T)) :=
  have ⟨R, hR⟩ := exists_stratification_isAdicLisseSheaf_adicRightDerivedLowerStarUnit l g aT aY
    hg hψι
  finiteLowerStar_singleFunctor_unit_of_stratification l g aT aY hg d hd R hR

end AlgebraicGeometry.ProEtale

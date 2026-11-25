/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.LineSmooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.TraceIsomorphism
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# Cohomology of the affine line with constant coefficients

The geometric affine line `𝔸¹_k̄` has the cohomology of a point: `H⁰(𝔸¹, ℚ̄_ℓ) = ℚ̄_ℓ` and
`Hʳ(𝔸¹, ℚ̄_ℓ) = 0` for `r ≠ 0`. The compactly supported cohomology is computed by the Thom
isomorphism for the trivial line bundle `π : 𝔸¹ ⟶ Spec k₀`: `Rπ₀! ℚ̄_ℓ = Rπ₀! π^* ℚ̄_ℓ ≅
ℚ̄_ℓ(-1)[-2]`, so that `H_cʳ(𝔸¹, ℚ̄_ℓ)` vanishes for `r ≠ 2`. By Poincaré duality on the smooth
curve `𝔸¹`, `Hʳ(𝔸¹, ℚ̄_ℓ(1))` is dual to `H_c^{2-r}(𝔸¹, ℚ̄_ℓ)`, hence vanishes for `r ≠ 0`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant_affineLine`:
  the vanishing of `H_cʳ(𝔸¹, ℚ̄_ℓ)` for `r ≠ 2`.
- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_affineLine`: the vanishing
  of `Hʳ(𝔸¹, ℚ̄_ℓ)` for `r ≠ 0`.
-/

@[expose] public section

-- `WeilConjectures.WeilSheaf.Localization` (through `FourierInversion.OtherSections`) brings in
-- `AlgebraicGeometry.specOverSpec`, under which `Spec k₀` would lie over itself through
-- `Algebra.id`; the canonical instance is given priority here.
attribute [local instance 1100] CategoryTheory.instOverClass

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {k₀ l} in
/-- **Thom isomorphism for the affine line.** For a Weil sheaf `P` on `Spec k₀` and the structure
morphism `π : 𝔸¹ ⟶ Spec k₀`, the cohomology sheaves `R^r π₀! π^* P` vanish for `r ≠ 2`:
`Rπ₀! π^* P ≅ P(-1)[-2]` by the rank-one Thom isomorphism, and the Tate twist of a sheaf placed
in degree zero is a sheaf placed in degree zero. -/
theorem isZero_homologySheaf_derivedLowerShriek_upperStar_affineLine
    (P : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) {r : ℤ} (hr : r ≠ 2) :
    IsZero ((WeilComplex.homologySheaf r).obj
      ((WeilComplex.derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj ((upperStar (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj P)))) := by
  obtain ⟨T⟩ := WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback
    (k₀ := k₀) (l := l) (X := Spec (CommRingCat.of k₀)) (Y := affineLine k₀)
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (𝟙 _) IsPullback.of_id_snd
  have hG := isLisse_tateTwistSheaf k₀ l (Spec (CommRingCat.of k₀)) (-1)
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor
    ((tateTwistSheaf k₀ l (Spec (CommRingCat.of k₀)) (-1)).dual hG).obj hG.dual
  -- `π^*` and the Tate twist, both exact, commute with placing a sheaf in degree zero
  let eU : toComplex.obj ((upperStar (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj P) ≅
      (WeilComplex.upperStar (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj P) :=
    (ObjectProperty.isoMk _ (((ProEtaleWeilSheaf.upperStar k₀ l
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).mapDerivedCategorySingleFunctor 0).app
        P.obj)).symm
  let eT : (WeilComplex.tateTwist k₀ l (Spec (CommRingCat.of k₀)) (-1)).obj (toComplex.obj P) ≅
      toComplex.obj (tensorObj (tateTwistSheaf k₀ l (Spec (CommRingCat.of k₀)) (-1)) P hG) :=
    ObjectProperty.isoMk _ ((ProEtaleWeilSheaf.ihomFunctor k₀ l (Spec (CommRingCat.of k₀))
      ((tateTwistSheaf k₀ l (Spec (CommRingCat.of k₀)) (-1)).dual
        hG).obj).singleFunctorCompRightDerivedFunctorIso.app P.obj)
  exact (isZero_homologySheaf_shift_toComplex _ (n := -2) (by omega)).of_iso
    ((WeilComplex.homologySheaf r).mapIso
      ((WeilComplex.derivedLowerShriek k₀ l _).mapIso eU ≪≫ T.app _ ≪≫
        (shiftFunctor _ (-2 : ℤ)).mapIso eT))

/-- `H_cʳ(𝔸¹_k̄, ℚ̄_ℓ) = 0` for `r ≠ 2`: the constant sheaf on `𝔸¹` is the pullback `π^* ℚ̄_ℓ` of
the constant sheaf on `Spec k₀`, and `Rπ₀! π^* ℚ̄_ℓ ≅ ℚ̄_ℓ(-1)[-2]` by the Thom isomorphism
(`AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_upperStar_affineLine`). -/
theorem subsingleton_compactlySupportedCohomology_adicConstant_affineLine {r : ℤ}
    (hr : r ≠ 2) :
    Subsingleton ((adicConstant k₀ l (affineLine k₀)).compactlySupportedCohomology r).carrier := by
  have : Subsingleton (((upperStar (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj
      (adicConstant k₀ l (Spec (CommRingCat.of k₀)))).compactlySupportedCohomology r).carrier :=
    subsingleton_globalSections_of_isZero
      (isZero_homologySheaf_derivedLowerShriek_upperStar_affineLine _ hr)
  exact (compactlySupportedCohomologyEquivOfIso (upperStarAdicConstantIso
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀))) r).toLinearEquiv.symm.toEquiv.subsingleton

/-- **Constant cohomology of the affine line.** `Hʳ(𝔸¹_k̄, ℚ̄_ℓ) = 0` for `r ≠ 0`: by Poincaré
duality on the smooth curve `𝔸¹`, `Hʳ(𝔸¹_k̄, ℚ̄_ℓ(1))`, which is `Hʳ(𝔸¹_k̄, ℚ̄_ℓ)` up to the
Frobenius, is dual to `H_c^{2-r}(𝔸¹_k̄, ℚ̄_ℓ)`, which vanishes since `2 - r ≠ 2`.
(blueprint: `lemma-integral-linear-character--2`, subsection
`lemma-artin-schreier-character-sheaf`) -/
theorem subsingleton_cohomology_adicConstant_affineLine {r : ℤ} (hr : r ≠ 0) :
    Subsingleton ((adicConstant k₀ l (affineLine k₀)).cohomology r).carrier := by
  obtain ⟨P, hP, -⟩ := exists_isPerfPair_compactlySupportedCohomology_adicConstant k₀ l
    (affineLine k₀) 1 (2 - r) r (by push_cast; ring)
  obtain ⟨E⟩ := nonempty_equiv_cohomology_tateTwistSheaf k₀ l (affineLine k₀) ((1 : ℕ) : ℤ) r
  have := subsingleton_compactlySupportedCohomology_adicConstant_affineLine k₀ l
    (r := 2 - r) (by omega)
  have : Subsingleton ((tateTwistSheaf k₀ l (affineLine k₀) ((1 : ℕ) : ℤ)).cohomology
      r).carrier :=
    hP.bijective_right.injective.subsingleton
  exact E.toLinearEquiv.symm.toEquiv.subsingleton

end AlgebraicGeometry.WeilSheaf

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitPoint
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
import WeilConjectures.RingTheory.StrictHenselizationAlgebraic

/-!

# The strict localization at the slice point is algebraic over the affine chart

Let `R₁` be a discrete valuation ring and `s = sliceTraitPoint b₁` the geometric point of `𝔸¹_{R₁}`
over the generic point of the special fibre. The ring `𝒪^{sh}_{𝔸¹_{R₁}, s}` of the strict
localization receives the chart map `g : R₁[x] ⟶ 𝒪^{sh}` and is a strict henselization of the
local ring `R₁[x]_q`. Since `𝒪^{sh}` is a domain, every element of it is algebraic over `R₁[x]_q`
(`Algebra.IsStrictHenselization.isAlgebraic`), hence over `R₁[x]` after clearing denominators.

## Main results

- `AlgebraicGeometry.exists_coord_isAlgebraic_strictHenselization_sliceTraitPoint`: the chart map
  `g : R₁[x] ⟶ 𝒪^{sh}` is compatible with the structure map, sends `x` to an element with value
  `traitSliceCoord κ₁` at the geometric point, and every element of `𝒪^{sh}` is a root of a nonzero
  polynomial with coefficients in `R₁[x]`.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

open Scheme

variable {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁] {κ₁ : Type u}
  [Field κ₁] (b₁ : R₁ →+* κ₁)

/-- **The strict localization at the slice point is algebraic over the affine chart.** There is a
ring map `g : R₁[x] ⟶ 𝒪^{sh}_{𝔸¹_{R₁}, s}` extending the structure map of `R₁`, sending the
coordinate to an element whose value at the geometric point is `traitSliceCoord κ₁`, such that
every element of `𝒪^{sh}` is a root of a nonzero polynomial with coefficients in `R₁[x]`. -/
theorem exists_coord_isAlgebraic_strictHenselization_sliceTraitPoint
    (hb₁ : RingHom.ker b₁ = maximalIdeal R₁) :
    ∃ g : MvPolynomial (ULift.{u} (Fin 1)) R₁ →+* strictHenselization (sliceTraitPoint b₁),
      g.comp MvPolynomial.C = sliceTraitStructureMap b₁ ∧
      (strictHenselizationEval (sliceTraitPoint b₁)).hom (g (MvPolynomial.X ⟨0⟩)) =
        traitSliceCoord κ₁ ∧
      ∀ r, ∃ f : Polynomial (MvPolynomial (ULift.{u} (Fin 1)) R₁),
        f ≠ 0 ∧ (f.map g).eval r = 0 := by
  have hdom := isDomain_strictHenselization_sliceTraitPoint b₁ hb₁
  rw [sliceTraitStructureMap, sliceTraitPoint_eq] at *
  obtain ⟨q, _, K, _, _, _, _, _, _, b, -, hb, hcomp, hH⟩ :=
    Scheme.strictHenselization_chart_isStrictHenselization _
      (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R₁)).inv
      (Spec.map (CommRingCat.ofHom (sliceTraitPointRingHom b₁)))
  refine ⟨b.hom, ?_, ?_, fun r ↦ ?_⟩
  · have hpre : Spec.preimage (strictLocalizationToBase _ ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁)) =
          CommRingCat.ofHom MvPolynomial.C ≫ b := by
      apply Spec.map_injective
      rw [Spec.map_preimage, ← hb, Category.assoc, AffineSpace.SpecIso_inv_over, Spec.map_comp]
    rw [hpre]
    rfl
  · have hev : b ≫ strictHenselizationEval _ = CommRingCat.ofHom (sliceTraitPointRingHom b₁) := by
      apply Spec.map_injective
      rw [← cancel_mono (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R₁)).inv, Spec.map_comp,
        Category.assoc, hb, spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
    have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hev) (MvPolynomial.X ⟨0⟩)
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h.trans (by simp [sliceTraitPointRingHom])
  · let := b.hom.toAlgebra
    have : IsScalarTower (MvPolynomial (ULift.{u} (Fin 1)) R₁) (Localization.AtPrime q) _ :=
      .of_algebraMap_eq fun a ↦ (hcomp a).symm
    have : Algebra.IsAlgebraic (MvPolynomial (ULift.{u} (Fin 1)) R₁) (Localization.AtPrime q) :=
      IsLocalization.isAlgebraic _ q.primeCompl
    obtain ⟨f, hf, hfr⟩ := (hH.isAlgebraic.isAlgebraic r).restrictScalars
      (MvPolynomial (ULift.{u} (Fin 1)) R₁)
    refine ⟨f, hf, ?_⟩
    rw [Polynomial.eval_map]
    exact hfr

end AlgebraicGeometry

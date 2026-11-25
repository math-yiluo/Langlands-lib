/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GenericQuotient
public import WeilConjectures.TraceFormula.ProjectiveLineFibre
public import WeilConjectures.TraceFormula.ProperCurve
public import WeilConjectures.TraceFormula.ShriekTraceFunctionFibre
public import WeilConjectures.TraceFormula.ShriekTraceFunctionOpenImmersion

/-!

# The sheaf–function compatibility along the relative projective and affine lines

Let `B` be a separated scheme of finite type over a finite field `k` with an automorphism `e_B`.
The sheaf–function compatibility (`ProEtale.CondensedRing.ShriekTraceFunctionAt`) holds along

1. the relative projective line `ℙ¹_B ⟶ B`, for the automorphisms `ℙ¹(e_B)` and `e_B`
   (`ProEtale.CondensedRing.shriekTraceFunctionAt_overProjectiveLineProj`): the geometric fibre
   at a point `ȳ` of degree `n + 1` is `ℙ¹_{k̄}` with the `q^{n+1}`-power Frobenius
   (`WeilConjectures.TraceFormula.ProjectiveLineFibre`), on which the trace formula is the
   Lefschetz–Verdier formula for the Frobenius graph on a proper smooth curve
   (`WeilBoundedConstructible.trace_globalOperator_eq_sum_of_smoothOfRelativeDimension_one`), and
   the compatibility at `ȳ` follows from the trace formula on the fibre
   (`weilStalkTraceAlternatingSum_weilLowerShriek_eq_finsum_of_fibre`);
2. the relative affine line `𝔸^{j+1}_k ×_k E ⟶ 𝔸ʲ_k ×_k E`
   (`ProEtale.CondensedRing.shriekTraceFunctionAt_overProdMap_polyAffineProj`), the composite of
   the open immersion into `ℙ¹_{𝔸ʲ_k ×_k E}` (`shriekTraceFunctionAt_of_isOpenImmersion`) and of
   the projection of item 1. This is the case of the affine line in blueprint
   `theorem-trace-formula-frobenius-correspondence--1`, the geometric base case of the trace
   formula.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding hasRightDualPoint

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option linter.overlappingInstances false in
/-- **The relative projective line**: the sheaf–function compatibility holds along
`ℙ¹_B ⟶ B` for the automorphisms `ℙ¹(e_B)` and `e_B`. At a point `ȳ` of degree `n + 1` the
geometric fibre is `ℙ¹_{k̄}` with the `q^{n+1}`-power Frobenius, a proper smooth curve with a model
Frobenius, on which the trace formula holds by the Lefschetz–Verdier formula. -/
theorem shriekTraceFunctionAt_overProjectiveLineProj (B : Over (Spec (.of k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (eB : B ≅ B) :
    ShriekTraceFunctionAt ℓ (overProjectiveLineIso eB) eB (overProjectiveLineMap_proj eB.hom) := by
  intro K n y
  obtain ⟨k₁, _, _, _, X₁, f₁, _, p₁, -, hΦ⟩ :=
    exists_isModelFrobenius_projectiveLineFibre k (AlgebraicClosure k) n
  have := finite_fixedPoint_projectiveLineFibreFrobenius k (AlgebraicClosure k) n
  let _ := Fintype.ofFinite (FixedPoint (projectiveLineFibreFrobenius k (AlgebraicClosure k) n) 1)
  have := hΦ.isFinite 1
  have := hΦ.isUniversalHomeomorphism 1
  have h₁ := hΦ.isFinite 1
  have h₂ := hΦ.isUniversalHomeomorphism 1
  rw [frobeniusIterate_one] at h₁ h₂
  exact weilStalkTraceAlternatingSum_weilLowerShriek_eq_finsum_of_fibre ℓ
    (overProjectiveLineMap_proj eB.hom) y (projectiveLineFibreι_comp eB y)
    (isPullback_projectiveLineFibreι eB y) K
    (WeilBoundedConstructible.trace_globalOperator_eq_sum_of_smoothOfRelativeDimension_one hΦ _
      le_rfl)

/-- **The affine line**: the sheaf–function compatibility holds along the coordinate projection
`𝔸^{j+1}_k ×_k E ⟶ 𝔸ʲ_k ×_k E`, the relative affine line over `B = 𝔸ʲ_k ×_k E`, for the
automorphisms `𝟙 ×_k e_E`. The relative affine line is the open complement of the section at
infinity in `ℙ¹_B` (`Scheme.overAffineLineι`), so the compatibility is the composite of the one
along the open immersion (`shriekTraceFunctionAt_of_isOpenImmersion`) and the one along
`ℙ¹_B ⟶ B` (`shriekTraceFunctionAt_overProjectiveLineProj`); this is the case of the affine
line in blueprint `theorem-trace-formula-frobenius-correspondence--1`. -/
theorem shriekTraceFunctionAt_overProdMap_polyAffineProj (j : ℕ) (E : Over (Spec (.of k)))
    [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom] (eE : E ≅ E)
    (he : ∃ m : ℕ, eE.pow (m + 1) = Iso.refl E) :
    ShriekTraceFunctionAt ℓ (overProdIso (Iso.refl (polyAffine k (j + 1))) eE)
      (overProdIso (Iso.refl (polyAffine k j)) eE)
      (overProdIso_refl_hom_comp_overProdMap (polyAffineProj k j) eE) := by
  obtain ⟨m, hm⟩ := he
  have hh : (overProdIso (Iso.refl (polyAffine k (j + 1))) eE).hom ≫ overAffineLineι j E =
      overAffineLineι j E ≫
        (overProjectiveLineIso (overProdIso (Iso.refl (polyAffine k j)) eE)).hom := by
    simpa only [overProdIso_hom, Iso.refl_hom, overProjectiveLineIso_hom] using
      overAffineLineι_naturality j eE.hom
  have hX : (overProdIso (Iso.refl (polyAffine k (j + 1))) eE).pow (m + 1) = Iso.refl _ := by
    rw [overProdIso_pow, hm, Iso.pow_refl, overProdIso_refl]
  have hZ : (overProjectiveLineIso (overProdIso (Iso.refl (polyAffine k j)) eE)).pow (m + 1) =
      Iso.refl _ := by
    rw [overProjectiveLineIso_pow, overProdIso_pow, hm, Iso.pow_refl,
      overProdIso_refl, overProjectiveLineIso_refl]
  exact ShriekTraceFunctionAt.of_eq ℓ (overAffineLineι_proj j E)
    (shriekTraceFunctionAt_comp ℓ _ _ _ hh (overProjectiveLineMap_proj _) ⟨m, hX⟩ ⟨m, hZ⟩
      (shriekTraceFunctionAt_of_isOpenImmersion ℓ k _ _ hh ⟨m, hX⟩)
      (shriekTraceFunctionAt_overProjectiveLineProj ℓ _ _))

end AlgebraicGeometry.ProEtale.CondensedRing

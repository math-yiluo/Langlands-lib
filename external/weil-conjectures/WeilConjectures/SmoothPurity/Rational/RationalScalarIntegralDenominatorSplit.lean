/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionConstructible
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationPureTensor
import WeilConjectures.SmoothPurity.Rational.RationalScalarIntegralTraceUnit
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientIntegralTrace
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionComplete
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionUniformizerPow

/-! # Ambient finite separable trace retraction

This is the ambient derived-category part of the coefficient-retract argument.
(blueprint: lem-sf-rational-scalar-integral-denominator-split).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Integral trace splitting of the multiplication map, up to a power of the uniformizer.

For a derived-complete complex `K` of completed `𝒪_F`-modules, let `Res K` be its derived
restriction to `𝒪_E` and `Ext (Res K)` its completed scalar extension back to `𝒪_F`.
Then there are integral morphisms `s : K ⟶ Ext (Res K)` and `μ : Ext (Res K) ⟶ K` with
`s ≫ μ = ϖ_F ^ n • 𝟙 K` for some `n`.

Mathematics: `Res K` is derived complete, so the finite-free completed comparison
identifies `Ext (Res K)` with the ordinary extension `𝒪_F ⊗_{𝒪_E} Res K`. The map `μ` is the
counit `z ⊗ k ↦ z k` of extension ⊣ restriction. Choose an `E`-basis `b_i` of `F` and its
trace-dual basis `c_i`, so that `∑ i, b_i c_i = 1` and `∑ i, c_i ⊗ b_i` is the separability
idempotent of `F ⊗_E F`. Clear denominators: `δ c_i, b_i ∈ 𝒪_F` with `δ = u ϖ_F ^ n`. Then
`s : k ↦ ∑ i, u⁻¹ δ c_i ⊗ b_i k` is `𝒪_F`-linear by the centralizing identity of the
separability idempotent, and `μ ∘ s = ϖ_F ^ n`. These are termwise formulas on complexes of
sheaves, so they descend to the derived category.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; Stacks Project Tags 090W and
02FL (separability idempotent).
(blueprint: lem-sf-rational-scalar-integral-denominator-split).

Proof: `rationalScalarIntegral_unit_comp_counit` gives natural maps of module sheaves whose
composite is multiplication by an integer `N = c ϖ_F ^ n`, `c` a unit (the Frobenius unit of
the completed coefficient map followed by the multiplication counit, rescaled). Applied
termwise to a representative complex of `K` they give the composite `N • 𝟙 K`; the exact
ordinary extension is identified with the completed one on the complete object `Res K`
(`isIso_completedScalarComparison_app`). Rescaling by `c⁻¹` gives the claim. -/
theorem rationalScalarIntegral_trace_split
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l F W)) (hK : IsSfDerivedComplete l F W K) :
    ∃ (n : ℕ)
      (s : K ⟶ (integralScalarExtension l E F ι W).obj
        ((rationalScalarDerivedRestriction l E F ι W).obj K))
      (μ : (integralScalarExtension l E F ι W).obj
        ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶ K),
      s ≫ μ = Padic.coefficientExtensionUniformizer l F ^ n • 𝟙 K := by
  obtain ⟨N, σ, τ, hN, hστ⟩ := rationalScalarIntegral_unit_comp_counit l E F ι W
  obtain ⟨n, c, hc⟩ := Padic.exists_eq_unit_mul_coefficientExtensionUniformizer_pow l F hN
  let Res := rationalScalarModuleRestriction l E F ι W
  let Ord := integralOrdinaryScalar l E F ι W
  let := (rationalScalarModuleRestriction_exact l E F ι W).1
  let := (rationalScalarModuleRestriction_exact l E F ι W).2
  let P := DerivedCategory.Q.objPreimage K
  let eP : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let RK := (rationalScalarDerivedRestriction l E F ι W).obj K
  have := isIso_completedScalarComparison_app l E W F ι RK
    (rationalScalarDerivedRestriction_isSfDerivedComplete l E F ι W K hK)
  let χ : (integralOrdinaryDerivedScalar l E F ι W).obj RK ≅
      (integralScalarExtension l E F ι W).obj RK :=
    asIso ((integralOrdinaryDerivedScalarIso l E W F ι).hom.app RK ≫
      (completedScalarComparison l E F ι W).app RK)
  let eR : RK ≅ DerivedCategory.Q.obj ((Res.mapHomologicalComplex _).obj P) :=
    (rationalScalarDerivedRestriction l E F ι W).mapIso eP.symm ≪≫
      Res.mapDerivedCategoryFactors.app P
  let eO : (integralOrdinaryDerivedScalar l E F ι W).obj RK ≅
      DerivedCategory.Q.obj ((Ord.mapHomologicalComplex _).obj
        ((Res.mapHomologicalComplex _).obj P)) :=
    (integralOrdinaryDerivedScalar l E F ι W).mapIso eR ≪≫
      Ord.mapDerivedCategoryFactors.app _
  let σP : P ⟶ (Ord.mapHomologicalComplex _).obj ((Res.mapHomologicalComplex _).obj P) :=
    { f i := σ.app (P.X i)
      comm' i j _ := (σ.naturality (P.d i j)).symm }
  let τP : (Ord.mapHomologicalComplex _).obj ((Res.mapHomologicalComplex _).obj P) ⟶ P :=
    { f i := τ.app (P.X i)
      comm' i j _ := (τ.naturality (P.d i j)).symm }
  have hP : σP ≫ τP = N • 𝟙 P := by
    ext i : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f]
    exact hστ (P.X i)
  refine ⟨n, (↑c⁻¹ : Padic.coefficientExtensionIntegers l F) •
    (eP.inv ≫ DerivedCategory.Q.map σP ≫ eO.inv ≫ χ.hom),
    χ.inv ≫ eO.hom ≫ DerivedCategory.Q.map τP ≫ eP.hom, ?_⟩
  simp only [Linear.smul_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, hP, Functor.map_nsmul, CategoryTheory.Functor.map_id,
    Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, Iso.inv_hom_id,
    ← Nat.cast_smul_eq_nsmul (Padic.coefficientExtensionIntegers l F), smul_smul, hc,
    Units.inv_mul_cancel_left]

/-- The finite separable trace construction gives an ambient retract after
restriction of coefficients.  Constructibility is handled separately.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; Stacks Project
Tags 090W and 02FL.
(blueprint: lem-sf-rational-scalar-integral-denominator-split).

Proof: use the trace-dual basis of the finite separable extension F/E.  Restrict
K along the completed coefficient map.  The trace-dual section and multiplication
retraction are defined on the derived representatives and descend through scalar
localization; their composite is the identity by the two dual-basis identities. -/
theorem rationalScalar_ambient_trace_retract
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (K : sfRationalConstructibleCategory l F W) :
    Nonempty (Retract
      (ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l F)
      (C := DerivedCategory (scalarReductionSource l F W))
      (p := Padic.coefficientExtensionUniformizer l F) K.obj.obj)
      (ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l F)
        (C := DerivedCategory (scalarReductionSource l F W))
        (p := Padic.coefficientExtensionUniformizer l F)
        ((sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj
          ⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
            rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩).obj.obj)) := by
  obtain ⟨n, s, μ, h⟩ := rationalScalarIntegral_trace_split l E F ι W K.obj.obj K.obj.property.1
  rw [congrArg (fun Z : sfRationalConstructibleCategory l F W ↦ Z.obj.obj)
    (sfRationalScalarExtension_obj l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι _)]
  exact ⟨ScalarLocalization.retractOfSmulSplit n s μ h⟩

end WeilConjectures

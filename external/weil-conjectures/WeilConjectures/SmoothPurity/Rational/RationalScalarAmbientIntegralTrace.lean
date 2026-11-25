/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFrobeniusSystem
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapHomotopyCategoryCongr
import WeilConjectures.CategoryTheory.Adjunction.HomEquivCompAppOfIsIso

/-! # Integral ambient trace before rational localization

This is the integral derived part of the ambient trace argument. It is kept
separate from the denominator-clearing transport through scalar localization.
(blueprint: new-sf-rational-scalar-ambient-integral-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : AlgebraicGeometry.Scheme.{u})

/-- The two specified completed coefficient maps `𝒪_E^∧ ⟶ 𝒪_F^∧` coincide: both are
characterised by their composites with the finite quotient projections.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.8.2(1)
(blueprint: new-sf-rational-scalar-ambient-integral-trace). -/
theorem completedCoefficientMap_eq_integralCompletedScalarMap
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) :
    completedCoefficientMap l E F ι W = integralCompletedScalarMap l E F ι W :=
  (completedCoefficientMap_existsUnique l E F ι W).unique
    (completedCoefficientMap_existsUnique l E F ι W).exists.choose_spec
    (integralCompletedScalarMap_existsUnique l E F ι W).exists.choose_spec

/-- The two specified ordinary sheafified scalar extensions along `𝒪_E^∧ ⟶ 𝒪_F^∧` are
equal: both have the change-of-rings objects and maps along the same coefficient map.
Source: Stacks Tag 03EK (blueprint: new-sf-rational-scalar-ambient-integral-trace). -/
theorem completedOrdinaryScalarExtension_eq_integralOrdinaryScalar
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) :
    completedOrdinaryScalarExtension l E F ι W = integralOrdinaryScalar l E F ι W := by
  obtain ⟨hFo, hFm, -⟩ := (completedScalarChangeData l E F ι W).choose_spec
  obtain ⟨hGo, hGm, -⟩ := (integralOrdinaryScalarWitness l E F ι W).choose_spec
  have hφ := completedCoefficientMap_eq_integralCompletedScalarMap l E W F ι
  unfold completedOrdinaryScalarExtension integralOrdinaryScalar
  generalize (completedScalarChangeData l E F ι W).choose = G at hFo hFm ⊢
  generalize completedCoefficientMap l E F ι W = φ at hFo hFm hφ
  subst hφ
  exact CategoryTheory.Functor.ext (fun M ↦ (hFo M).trans (hGo M).symm) (fun M N a ↦ by
    rw [hFm, hGm]
    simp)

/-- The exact ordinary derived scalar extension is the universal derived scalar extension.
Source: Stacks Tag 06YY (blueprint: new-sf-rational-scalar-ambient-integral-trace). -/
noncomputable def integralOrdinaryDerivedScalarIso
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) :
    integralOrdinaryDerivedScalar l E F ι W ≅ completedDerivedScalarExtension l E F ι W :=
  let q := HomotopyCategory.quasiIso (integralTowerModules l E W) (ComplexShape.up ℤ)
  let ε : DerivedCategory.Qh ⋙ completedDerivedScalarExtension l E F ι W ⟶
      (completedOrdinaryScalarExtension l E F ι W).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
    (completedScalarChangeData l E F ι W).choose_spec.choose_spec.choose_spec.choose_spec
      |>.2.2.choose_spec.choose
  letI : (integralOrdinaryScalar l E F ι W).mapDerivedCategory.IsLeftDerivedFunctor
      (integralOrdinaryScalar l E F ι W).mapDerivedCategoryFactorsh.hom q :=
    Functor.isLeftDerivedFunctor_of_inverts q _
      (integralOrdinaryScalar l E F ι W).mapDerivedCategoryFactorsh
  letI : (completedDerivedScalarExtension l E F ι W).IsLeftDerivedFunctor ε q :=
    (completedScalarChangeData l E F ι W).choose_spec.choose_spec.choose_spec.choose_spec
      |>.2.2.choose_spec.choose_spec.1
  Functor.leftDerivedNatIso _ (completedDerivedScalarExtension l E F ι W)
    (integralOrdinaryScalar l E F ι W).mapDerivedCategoryFactorsh.hom ε q
    (eqToIso (by
      rw [Functor.mapHomotopyCategory_congr (ComplexShape.up ℤ)
        (completedOrdinaryScalarExtension_eq_integralOrdinaryScalar l E W F ι)]))

/-- The completed scalar comparison is invertible on derived complete objects.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: new-sf-rational-scalar-ambient-integral-trace). -/
theorem isIso_completedScalarComparison_app
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (hK : IsSfDerivedComplete l E W K) :
    IsIso ((completedScalarComparison.{u, u} l E F ι W).app K) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hp⟩
  let Δ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_refl 1
      cardinality_eq := (pow_one p).symm
      k₀ := ZMod p
      card_base := by simp
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ Δ.p := (by omega : l < p).ne
  exact ((finiteFreeCompletedScalarComparison.{u, u} l E F ι W).2.1 K
    ⟨Δ, hl, (sfDerivedComplete_iff_legacy l E W Δ hl K).mp hK⟩).1

/-- Frobenius reciprocity for the finite free completed coefficient extension: exact
restriction of scalars along `𝒪_E^∧ ⟶ 𝒪_F^∧` is left adjoint to the ordinary (sheafified)
extension of scalars `𝒪_F^∧ ⊗_{𝒪_E^∧} -`.

Mathematics: restriction is always left adjoint to coextension
`M ↦ Hom_{𝒪_E^∧}(𝒪_F^∧, M)`. Choose an `𝒪_E`-basis `(b_i)` of `𝒪_F` and a Frobenius form
`t : 𝒪_F → 𝒪_E`, i.e. a generator of the rank one free `𝒪_F`-module `Hom_{𝒪_E}(𝒪_F, 𝒪_E)`
(the inverse different is principal; `Module.exists_bijective_comp_mulLeft`), with dual
basis `(b_i^*)`, `t(b_i b_j^*) = δ_ij`. Since `𝒪_F^∧ = 𝒪_F ⊗_{𝒪_E} 𝒪_E^∧` is finite free
(`completedIntegralFiniteFree`), the unit `N ⟶ 𝒪_F^∧ ⊗ N`, `n ↦ ∑ b_i ⊗ b_i^* n`, and
the counit `𝒪_F^∧ ⊗ M ⟶ M`, `s ⊗ m ↦ t(s) m`, are well-defined maps of sheaves of modules
and satisfy the triangle identities by the dual-basis identities.

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.8.14(2) and
Remark 6.8.15 (finite coefficient extension); Stacks Tags 03CZ, 03EK (restriction and
extension of scalars for sheaves of modules); the constant-coefficient analogue is used in
`WeilConjectures.PurStrictScalar.scalarTensor_preservesKInjective`.
(blueprint: new-sf-rational-scalar-ambient-integral-trace).

Proof: `integralOrdinaryScalar_restrictScalars_adjunction`, the Frobenius-system adjunction
for the completed coefficient sheaves. -/
theorem pbcRestrict_integralCompletedScalarMap_adjunction
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) :
    Nonempty (AlgebraicGeometry.Scheme.pbcRestrict (integralCompletedScalarMap l E F ι W) ⊣
      integralOrdinaryScalar l E F ι W) :=
  integralOrdinaryScalar_restrictScalars_adjunction l E F ι W

/-- Integral trace data, before passing to the scalar-localized categories.
Source: Bhatt--Scholze, Proposition 6.8.14(2), finite separable trace and
finite-free completed scalar comparison.
(blueprint: new-sf-rational-scalar-ambient-integral-trace).

Proof: choose a trace-dual basis for the finite separable extension F/E. The
usual restriction/coextension unit and counit are finite sums, so one common
integral denominator makes them maps of completed coefficient sheaves. The
trace-dual identities prove the two triangles on complexes and on roofs in the
derived category. Exactness of restriction and finite-free extension carries
the construction through the chosen derived restriction; the comparison for a
complete E-object identifies the finite-free extension with the recorded
integral scalar extension. The same formulas commute with every constructible
map, giving the displayed naturality equation. -/
theorem rationalScalarAmbientIntegralTrace
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W)) :
    ∃ e : ∀ M : sfIntegralConstructibleCategory l E W,
      ((rationalScalarDerivedRestriction l E F ι W).obj K ⟶ M.obj) ≃
        (K ⟶ ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).obj M).obj),
      ∀ (M N : sfIntegralConstructibleCategory l E W) (f : M ⟶ N) (h),
        e N (h ≫ f.hom) =
          e M h ≫ ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).map f).hom := by
  let Res := rationalScalarModuleRestriction l E F ι W
  let Ord := integralOrdinaryScalar l E F ι W
  have hRes : Res = AlgebraicGeometry.Scheme.pbcRestrict
      (integralCompletedScalarMap l E F ι W) := by
    rw [← completedCoefficientMap_eq_integralCompletedScalarMap l E W F ι]
    rfl
  obtain ⟨adj₀⟩ := pbcRestrict_integralCompletedScalarMap_adjunction l E W F ι
  let adj : Res ⊣ Ord := adj₀.ofNatIsoLeft (eqToIso hRes.symm)
  let := (rationalScalarModuleRestriction_exact l E F ι W).1
  let := (rationalScalarModuleRestriction_exact l E F ι W).2
  let : CatCommSq (Res.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q Res.mapDerivedCategory := ⟨Res.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (Ord.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q Ord.mapDerivedCategory := ⟨Ord.mapDerivedCategoryFactors.symm⟩
  let dadj : Res.mapDerivedCategory ⊣ Ord.mapDerivedCategory :=
    (adj.mapHomologicalComplex (.up ℤ)).localization DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) Res.mapDerivedCategory Ord.mapDerivedCategory
  exact dadj.exists_homEquiv_comp_app_of_isIso
    ((integralOrdinaryDerivedScalarIso l E W F ι).hom ≫ completedScalarComparison l E F ι W)
    (sfIntegralConstructible l E W) (fun M hM ↦ IsIso.comp_isIso' inferInstance
      (isIso_completedScalarComparison_app l E W F ι M hM.1)) K

end WeilConjectures

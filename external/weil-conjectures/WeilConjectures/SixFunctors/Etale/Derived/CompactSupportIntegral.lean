/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.SixFunctors.Adic.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Compact support at the integral and rational stages

Let `E/ℚ_ℓ` be a finite extension inside `ℚ̄_ℓ` with ring of integers `𝒪_E` and maximal ideal
`𝔪_E = (ϖ_E)`, and let `f : X ⟶ Y` be a morphism admitting a compactification. The blueprint
defines, for `K ∈ Dᵇc(X, 𝒪_E)` with reductions `K_n = K ⊗ᴸ_{𝒪_E} A_{E,n}`,

`Rf_! K = R lim_n Res_n Rf_{!,n} K_n`,

and for an object `K_E` of the rational stage represented by `K`, `Rf_! K_E = (Rf_! K) ⊗ᴸ E`.

As everywhere in the repository (see `Etale.rightDerivedLowerStarDerivedCompleteIntegral`
and `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegralOfSupport`), the integral
stage is realised as the derived complete objects `D_comp(X_ét, 𝒪_E)` of the derived category of
étale sheaves of `𝒪_E`-modules, the reductions `Res_n K_n` as the `𝒪_E`-complexes
`K ⊗ᴸ (𝒪_E/𝔪_Eⁿ)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`), and the rational stage as the
rationalization `D_comp(X_ét, E)` of `D_comp(X_ét, 𝒪_E)`
(`DerivedCategoryDerivedCompleteRational`). The integral functor is defined as the derived
completion `(Rf_! K)^ = R lim_n ((Rf_! K) ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` of the étale `Rf_! K` over `𝒪_E`; since
`Rf_!` commutes with the reductions
(`Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isWeaklyRegular`)
and the completion does not change them
(`AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_completionAdjunction_unit_app`), its
reductions are the étale `Rf_!` of the reductions `K_n`
(`nonempty_iso_reductionModIdeal_rightDerivedLowerShriekDerivedCompleteIntegral`),
and as a derived complete object it is the homotopy limit of these
(`DerivedCategory.derivedCompleteIntegral_iff_exists_iso`): this is the blueprint's
`R lim_n Res_n Rf_{!,n} K_n`. It is defined on all of `D_comp(X_ét, 𝒪_E)`, which contains
`Dᵇc(X, 𝒪_E)`.

The rational functor is induced on rationalizations
(`CategoryTheory.Rationalization.map`), which is the blueprint's
`Rf_! K_E = (Rf_! K) ⊗ᴸ_{𝒪_E} E`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedCompleteRationalFromIntegralIso`); in
particular it does not depend on the integral representative:
`AlgebraicGeometry.Etale.nonempty_iso_fromIntegral_rightDerivedLowerShriekDerivedCompleteIntegral`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedCompleteIntegral`: `Rf_!` at `𝒪_E`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedCompleteRational`: `Rf_!` at `E`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_compactSupportIntegral
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- A nonzerodivisor forms a weakly regular sequence of length one. -/
lemma isWeaklyRegular_singleton_of_mem_nonZeroDivisors {Λ : Type*} [CommRing Λ] {r : Λ}
    (hr : r ∈ nonZeroDivisors Λ) : RingTheory.Sequence.IsWeaklyRegular Λ [r] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
  refine ⟨fun a b h ↦ ?_, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩
  have h' : (a - b) * r = 0 := by
    change r * a = r * b at h
    rw [sub_mul, mul_comm a, mul_comm b, h, sub_self]
  exact sub_eq_zero.1 ((mul_right_mem_nonZeroDivisors_eq_zero_iff hr).1 h')

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. -/
local notation "𝐌" => ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- Integral, rational, and algebraically closed compact-support functors (the integral stage
`𝒪_E`).

The compact-support direct image `Rf_! : D_comp(X_ét, 𝒪_E) ⥤ D_comp(Y_ét, 𝒪_E)`,
`K ↦ R lim_n Res_n Rf_{!,n} K_n`: the derived completion of the étale `Rf_! K` over `𝒪_E`. Its
reductions modulo `𝔪_Eⁿ` are the étale `Rf_!` of the reductions `K_n`
(`nonempty_iso_reductionModIdeal_rightDerivedLowerShriekDerivedCompleteIntegral`),
and, being derived complete, it is the homotopy limit of its reductions; so it is the
blueprint's `R lim_n Res_n Rf_{!,n} K_n`, computed for the chosen compactification of `f`
(blueprint `proposition-construction-independence-rf-shriek`). -/
noncomputable def rightDerivedLowerShriekDerivedCompleteIntegral :
    DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E :=
  DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌] ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E

noncomputable instance : (rightDerivedLowerShriekDerivedCompleteIntegral l E f).CommShift ℤ :=
  inferInstanceAs ((DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌] ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E).CommShift ℤ)

/-- The integral compact-support functor is exact, being a composite of triangulated functors
(`proposition-construction-independence-rf-shriek--1` for `Rf_!`, and the derived completion). -/
instance : (rightDerivedLowerShriekDerivedCompleteIntegral l E f).IsTriangulated :=
  inferInstanceAs ((DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌] ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E).IsTriangulated)

/-- The integral compact-support functor is `𝒪_E`-linear. -/
instance : (rightDerivedLowerShriekDerivedCompleteIntegral l E f).Linear
    (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  inferInstanceAs ((DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌] ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E).Linear _)

/-- The value of the integral `Rf_!` is the derived completion of the étale `Rf_!`: the unit of
the derived completion, `Rf_! K ⟶ (Rf_! K)^`. -/
noncomputable def toRightDerivedLowerShriekDerivedCompleteIntegral
    (K : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) :
    (R(f)_![𝐌]).obj ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K) ⟶
      (DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj
        ((rightDerivedLowerShriekDerivedCompleteIntegral l E f).obj K) :=
  (DerivedCategoryDerivedCompleteIntegral.completionAdjunction _ l E).unit.app _

/-- The unit `Rf_! K ⟶ (Rf_! K)^` induces isomorphisms on all reductions modulo `𝔪_Eⁿ`. -/
instance (n : ℕ) (K : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) :
    IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n)).map
      (toRightDerivedLowerShriekDerivedCompleteIntegral l E f K)) :=
  isIso_reductionModIdeal_map_completionAdjunction_unit_app l E n _

/-- The reductions of the integral compact-support direct image. For `K ∈ D_comp(X_ét, 𝒪_E)` and
`n : ℕ`,

`Res_n ((Rf_! K) ⊗ᴸ A_{E,n}) ≅ Res_n Rf_{!,n} K_n`,

naturally in `K`, both sides realised as `𝒪_E`-complexes: the completion does not change the
reductions, and `Rf_!` commutes with the reduction modulo the regular element `ϖ_Eⁿ`. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerShriekDerivedCompleteIntegral (n : ℕ) :
    Nonempty (rightDerivedLowerShriekDerivedCompleteIntegral l E f ⋙
        DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙
          reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n) ≅
      DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙
        reductionModIdeal _ X (PadicAlgCl.maximalIdealShrink l E ^ n) ⋙ R(f)_![𝐌]) := by
  obtain ⟨hϖ, hI⟩ := (PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u}
    l E).choose_spec
  set ϖ := (PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E).choose
  have hJ : PadicAlgCl.maximalIdealShrink l E ^ n = Ideal.ofList [ϖ ^ n] := by
    rw [hI, Ideal.span_singleton_pow]
    simp [Ideal.ofList]
  obtain ⟨e⟩ : Nonempty (R(f)_![𝐌] ⋙
      reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n) ≅
      reductionModIdeal _ X (PadicAlgCl.maximalIdealShrink l E ^ n) ⋙ R(f)_![𝐌]) := by
    rw [hJ]
    exact nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_isWeaklyRegular f
      [ϖ ^ n] (isWeaklyRegular_singleton_of_mem_nonZeroDivisors (pow_mem hϖ n))
  let τ : DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ R(f)_![𝐌] ⋙
        reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n) ⟶
      rightDerivedLowerShriekDerivedCompleteIntegral l E f ⋙
        DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙
          reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n) :=
    { app K := (reductionModIdeal _ Y _).map
        (toRightDerivedLowerShriekDerivedCompleteIntegral l E f K)
      naturality K K' φ := by
        simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp]
        congr 1
        exact (DerivedCategoryDerivedCompleteIntegral.completionAdjunction _ l E).unit.naturality
          ((R(f)_![𝐌]).map ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).map φ)) }
  have : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact inferInstanceAs (IsIso ((reductionModIdeal _ Y _).map
      (toRightDerivedLowerShriekDerivedCompleteIntegral l E f K)))
  exact ⟨(asIso τ).symm ≪≫ Functor.isoWhiskerLeft _ e⟩

/-- Integral, rational, and algebraically closed compact-support functors (the rational stage `E`).

The compact-support direct image `Rf_! : D_comp(X_ét, E) ⥤ D_comp(Y_ét, E)` at the rational
stage, the functor induced on the rationalizations by the integral compact-support functor
`AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedCompleteIntegral`, which is exact and
`𝒪_E`-linear (the rational transport of the integral functor). On an
object `K_E` represented by an integral `K` it is `(Rf_! K) ⊗ᴸ_{𝒪_E} E`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedCompleteRationalFromIntegralIso`). -/
noncomputable def rightDerivedLowerShriekDerivedCompleteRational :
    DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E :=
  Rationalization.map _ (rightDerivedLowerShriekDerivedCompleteIntegral l E f)

/-- The rational compact-support functor on the image `K ⊗ᴸ_{𝒪_E} E` of an integral object `K`
is `(Rf_! K) ⊗ᴸ_{𝒪_E} E`, naturally in `K`. -/
noncomputable def rightDerivedLowerShriekDerivedCompleteRationalFromIntegralIso :
    DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E ⋙
        rightDerivedLowerShriekDerivedCompleteRational l E f ≅
      rightDerivedLowerShriekDerivedCompleteIntegral l E f ⋙
        DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E :=
  Rationalization.mapFac _ _

/-- Independence of the integral representative.

If two integral complexes `K, K'` represent the same object of the rational stage, through an
isomorphism `e : K ⊗ᴸ E ≅ K' ⊗ᴸ E`, then `(Rf_! K) ⊗ᴸ_{𝒪_E} E` and `(Rf_! K') ⊗ᴸ_{𝒪_E} E` are
canonically isomorphic: both are the value of the rational compact-support functor (the unique
extension of the exact `𝒪_E`-linear integral functor to the rationalization) on that object, and
the isomorphism is its image of `e`. -/
noncomputable def rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso
    {K K' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    (e : (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).obj K ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).obj K') :
    (DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).obj
        ((rightDerivedLowerShriekDerivedCompleteIntegral l E f).obj K) ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).obj
        ((rightDerivedLowerShriekDerivedCompleteIntegral l E f).obj K') :=
  ((rightDerivedLowerShriekDerivedCompleteRationalFromIntegralIso l E f).app K).symm ≪≫
    (rightDerivedLowerShriekDerivedCompleteRational l E f).mapIso e ≪≫
      (rightDerivedLowerShriekDerivedCompleteRationalFromIntegralIso l E f).app K'

/-- The representative comparison of the identity is the identity. -/
@[simp]
lemma rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso_refl
    (K : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E) :
    rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso l E f (Iso.refl
      ((DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).obj K)) =
      Iso.refl _ := by
  ext
  simp [rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso]

/-- The representative comparisons are transitive. -/
lemma rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso_trans
    {K K' K'' : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E}
    (e : (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).obj K ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).obj K')
    (e' : (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).obj K' ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).obj K'') :
    rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso l E f (e ≪≫ e') =
      rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso l E f e ≪≫
        rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso l E f e' := by
  ext
  simp [rightDerivedLowerShriekDerivedCompleteIntegralRepresentativeIso]

end Etale

end AlgebraicGeometry

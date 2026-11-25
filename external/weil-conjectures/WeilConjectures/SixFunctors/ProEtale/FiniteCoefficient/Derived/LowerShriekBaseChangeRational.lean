/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChangeComplete
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Triangulated

/-!
# Compact-support base change over a finite extension of `ℚ_ℓ`

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E`. The integral stage
`D_comp(X_proét, 𝒪_E)` consists of the derived complete objects of `D(X_proét, 𝒪_E)`
(`DerivedCategoryDerivedCompleteIntegral`), and the rational stage `D_comp(X_proét, E)` is its
rationalization (`DerivedCategoryDerivedCompleteRational`). Following the blueprint, the
operations of the rational stage are obtained by transport from the integral stage
(`CategoryTheory.Rationalization.map`): the integral operations, `K ↦ (F K)^` for the plain
operation `F`, are `𝒪_E`-linear triangulated functors between the integral stages.

* `AlgebraicGeometry.ProEtale.integralRightDerivedLowerShriek`: the integral compact-support
  direct image `K ↦ (Rf_! K)^`, and `rationalRightDerivedLowerShriek` its transport to the rational
  stages.
* `AlgebraicGeometry.ProEtale.rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap`:
  the rational compact-support exchange map, the transport of the completed one.

## Main statements

- `isIso_rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap_app`: compact-support
  base change over a finite extension `E` of `ℚ_ℓ`.
- `AlgebraicGeometry.ProEtale.nonempty_iso_fromIntegral_integralRightDerivedLowerShriek`: the
  rational compact-support direct image does not depend on the integral representative.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E]

set_option hygiene false in
/-- The ring of integers `𝒪_E`, in the universe `u + 1`. -/
local notation "𝐎" => Shrink.{u + 1} (PadicAlgCl.integers l E)

set_option hygiene false in
/-- The derived category `D(X_proét, 𝒪_E)`. -/
local notation "𝐃(" X ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} 𝐎))

set_option hygiene false in
/-- The integral stage `D_comp(X_proét, 𝒪_E)`. -/
local notation "𝐃𝐜(" X ")" =>
  DerivedCategoryDerivedCompleteIntegral (Scheme.ProEt.topology X) l E

set_option hygiene false in
/-- The rational stage `D_comp(X_proét, E)`. -/
local notation "𝐃𝐐(" X ")" =>
  DerivedCategoryDerivedCompleteRational (Scheme.ProEt.topology X) l E

set_option hygiene false in
/-- The submonoid of nonzero elements of `𝒪_E`, inverted by the rationalization. -/
local notation "𝐌" => nonZeroDivisors 𝐎

/-! ### Integral operations -/

section Integral

variable {X Y : Scheme.{u}}

/-- The extension by zero along an open immersion, on the derived categories of pro-étale
sheaves of `Λ`-modules, is `Λ`-linear, being left adjoint to the `Λ`-linear restriction. -/
instance linear_mapDerivedCategory_openImmersionLowerShriek (Λ : Type (u + 1)) [CommRing Λ]
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    D((j)_!open[ModuleCat.{u + 1} Λ]).Linear Λ :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).left_adjoint_linear

/-- The compact-support direct image `Rf_!(c) = D(i_!) ⋙ R(g_*)` of pro-étale sheaves of
`Λ`-modules is `Λ`-linear. -/
instance linear_rightDerivedLowerShriekOfCompactification (Λ : Type (u + 1)) [CommRing Λ]
    {f : X ⟶ Y} (c : Compactification f) : Rf_!(c)[ModuleCat.{u + 1} Λ].Linear Λ :=
  inferInstanceAs ((D((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙
    R((c.g)_*[ModuleCat.{u + 1} Λ])).Linear Λ)

/-- The integral version `K ↦ (F K)^` of an operation `F : D(X_proét, 𝒪_E) ⥤ D(Y_proét, 𝒪_E)`,
a functor between the integral stages: the inclusion of the derived complete objects, followed by
`F` and by the derived completion. -/
noncomputable abbrev integralOperation (F : 𝐃(X) ⥤ 𝐃(Y)) : 𝐃𝐜(X) ⥤ 𝐃𝐜(Y) :=
  DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ F ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E

section

variable (F : 𝐃(X) ⥤ 𝐃(Y))

/-- The integral version of an operation commuting with shifts commutes with shifts. -/
noncomputable instance commShift_integralOperation [F.CommShift ℤ] :
    (integralOperation l E F).CommShift ℤ :=
  inferInstanceAs ((DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ F ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E).CommShift ℤ)

/-- The integral version of a triangulated operation is triangulated. -/
instance isTriangulated_integralOperation [F.CommShift ℤ] [F.IsTriangulated] :
    (integralOperation l E F).IsTriangulated :=
  inferInstanceAs (DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ F ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E).IsTriangulated

/-- The integral version of an `𝒪_E`-linear operation is `𝒪_E`-linear. -/
instance linear_integralOperation [F.Linear 𝐎] : (integralOperation l E F).Linear 𝐎 :=
  inferInstanceAs ((DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ F ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E).Linear 𝐎)

end

/-- The integral compact-support direct image `K ↦ (Rf_!(c) K)^ = R lim_n Rf_!(c) K_n` of a
compactification `c` of `f`. -/
noncomputable abbrev integralRightDerivedLowerShriek {f : X ⟶ Y} (c : Compactification f) :
    𝐃𝐜(X) ⥤ 𝐃𝐜(Y) :=
  integralOperation l E Rf_!(c)[ModuleCat.{u + 1} 𝐎]

/-- The compact-support direct image `D_comp(X_proét, E) ⥤ D_comp(Y_proét, E)` at the rational
stage `E` of a compactification `c` of `f`, the transport to the rationalizations of the
integral compact-support direct image (`CategoryTheory.Rationalization.map`). -/
noncomputable abbrev rationalRightDerivedLowerShriek {f : X ⟶ Y} (c : Compactification f) :
    𝐃𝐐(X) ⥤ 𝐃𝐐(Y) :=
  Rationalization.map 𝐌 (integralRightDerivedLowerShriek l E c)

/-- Independence of the integral representative.

Let `K, K' ∈ D_comp(X_proét, 𝒪_E)` be integral complexes representing the same object of the
rationalized category `D_comp(X_proét, E)`. Then the rationalizations `(Rf_! K) ⊗ E` and
`(Rf_! K') ⊗ E` of their integral compact-support direct images are canonically isomorphic: the
integral compact-support direct image is an exact `𝒪_E`-linear functor, so it extends to the
rationalizations (`CategoryTheory.Rationalization.map`), and the extension identifies both objects
with its value on the common rationalization. -/
theorem nonempty_iso_fromIntegral_integralRightDerivedLowerShriek {f : X ⟶ Y}
    (c : Compactification f) {K K' : 𝐃𝐜(X)}
    (e : (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K') :
    Nonempty ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj
        ((integralRightDerivedLowerShriek l E c).obj K) ≅
      (DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj
        ((integralRightDerivedLowerShriek l E c).obj K')) :=
  ⟨(Rationalization.mapFac 𝐌 (integralRightDerivedLowerShriek l E c)).symm.app K ≪≫
    (rationalRightDerivedLowerShriek l E c).mapIso e ≪≫
    (Rationalization.mapFac 𝐌 (integralRightDerivedLowerShriek l E c)).app K'⟩

end Integral

/-! ### The rational exchange map -/

section Exchange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The completed compact-support exchange map, restricted to the integral stage: a natural
transformation `(Lg^* Rf_!(c) K)^ ⟶ (Rf'_!(c') Lg'^* K)^` of functors
`D_comp(X_proét, 𝒪_E) ⥤ D_comp(Y'_proét, 𝒪_E)`
(`AlgebraicGeometry.ProEtale.completedRightDerivedLowerShriekOfCompactificationBaseChangeMap`,
on the derived complete objects). -/
noncomputable def integralRightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    integralOperation l E (Rf_!(c)[ModuleCat.{u + 1} 𝐎] ⋙ L((g)^*[ModuleCat.{u + 1} 𝐎])) ⟶
      integralOperation l E (L((g')^*[ModuleCat.{u + 1} 𝐎]) ⋙
        Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} 𝐎]) :=
  Functor.whiskerLeft (DerivedCategoryDerivedCompleteIntegral.ι _ l E)
    (Functor.whiskerRight
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} 𝐎) sq c)
      (DerivedCategoryDerivedCompleteIntegral.completion _ l E))

lemma integralRightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃𝐜(X)) :
    (integralRightDerivedLowerShriekOfCompactificationBaseChangeMap l E sq c).app K =
      (DerivedCategoryDerivedCompleteIntegral.completion _ l E).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} 𝐎) sq
          c).app ((DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K)) :=
  rfl

/-- The rational compact-support exchange map `Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` on the rational
stage `D_comp(X_proét, E)`, the transport to the rationalizations
(`CategoryTheory.Rationalization.mapNatTrans`) of the integral exchange map
`AlgebraicGeometry.ProEtale.integralRightDerivedLowerShriekOfCompactificationBaseChangeMap`. -/
noncomputable def rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    Rationalization.map 𝐌
        (integralOperation l E (Rf_!(c)[ModuleCat.{u + 1} 𝐎] ⋙ L((g)^*[ModuleCat.{u + 1} 𝐎]))) ⟶
      Rationalization.map 𝐌 (integralOperation l E (L((g')^*[ModuleCat.{u + 1} 𝐎]) ⋙
        Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} 𝐎])) :=
  Rationalization.mapNatTrans 𝐌
    (integralRightDerivedLowerShriekOfCompactificationBaseChangeMap l E sq c)

/-- Compact-support base change over a finite extension.

For a finite extension `E/ℚ_ℓ`, a cartesian square `g' ≫ f = f' ≫ g` with `g` arbitrary and a
compactification `c` of `f` (`remark-base-change-compactification--1`), and an object of the
rational stage `D_comp(X_proét, E)` given by an integral lattice `K ∈ D_comp(X_proét, 𝒪_E)` whose
reductions `K_n = K ⊗ᴸ 𝒪_E/𝔪_Eⁿ` carry étale-origin witnesses, the rational compact-support
exchange map `Lg^* Rf_! K ⟶ Rf'_! Lg'^* K` is an isomorphism in `D_comp(Y'_proét, E)`. It is
natural, being a component of a natural transformation, and it does not depend on the lattice:
it is the component at the rationalization of `K` of a natural transformation of functors on the
rational stage
(`AlgebraicGeometry.ProEtale.rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap`).

The isomorphism is transported from the integral one,
`proposition-composition-base-change-rf-shriek--4`
(`isIso_completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app`), along the
rationalization. -/
theorem isIso_rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃𝐜(X))
    (Kn : ∀ n : ℕ, _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (𝐎 ⧸ PadicAlgCl.maximalIdealShrink l E ^ n))))
    (η : ∀ n : ℕ, (DerivedCategoryDerivedCompleteIntegral.ι _ l E).obj K ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X)
        (Ideal.Quotient.mk (PadicAlgCl.maximalIdealShrink l E ^ n))).obj (Kn n))
    (hη : ∀ n : ℕ, Sheaf.IsDerivedBaseChange (η n))
    (hKn : ∀ n : ℕ, DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (𝐎 ⧸ PadicAlgCl.maximalIdealShrink l E ^ n)) X (Kn n)) :
    IsIso ((rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap l E sq c).app
      ((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).obj K)) := by
  have : ∀ n : ℕ, Finite (𝐎 ⧸ PadicAlgCl.maximalIdealShrink l E ^ n) := fun n ↦
    .of_equiv _ (Ideal.quotientEquiv _ _ (PadicAlgCl.shrinkRingEquiv l E)
      (by rw [PadicAlgCl.maximalIdealShrink, Ideal.map_pow]; rfl)).toEquiv
  have h := isIso_completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E) sq c _ K.2
    Kn η hη hKn
  have h' : IsIso ((integralRightDerivedLowerShriekOfCompactificationBaseChangeMap l E sq
      c).app K) := by
    rw [integralRightDerivedLowerShriekOfCompactificationBaseChangeMap_app]
    exact h
  rw [rationalRightDerivedLowerShriekOfCompactificationBaseChangeMap]
  erw [Rationalization.mapNatTrans_app]
  infer_instance

end Exchange

end AlgebraicGeometry.ProEtale

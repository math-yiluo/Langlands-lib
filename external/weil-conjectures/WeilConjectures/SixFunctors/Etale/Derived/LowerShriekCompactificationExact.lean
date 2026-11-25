/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# Compact support along one compactification

For a finite coefficient ring `Λ` and a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of
`f : X ⟶ Y`, the derived lower shriek `Rf_!(c) = D(i_!) ⋙ Rg_*` on the unbounded derived
categories of étale sheaves of `Λ`-modules is triangulated, commutes with coproducts and, for
`Y` of finite type over a field on which the exponent of `Λ` is invertible, carries `Dctf(X, Λ)`
into `Dctf(Y, Λ)` (blueprint `proposition-construction-independence-rf-shriek`).

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification_isTriangulated_and_ctf`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `proposition-construction-independence-rf-shriek`: compact support along one
compactification.

Let `c = (X ⟶[i] Z ⟶[g] Y)` be a compactification of `f`, with `i` an open immersion and `g`
proper. Then `Rf_!(c) = D(i_!) ⋙ Rg_* : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` is a triangulated functor,
preserves coproducts, and, if `f` is quasi-compact and `Y` is of finite type over a field `k`
with the exponent of `Λ` invertible on `Y`, it carries `Dctf(X, Λ)` into `Dctf(Y, Λ)`.

The blueprint states this for admissible `Λ` on the pro-étale site, as a functor between the
localizing closures `Loc(Dctf(-, Λ))`. The repository models the compactly supported direct image
`Rf_!(c)` for finite `Λ` on the whole unbounded derived category of the étale site, and does not
model localizing closures. Restricting to `Loc(Dctf)` is then automatic from the three clauses
proved here: the objects whose image lies in `Loc(Dctf(Y, Λ))` form a triangulated subcategory
closed under coproducts containing `Dctf(X, Λ)`.

The proof is the blueprint's: `D(i_!)` is triangulated, a left adjoint, and preserves `Dctf`
(`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek`);
`Rg_*` is triangulated, preserves coproducts since `g` is proper
(`AlgebraicGeometry.Etale.preservesColimitsOfShape_rightDerivedLowerStar_of_isProper`) and
preserves `Dctf` (`AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`). -/
theorem rightDerivedLowerShriekOfCompactification_isTriangulated_and_ctf
    (c : Compactification f) :
    (Rf_!(c)[ModuleCat.{u + 1} Λ]).IsTriangulated ∧
      (∀ J : Type (u + 1),
        PreservesColimitsOfShape (Discrete J) (Rf_!(c)[ModuleCat.{u + 1} Λ])) ∧
      ∀ (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
        [HasInvertibleExponent Λ Y] [QuasiCompact f]
        {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
          constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
            ((Rf_!(c)[ModuleCat.{u + 1} Λ]).obj K) := by
  refine ⟨inferInstance, fun J ↦ ?_, fun aY _ _ _ _ K hK ↦ ?_⟩
  · have : (D((c.i)_!open[ModuleCat.{u + 1} Λ])).IsLeftAdjoint :=
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) c.i).isLeftAdjoint
    have := preservesColimitsOfShape_rightDerivedLowerStar_of_isProper Λ isAddTorsion_of_finite
      c.g J
    exact comp_preservesColimitsOfShape _ _
  · have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    obtain ⟨hbc, a, b, hta⟩ := hK
    have h := constructibleTorAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek Λ c.i a b
      ⟨⟨hbc, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩, hta⟩
    exact constructibleFiniteTor_rightDerivedLowerStar Λ (c.g ≫ aY) aY c.g rfl ⟨h.1.1, a, b, h.2⟩

end Etale

end AlgebraicGeometry

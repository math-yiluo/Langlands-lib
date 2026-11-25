/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeTriangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness

/-!

# Coefficients and geometric categories

This file formalises the coefficient setup of the trace formula (blueprint `sk-d-setup`): the
subcategories `Dᵇctf(X, A) ⊂ D(X_proét, A)` of bounded constructible complexes of finite Tor
amplitude are triangulated, closed under isomorphisms, stable under `Lf^*` for every morphism
`f` and under `Rf_!` for compactifiable quasi-compact morphisms to schemes of finite type over
the base field (the blueprint asks for every compactifiable morphism).

The blueprint fixes `A = 𝒪_E/ϖ_Eⁿ` for a finite extension `E/ℚ_ℓ` and `ℓ` invertible on the base
field `k`. Here `A` is generalised to an arbitrary finite commutative ring `Λ` whose exponent is
invertible on `k` (`AlgebraicGeometry.HasInvertibleExponent`).

## Main definitions

- `AlgebraicGeometry.ProEtale.IsCoefficientSetup`: the properties required of a family of
  subcategories `P X ⊂ D(X_proét, Λ)` in the blueprint.

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_constructibleFiniteTor`:
  `Dᵇctf(X, Λ)` is a triangulated subcategory of `D(X_proét, Λ)`.
- `AlgebraicGeometry.ProEtale.isCoefficientSetup_constructibleFiniteTor`: the family
  `X ↦ Dᵇctf(X, Λ)` satisfies `IsCoefficientSetup`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `Dᵇctf(X, Λ)` is a triangulated subcategory of `D(X_proét, Λ)`, for a finite ring `Λ`. -/
instance DerivedCategory.isTriangulated_constructibleFiniteTor [Finite Λ] (X : Scheme.{u}) :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
  inferInstanceAs (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ⊓
    DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) X).IsTriangulated

/-- Blueprint `sk-d-setup`: the coefficient data of the trace formula.

A family `P X ⊂ D(X_proét, Λ)` of subcategories, indexed by all schemes `X`, is a *coefficient
setup* over the field `k` if every `P X` is a triangulated subcategory of `D(X_proét, Λ)`,
closed under isomorphisms, the family is stable under `Lf^*` for every morphism `f`, and stable
under `Rf_!` for every compactifiable quasi-compact morphism `f : X ⟶ Y` whose target `Y` is
locally of finite type and quasi-compact over `Spec k`.

The blueprint takes `Λ = 𝒪_E/ϖ_Eⁿ`; this predicate makes sense for any coefficient ring, and
`AlgebraicGeometry.ProEtale.isCoefficientSetup_constructibleFiniteTor` proves it for
`P = Dᵇctf(-, Λ)` with `Λ` finite of exponent invertible on `k`. -/
structure IsCoefficientSetup (k : Type u) [Field k]
    (P : ∀ X : Scheme.{u},
      ObjectProperty (_root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))) :
    Prop where
  /-- Each `P X` is a triangulated subcategory of `D(X_proét, Λ)`. -/
  isTriangulated (X : Scheme.{u}) : (P X).IsTriangulated
  /-- Each `P X` is closed under isomorphisms. -/
  isClosedUnderIsomorphisms (X : Scheme.{u}) : (P X).IsClosedUnderIsomorphisms
  /-- Stability under the derived pullback `Lg^*` along any morphism `g`. -/
  leftDerivedFunctor_upperStar_obj {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))} (hK : P X K) :
    P Y (L((g)^*[ModuleCat.{u + 1} Λ]).obj K)
  /-- Stability under the compact-support direct image `Rf_!` along a compactifiable
  quasi-compact morphism `f` whose target is locally of finite type and quasi-compact over
  `Spec k`. This deviates from the blueprint, which asks for every compactifiable `f`; the
  geometric schemes of the blueprint are of finite type over `k`, so this is the case used. -/
  rightDerivedLowerShriek_obj {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) [HasCompactification f]
    [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))} (hK : P X K) :
    P Y ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K)

/-- Blueprint `sk-d-setup`: the subcategories `Dᵇctf(X, Λ)` of bounded constructible complexes
of finite Tor amplitude form a coefficient setup over `k`, for a finite commutative ring `Λ`
whose exponent is invertible on `k`. This generalises the blueprint's `A = 𝒪_E/ϖ_Eⁿ` with `ℓ`
invertible in `k`. -/
theorem isCoefficientSetup_constructibleFiniteTor [Finite Λ] (k : Type u) [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    IsCoefficientSetup Λ k fun X ↦ DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
    where
  isTriangulated _ := inferInstance
  isClosedUnderIsomorphisms _ := inferInstance
  leftDerivedFunctor_upperStar_obj g _ hK :=
    constructibleFiniteTor_leftDerivedFunctor_upperStar_obj g hK
  rightDerivedLowerShriek_obj aY _ _ f _ _ _ hK :=
    have : HasInvertibleExponent Λ _ := HasInvertibleExponent.of_hom aY
    constructibleFiniteTor_rightDerivedLowerShriek Λ aY f hK

end AlgebraicGeometry.ProEtale

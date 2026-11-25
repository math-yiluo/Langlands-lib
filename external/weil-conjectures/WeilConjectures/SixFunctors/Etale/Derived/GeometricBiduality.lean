/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.BidualitySupport
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPointSupport
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Finite-stage étale Verdier biduality: the closed-point step

This file contains the closing argument of the proof of blueprint
`theorem-verdier-biduality--1`. Let `δ : K ⟶ 𝔻𝔻K` be completed to a distinguished triangle
`K ⟶ 𝔻𝔻K ⟶ Δ ⟶ K[1]`. If the cohomology sheaves of the bounded constructible `Δ` vanish at every
non-closed point, then `Δ` is supported on a finite set of closed points
(`AlgebraicGeometry.Etale.exists_isFinite_isZero_upperStar_of_boundedConstructible`); if moreover
`Ra_*δ` is an isomorphism, then `Ra_*Δ = 0`, and so `Δ = 0`
(`AlgebraicGeometry.Etale.isZero_of_isZero_rightDerivedLowerStar_of_isFinite`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `theorem-verdier-biduality--1`, the closed-point step: let
`a : X ⟶ Spec k` be locally of finite type with `X` quasi-compact, and let `T` be a distinguished
triangle in `D(X_ét, Λ)` whose third term is bounded constructible with cohomology sheaves
vanishing at every non-closed point. If `Ra_*` carries the first morphism of `T` to an
isomorphism, then the third term of `T` is zero. -/
theorem isZero_obj₃_of_isIso_rightDerivedLowerStar_map {k : Type u} [Field k] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a] [CompactSpace X]
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _)
    (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X T.obj₃)
    (hgen : ∀ (q : ℤ), ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj T.obj₃)))
    (ha : IsIso ((R((a)_*[ModuleCat.{u + 1} Λ])).map T.mor₁)) : IsZero T.obj₃ := by
  obtain ⟨Z, U, i, j, _, _, _, hij, hj⟩ :=
    exists_isFinite_isZero_upperStar_of_boundedConstructible a T.obj₃ hbc hgen
  refine isZero_of_isZero_rightDerivedLowerStar_of_isFinite Λ a i j hij hj ?_
  exact Triangle.isZero₃_of_isIso₁ _ ((R((a)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hT) ha

end Etale

end AlgebraicGeometry

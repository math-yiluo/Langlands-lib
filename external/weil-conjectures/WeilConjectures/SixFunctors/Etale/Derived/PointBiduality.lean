/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation

/-!
# Verdier biduality at a point

On a scheme `S` with a single point — for instance the spectrum of a separably closed field —
the dualizing complex of `𝟙_S` is the unit (`AlgebraicGeometry.Etale.dualizingComplexIdIso`),
and every object of `Dctf(S, Λ)` is perfect, that is dualizable
(`AlgebraicGeometry.Etale.isDualizable_of_constructibleFiniteTor_of_subsingleton`). Hence the
double-dual map `K ⟶ 𝔻_S 𝔻_S K` is an isomorphism: this is the coefficient biduality of blueprint
`lemma-perfect-complexes-geometric-point--8` (derived evaluation into the coefficient double dual is
an isomorphism for every perfect complex), the base case of the induction in
`theorem-verdier-biduality--1`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- Blueprint `lemma-perfect-complexes-geometric-point--8` (the derived form): for the identity of a
scheme `S`, whose dualizing complex is the unit, the double-dual map of a dualizable `K` is an
isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_id_of_isDualizable {Λ : Type (u + 1)} [CommRing Λ]
    [Finite Λ] (S : Scheme.{u})
    {K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    IsIso ((verdierDualDoubleDual Λ (𝟙 S)).app K) :=
  isIso_verdierDualDoubleDual_app_of_isDualizable (dualizingComplexIdIso Λ S).symm
    isInvertible_unit hK

/-- Blueprint `lemma-perfect-complexes-geometric-point--8`, geometric form: on a nonempty noetherian
scheme `S` with a single point (such as the spectrum of a field) and for a finite ring `Λ`, the
double-dual map `K ⟶ 𝔻_S 𝔻_S K` relative to `𝟙_S` is an isomorphism for every `K` in
`Dctf(S, Λ)`: such a `K` is perfect, and derived evaluation into the double dual is an
isomorphism for perfect complexes. -/
theorem isIso_verdierDualDoubleDual_app_id_of_subsingleton (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {S : Scheme.{u}} [IsNoetherian S] [Subsingleton S]
    {K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) S K) :
    IsIso ((verdierDualDoubleDual Λ (𝟙 S)).app K) :=
  isIso_verdierDualDoubleDual_app_id_of_isDualizable S
    (isDualizable_of_constructibleFiniteTor_of_subsingleton Λ hK)

end Etale

end AlgebraicGeometry

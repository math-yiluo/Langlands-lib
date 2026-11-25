/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation

/-!
# General Verdier biduality at a finite stage

For `X` separated of finite type over a field `k` and a finite coefficient ring `Λ` whose
exponent is invertible on `k`, the Verdier dual `𝔻_X = RHom(-, ω_X)` carries `Dctf(X, Λ)` into
itself, with the Tor interval `[a, b]` going to `[-b - 2d, -a]` when `dim X ≤ d`
(`lemma-verdier-duality-preserves-constructibility--1`), and, for `k` algebraically closed, the
double-dual map `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism, so that `𝔻_X` is an anti-equivalence of
`Dctf(X, Λ)` (`sk-prop-sf-biduality-general`, `theorem-verdier-biduality--1`,
`theorem-verdier-biduality--1`).

## Implementation notes

The blueprint works over `k = 𝔽̄_q`. Its proof of preservation uses a stratification by smooth
strata, available over a perfect field, and its proof of biduality is an induction over
algebraically closed fields through geometric generic fibres. The statements below therefore
assume `k` perfect, respectively algebraically closed. The proofs are
`AlgebraicGeometry.Etale.constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField`
and `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_isAlgClosed`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]

/-- Blueprint `lemma-verdier-duality-preserves-constructibility--1`: Constructible preservation
before biduality (first half; the subsection `theorem-f-shriek-finite-coefficients`).

For `X` separated of finite type over a perfect field `k` and a finite coefficient ring `Λ`
whose exponent is invertible on `k`, the Verdier dual `𝔻_X = RHom(-, ω_X)` carries `Dctf(X, Λ)`
into itself. The Tor-amplitude bound of the same blueprint lemma is
`AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual`. This is the preservation half of the
general Verdier biduality `lemma-verdier-duality-preserves-constructibility--1`, whose blueprint
proof cites it. -/
theorem constructibleFiniteTor_verdierDual [PerfectField k]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      ((verdierDual Λ a).obj (op K)) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le a
  obtain ⟨hKbc, c, e, hKt⟩ := hK
  exact (constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField Λ a d hd c e
    hKbc hKt).1

/-- Blueprint `theorem-verdier-biduality--1`: General Verdier biduality.

For `X` separated of finite type over an algebraically closed field `k` and a finite
coefficient ring `Λ` whose exponent is invertible on `k`, the double-dual morphism
`δ_K : K ⟶ 𝔻_X 𝔻_X K` (`AlgebraicGeometry.Etale.verdierDualDoubleDual`) is an isomorphism for
every `K` in `Dctf(X, Λ)`. This is the finite-stage étale biduality
`theorem-verdier-biduality--1`
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_isAlgClosed`). -/
theorem isIso_verdierDualDoubleDual_app [IsAlgClosed k]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((verdierDualDoubleDual Λ a).app K) :=
  isIso_verdierDualDoubleDual_app_of_isAlgClosed Λ a hK

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality.

For `X` separated of finite type over an algebraically closed field `k` and a finite
coefficient ring `Λ` whose exponent is invertible on `k`, the Verdier dual is a contravariant
anti-equivalence of `Dctf(X, Λ)`: the double-dual morphism `K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for
every object `K` of `Dctf(X, Λ)` (`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`). -/
theorem nonempty_iso_verdierDual_verdierDual [IsAlgClosed k]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty (K ≅ (verdierDual Λ a).obj
      (op ((verdierDual Λ a).obj (op K)))) :=
  have := isIso_verdierDualDoubleDual_app Λ a hK
  ⟨asIso ((verdierDualDoubleDual Λ a).app K)⟩

/-- Blueprint `theorem-verdier-biduality--6`: General Verdier biduality.

For `X` separated of finite type over an algebraically closed field `k` and a finite
coefficient ring `Λ` whose exponent is invertible on `k`, the Verdier dual
`𝔻_X = RHom(-, ω_X)` restricts to a contravariant anti-equivalence
`Dctf(X, Λ)ᵒᵖ ≌ Dctf(X, Λ)`, with quasi-inverse `𝔻_X` itself: `𝔻_X` preserves `Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`) and the unit and the counit are
the double-dual isomorphisms `δ_K : K ≅ 𝔻_X 𝔻_X K`
(`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app`). -/
noncomputable def verdierDualEquivalence [IsAlgClosed k] :
    (DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X)ᵒᵖ ≌
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).liftDualEquivalence
    (verdierDual Λ a) (fun _ hK ↦ constructibleFiniteTor_verdierDual Λ a hK)
    (verdierDualDoubleDual Λ a)
    (fun _ hK ↦ isIso_verdierDualDoubleDual_app Λ a hK)

/-- Blueprint `lemma-verdier-duality-preserves-constructibility--1`: Verdier duality preserves
`Dctf`.

Let `X` be separated of finite type over a perfect field `k`, `ω_X = Ra_X^! Λ` and
`𝔻_X = RHom(-, ω_X)`. Then `𝔻_X` carries `Dctf(X, Λ)` into itself, and more precisely, if
`dim X ≤ d` and `K ∈ Dctf(X, Λ)` has Tor amplitude in `[a, b]`, then `𝔻_X K` has Tor amplitude
in `[-b - 2d, -a]`. The bound is independent of the exponent of `Λ`. The first half is
`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`. -/
theorem torAmplitudeIn_verdierDual [PerfectField k] (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * (d : ℤ)) (-a)
      ((verdierDual Λ aX).obj (op K)) :=
  (constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField Λ aX d hd a b hK
    hKt).2

end Etale

end AlgebraicGeometry

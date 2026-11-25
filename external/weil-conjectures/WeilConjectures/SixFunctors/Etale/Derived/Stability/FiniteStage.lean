/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.DualityPullback
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix

/-!
# The Tor interval of the exceptional inverse image on `Dctf`

Let `k` be an algebraically closed field, `Λ` a finite ring whose exponent is invertible on `k`
(the finite stage `A = A_{E,n}`), and let `f : X ⟶ Y` be a morphism of separated finite-type
`k`-schemes over `k`. This file proves the Tor interval of clause (v) of
`proposition-six-operations-dctf`: `Rf^!` sends `Dctf(Y, Λ)` objects of Tor amplitude `[a, b]` to
Tor amplitude `[a - 2 dim X, b + 2 dim Y]`.

## Main statements

- `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedUpperShriek_of_verdierDual`
  (`proposition-six-operations-dctf` (v)): the Tor interval `[a - 2 dim X, b + 2 dim Y]` of
  `Rf^! K`.

The isomorphism `Rf^! K ≅ 𝔻_X Lf^* 𝔻_Y K` it is derived from is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar`,
and the bundled theorem is `AlgebraicGeometry.Etale.constructibleFiniteTor_stability`, both in
`WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]

/-- Blueprint `proposition-six-operations-dctf`, clause (v), the Tor interval: if `dim X ≤ d_X`,
`dim Y ≤ d_Y` and `K ∈ Dctf(Y, Λ)` has Tor amplitude in `[a, b]`, then `Rf^! K` has Tor
amplitude in `[a - 2 d_X, b + 2 d_Y]`.

Indeed `Rf^! K ≅ 𝔻_X Lf^* 𝔻_Y K`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar`);
the duality bound
(`lemma-verdier-duality-preserves-constructibility--1`) on `Y` gives `𝔻_Y K` the interval
`[-b - 2 d_Y, -a]`, pullback preserves it, and the duality bound on `X` gives
`[a - 2 d_X, b + 2 d_Y]`. -/
theorem torAmplitudeIn_rightDerivedUpperShriek_of_verdierDual (f : X ⟶ Y) (hf : f ≫ aY = aX)
    [HasCompactification f] (dX dY : ℕ) (hdX : topologicalKrullDim X ≤ (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y ≤ (dY : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K)
    (hKt : torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
      ((R(f)^![Λ]).obj K) := by
  obtain ⟨e⟩ :=
    nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f hf hK
  have hD := constructibleFiniteTor_verdierDual Λ aY hK
  have hDt := torAmplitudeIn_verdierDual Λ aY dY hdY a b hK.1 hKt
  have hP := constructibleFiniteTor_leftDerivedUpperStar _ f hD
  have hPt := torAmplitudeIn_leftDerivedUpperStar _ f _ _ hDt
  have h := torAmplitudeIn_verdierDual Λ aX dX hdX _ _ hP.1 hPt
  refine (torAmplitudeIn (ModuleCat.{u + 1} Λ) X _ _).prop_of_iso e.symm ?_
  convert h using 2 <;> ring

end Etale

end AlgebraicGeometry

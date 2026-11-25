/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual

/-!
# The dualizing complex of the identity

For a coefficient category `A` (for instance `ModuleCat Λ`) and a scheme `S`, the compactly
supported direct image along the identity `𝟙 S` is the identity functor, hence so is its right
adjoint, the exceptional inverse image
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`). Consequently the dualizing complex of
`𝟙 S` is the unit `Λ_S` (`AlgebraicGeometry.Etale.dualizingComplexIdIso`), and the Verdier
dual `𝔻_S = RHom(-, ω_S)` relative to `𝟙 S` is the coefficient dual `(-)^∨ = RHom(-, Λ_S)`.
For `S = s` the geometric point this is blueprint `prose-10-04`; the proof
does not use anything about `S`.

## Main definitions

- `AlgebraicGeometry.Etale.verdierDualIdIso` (`prose-10-04`):
  `𝔻_S ≅ (-)^∨`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (S : Scheme.{u})

/-- Blueprint `prose-10-04`: Dualizing complex of the point.

The exceptional inverse image of the identity is the identity, so `ω_S = R(𝟙 S)^! Λ_S ≅ Λ_S`
(`AlgebraicGeometry.Etale.dualizingComplexIdIso`), and the Verdier dual relative to the identity
of `S` is the coefficient dual: `𝔻_S C = RHom(C, ω_S) ≅ RHom(C, Λ_S) = C^∨`, naturally in `C`. -/
noncomputable def verdierDualIdIso : verdierDual Λ (𝟙 S) ≅ DerivedCategory.coefficientDual
    (ModuleCat.{u + 1} Λ) S :=
  (RHom(S)[ModuleCat.{u + 1} Λ]).flip.mapIso (dualizingComplexIdIso Λ S)

end Etale

end AlgebraicGeometry

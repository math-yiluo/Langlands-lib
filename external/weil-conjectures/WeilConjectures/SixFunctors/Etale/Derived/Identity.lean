/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# The six functors along the identity

The derived lower shriek and the exceptional inverse image along the identity of a scheme `S`
are the identity functors, `R(𝟙_S)_! ≅ 𝟭` and `R(𝟙_S)^! ≅ 𝟭`, and the dualizing complex of the
identity is the unit (blueprint `theorem-global-verdier-duality`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`: `R(𝟙_S)_! ≅ 𝟭`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`: `R(𝟙_S)^! ≅ 𝟭`.
- `AlgebraicGeometry.Etale.dualizingComplexIdIso`: `ω_S ≅ Λ_S` for the identity of `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

universe u'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Point

variable (S : Scheme.{u})

/-- Blueprint `theorem-global-verdier-duality` (the dualizing complex of the base): the derived
lower shriek along the identity of `S` is the identity, `R(𝟙_S)_! ≅ 𝟭`. The identity is proper, so
`R(𝟙_S)_!` is `R(𝟙_S)_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), and `(𝟙_S)_* ≅ 𝟭`. -/
noncomputable def rightDerivedLowerShriekIdIso : R(𝟙 S)_![A] ≅ 𝟭 _ :=
  rightDerivedLowerShriekIsoRightDerivedLowerStar A (𝟙 S) ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarId A S) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The derived lower shriek along the identity of `S` is a left adjoint, being isomorphic to
the identity (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`). -/
instance isLeftAdjoint_rightDerivedLowerShriek_id : (R(𝟙 S)_![A]).IsLeftAdjoint :=
  ⟨_, ⟨Adjunction.id.ofNatIsoLeft (rightDerivedLowerShriekIdIso A S).symm⟩⟩

/-- Blueprint `theorem-global-verdier-duality` (the dualizing complex of the base): the exceptional
inverse image along the identity of `S` is the identity, `R(𝟙_S)^! ≅ 𝟭`, being right adjoint to
`R(𝟙_S)_! ≅ 𝟭`. -/
noncomputable def rightDerivedUpperShriekIdIso : R(𝟙 S)^![Λ] ≅ 𝟭 _ :=
  (rightDerivedUpperShriekAdjunction Λ (𝟙 S)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) S).symm)

/-- Blueprint `theorem-global-verdier-duality`: for the structure morphism `a_s = 𝟙_s` of the base,
the dualizing complex is the unit, `ω_s = Ra_s^! Λ ≅ Λ_s`. -/
noncomputable def dualizingComplexIdIso : dualizingComplex Λ (𝟙 S) ≅ 𝟙_ _ :=
  (rightDerivedUpperShriekIdIso Λ S).app _

end Point

end General

end Etale

end AlgebraicGeometry

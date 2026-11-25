/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnComponentBdcOfEq

/-!

# The exchange `ν_X` of a separated `X` on pushforwards

`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq` for the compactification
`X ⊂ X̄` of `a_X` and `ν_X = pointCompactSupportExchangeOfSeparated` (by `rfl`):
`pointCompactSupportExchangeOfSeparated_app_lowerStar`, and its instance for the thickened point
`B` of a fixed locus, `pointCompactSupportExchangeOfSeparated_app_lowerStar_component`.

The ambient hypothesis `hC` of these identities is proved in `PointExchangeOnComponentBdc`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Separated

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

instance isProper_compactificationOverField_overObj :
    IsProper (compactificationOverField (toPoint X)).overObj.hom :=
  have := (compactificationOverField (toPoint X)).isProper
  inferInstanceAs (IsProper (_ ≫ 𝟙 _))

variable (x : RationalPoint X) (k' : Type u) [Field k'] [Algebra k k'] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {B : Over (Spec (.of k))} [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom]

/-- **The exchange `ν_X` of a separated `X` on pushforwards from `B`**:
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq` for the compactification
`X ⊂ X̄` of `a_X` and `ν = pointCompactSupportExchangeOfSeparated` (`rfl`). -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar {B' : Scheme.{u}}
    {MB : NearbyCyclesModel B.left B'} {g : B ⟶ X}
    {g' : B' ⟶ (deformationSpecialFibre X x.left.ker k').left}
    (φg : MB.Hom (deformationModel X x.left.ker k') g.left g')
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq x
      (compactificationOverField (toPoint X)).overI k' φg
      (pointCompactSupportExchangeOfSeparated x k') rfl N) :=
  pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq x _ k' φg _ rfl N

/-- **The exchange `ν_X` of a separated `X` on pushforwards from a thickened point `B`**
(`b ≫ g = x`): `pointCompactSupportExchangeOfSeparated_app_lowerStar` for
`pointComponentModelHom`. -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar_component {b : RationalPoint B}
    (g : B ⟶ X) (hbg : b ≫ g = x) (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (pointCompactSupportExchangeOfSeparated_app_lowerStar x k'
      (pointComponentModelHom k' g hbg) N) :=
  pointCompactSupportExchangeOfSeparated_app_lowerStar x k' _ N

end Separated

end AlgebraicGeometry.ProEtale.CondensedRing

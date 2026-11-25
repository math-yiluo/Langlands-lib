/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.TateTwist.ProEtale

/-!
# The derived pullback of `ℚ̄_ℓ(0)`

For an arbitrary morphism of schemes `f : X ⟶ Y`, `Lf^* ℚ̄_ℓ,Y(0) ≅ ℚ̄_ℓ,X(0)`, both being the
tensor units placed in degree `0`
(`AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTateTwistDerivedZeroIso`). Unlike
`AlgebraicGeometry.ProEtale.upperStarTateTwistDerivedIso`, this needs no field below `Y`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The derived pullback of `ℚ̄_ℓ(0)`**: `Lf^* ℚ̄_ℓ,Y(0) ≅ ℚ̄_ℓ,X(0)`, both being the tensor units
placed in degree `0`. -/
noncomputable def leftDerivedUpperStarTateTwistDerivedZeroIso :
    L((f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj (tateTwistDerived Y ℓ 0) ≅
      tateTwistDerived X ℓ 0 :=
  leftDerivedUpperStarSingleIso _ f _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso _).symm

end AlgebraicGeometry.ProEtale.CondensedRing

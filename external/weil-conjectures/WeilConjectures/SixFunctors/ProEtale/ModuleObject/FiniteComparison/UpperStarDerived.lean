/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar

/-!

# The derived comparison of the two finite-coefficient models commutes with pullback

For a finite discrete commutative ring `T` and a morphism of schemes `f : X ⟶ Y`, the derived
comparison `ProEtale.finiteCoefficientDerivedEquivalence` between module objects over the
condensed coefficient ring `T̲` and pro-étale sheaves of `T`-modules commutes with the derived
pullbacks (`ProEtale.leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso`). All functors
involved are exact, so this is induced by the underived
`ProEtale.upperStarFiniteCoefficientModEquivalenceIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Type) [TopologicalSpace T] [CommRing T]
  [IsTopologicalRing T] [DiscreteTopology T] [Finite T]

/-- **The derived comparison of the two finite-coefficient models commutes with the derived
pullback**: `Lf^* ⋙ D(Φ_X) ≅ D(Φ_Y) ⋙ Lf^*`, induced by
`upperStarFiniteCoefficientModEquivalenceIso`, all functors involved being exact. -/
noncomputable def leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso :
    L(CondensedRing.upperStar (Profinite.continuousMapRingObj T) f) ⋙
        (finiteCoefficientDerivedEquivalence X T).functor ≅
      (finiteCoefficientDerivedEquivalence Y T).functor ⋙
        L(ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f) :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.continuousMapRingObj T) f) _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _) ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarFiniteCoefficientModEquivalenceIso f T) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).symm

end AlgebraicGeometry.ProEtale

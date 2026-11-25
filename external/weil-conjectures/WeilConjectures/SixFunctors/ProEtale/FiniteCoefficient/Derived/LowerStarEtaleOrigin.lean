/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-!

# Direct images preserve bounded below complexes of étale origin

For a quasi-compact quasi-separated morphism `f`, the pro-étale derived direct image `Rf_*` sends
bounded below complexes of étale origin `ν^* K'` to complexes of étale origin: `Rf_* ν^* K'` is
`ν^* Rf_* K'` (Bhatt–Scholze, Lemma 5.2.6;
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso`), and the étale
direct image preserves bounded below complexes
(`AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin_rightDerivedLowerStar_obj`). The
étale direct image is computed by its restriction to bounded below complexes
(`CategoryTheory.Functor.rightDerivedFunctorPlusCompatibility`).

-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- For `f` quasi-compact and quasi-separated and a bounded below complex `K'` of étale sheaves,
the pro-étale direct image of `ν^* K'` is `ν^* Rf_* K'`: the component at `K'` of the comparison
isomorphism `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'` (blueprint
`theorem-comparison-direct-images--1`). -/
noncomputable def rightDerivedLowerStarMapDerivedCategoryObjIso
    (K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hK' : _root_.DerivedCategory.TStructure.t.plus K') :
    (R(ProEtale.lowerStar A f)).obj (D(ν^*(X)[A]).obj K') ≅
      D(ν^*(Y)[A]).obj ((R(Etale.lowerStar A f)).obj K') :=
  ((rightDerivedLowerStarComparisonIso' f A).app ⟨K', hK'⟩).symm ≪≫
    D(ν^*(Y)[A]).mapIso ((Etale.lowerStar A f).rightDerivedFunctorPlusCompatibility.app ⟨K', hK'⟩)

namespace DerivedCategory

/-- The pro-étale derived direct image along a quasi-compact quasi-separated morphism preserves
bounded below complexes of étale origin. -/
lemma plusEtaleOrigin_rightDerivedLowerStar_obj
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hL : plusEtaleOrigin A X L) :
    plusEtaleOrigin A Y ((R((f)_*[A])).obj L) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hL
  refine ⟨(R(Etale.lowerStar A f)).obj K', ?_,
    ⟨(rightDerivedLowerStarMapDerivedCategoryObjIso A f K' hK').symm ≪≫
      (R((f)_*[A])).mapIso e⟩⟩
  exact _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.lowerStar A f).rightDerivedFunctorPlusCompatibility.app ⟨K', hK'⟩)
    ((R+(Etale.lowerStar A f)).obj ⟨K', hK'⟩).property

end DerivedCategory

end AlgebraicGeometry.ProEtale

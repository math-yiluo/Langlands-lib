/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar

/-!
# Pullbacks of complexes of étale origin

For a morphism of schemes `f : Y ⟶ X`, the derived pullback `Lf^*` of pro-étale sheaves sends
bounded below complexes of étale origin to bounded below complexes of étale origin
(`ProEtale.DerivedCategory.plusEtaleOrigin.leftDerivedUpperStar_obj`): pullback commutes with
`ν^*` (`ProEtale.comparisonUpperStarUpperStarIso`) and the étale pullback is exact.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X Y : Scheme.{u}}

/-- **Pullbacks of complexes of étale origin are of étale origin**: if `L` is bounded below of
étale origin on `X`, so is `Lf^* L` on `Y`. -/
lemma DerivedCategory.plusEtaleOrigin.leftDerivedUpperStar_obj (f : Y ⟶ X)
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hL : DerivedCategory.plusEtaleOrigin A X L) :
    DerivedCategory.plusEtaleOrigin A Y (L((f)^*[A]).obj L) := by
  obtain ⟨N, ⟨n, hN⟩, ⟨e⟩⟩ := hL
  have : N.IsGE n := hN
  have hN' : DerivedCategory.TStructure.t.plus (D(Etale.upperStar A f).obj N) :=
    ⟨n, (Etale.upperStar A f).isGE_mapDerivedCategory_obj N n⟩
  refine ObjectProperty.prop_of_iso _ ?_ (plusEtaleOrigin_mapDerivedCategory_obj hN')
  exact (Functor.mapDerivedCategoryCompIso _ _).app N ≪≫
    (Functor.mapDerivedCategoryNatIso (comparisonUpperStarUpperStarIso A f).symm).app N ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm.app N ≪≫
    (D((f)^*[A])).mapIso e ≪≫ (leftDerivedUpperStarIsoMapDerivedCategory A f).symm.app L

end AlgebraicGeometry.ProEtale

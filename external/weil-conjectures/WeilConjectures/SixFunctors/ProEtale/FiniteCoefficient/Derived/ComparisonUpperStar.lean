/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!

# `Rν_*` commutes with pullback on complexes of étale origin

For a morphism of schemes `g : Z ⟶ Y`, the comparison `ν^*` commutes with the pullbacks,
`g^*_{proét} ∘ ν_Y^* ≅ ν_Z^* ∘ g^*_{ét}` (`ProEtale.comparisonUpperStarUpperStarIso`), hence so do
the induced functors on derived categories (`ProEtale.derivedComparisonUpperStarUpperStarIso`).
Its mate under the adjunctions `D(ν^*) ⊣ Rν_*` is a base change morphism
```
Lg^*_{ét} (Rν_{Y,*} K) ⟶ Rν_{Z,*} (Lg^*_{proét} K)
```
(`ProEtale.rightDerivedComparisonBaseChange`). It is an isomorphism when `K` is bounded below of
étale origin (`ProEtale.isIso_rightDerivedComparisonBaseChange_app`): for `K = ν^* K'` with `K'`
bounded below, both sides are `Lg^* K'`, by the full faithfulness of `ν^*` on `D⁺`
(`ProEtale.isIso_derivedComparisonAdjunction_unit_app`).

-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- **`D(ν^*)` commutes with the derived pullbacks**: `D(ν_Y^*) ⋙ Lg^*_{proét} ≅
Lg^*_{ét} ⋙ D(ν_Z^*)`, induced by `ProEtale.comparisonUpperStarUpperStarIso`, all four functors
being induced by exact functors. -/
noncomputable def derivedComparisonUpperStarUpperStarIso :
    D(ν^*(Y)[A]) ⋙ L(ProEtale.upperStar A g) ≅
      L(Etale.upperStar A g) ⋙ D(ν^*(Z)[A]) :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (comparisonUpperStarUpperStarIso A g) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g).symm _

/-- **The base change morphism for `Rν_*` and the pullbacks**,
`Lg^*_{ét} ∘ Rν_{Y,*} ⟶ Rν_{Z,*} ∘ Lg^*_{proét}`: the mate of the inverse of
`ProEtale.derivedComparisonUpperStarUpperStarIso` under the adjunctions `D(ν^*) ⊣ Rν_*`. -/
noncomputable def rightDerivedComparisonBaseChange :
    R(ν_*(Y)[A]) ⋙ L(Etale.upperStar A g) ⟶ L(ProEtale.upperStar A g) ⋙ R(ν_*(Z)[A]) :=
  mateEquiv (derivedComparisonAdjunction A Y) (derivedComparisonAdjunction A Z)
    (derivedComparisonUpperStarUpperStarIso A g).inv

/-- **`Rν_*` commutes with pullback on complexes of étale origin**: the base change morphism
`Lg^* Rν_{Y,*} K ⟶ Rν_{Z,*} Lg^* K` is an isomorphism when `K` is bounded below of étale origin.
For `K = ν^* K'` with `K'` bounded below, the units `K' ⟶ Rν_* ν^* K'` and
`g^* K' ⟶ Rν_* ν^* g^* K'` are isomorphisms (`isIso_derivedComparisonAdjunction_unit_app`), and
the base change morphism is identified with their composite. -/
theorem isIso_rightDerivedComparisonBaseChange_app
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (hK : DerivedCategory.plusEtaleOrigin A Y K) :
    IsIso ((rightDerivedComparisonBaseChange A g).app K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  have := isIso_derivedComparisonAdjunction_unit_app A Y K' hK'
  have hGK' : DerivedCategory.TStructure.t.plus ((L(Etale.upperStar A g)).obj K') := by
    obtain ⟨n, hn⟩ := hK'
    exact DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory A g).app K').symm
      ⟨n, (Etale.upperStar A g).isGE_mapDerivedCategory_obj K' n⟩
  have := isIso_derivedComparisonAdjunction_unit_app A Z _ hGK'
  have : IsIso ((L(Etale.upperStar A g)).map ((derivedComparisonAdjunction A Y).unit.app K') ≫
      (rightDerivedComparisonBaseChange A g).app ((D(ν^*(Y)[A])).obj K')) := by
    rw [rightDerivedComparisonBaseChange, unit_mateEquiv]
    dsimp only [Functor.id_obj]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((L(Etale.upperStar A g)).map ((derivedComparisonAdjunction A Y).unit.app K')) _

end AlgebraicGeometry.ProEtale

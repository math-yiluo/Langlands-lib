/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStarCanonical
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek

/-!
# The compact-support comparison between étale and pro-étale sheaves

Let `f : X ⟶ Y` be a morphism admitting a compactification `X ⟶[i] Z ⟶[g] Y`. The derived lower
shriek functors on the étale and pro-étale sites are both `Rg_* ∘ i_!`, and the comparison
functor `ν^*` intertwines them on bounded below complexes:
`Rf_!^{proét} ∘ ν_X^* ≅ ν_Y^* ∘ Rf_!^{ét}`. This is the compact-support comparison used in the
proof of blueprint `theorem-existence-exceptional-inverse-image` (c), obtained from blueprint
`theorem-bounded-below-cohomology-comparison` applied to the extension by zero and to the proper
part.

## Main definitions

- `AlgebraicGeometry.ProEtale.comparisonLowerStarOpenImmersionRestrictionIso`: the restrictions
  along an open immersion commute with `ν_*`.
- `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparisonUpperStarIso`: the extensions
  by zero along an open immersion commute with `ν^*`, `ν_X^* ∘ j^{ét}_! ≅ j^{proét}_! ∘ ν_U^*`,
  the conjugate of the previous isomorphism.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso`: for a quasi-compact
  quasi-separated `g`, `Rg_*^{proét} ∘ ν^* ≅ ν^* ∘ Rg_*^{ét}` on bounded below complexes.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekComparisonIso`: the compact-support
  comparison `Rf_!^{proét} ∘ ν_X^* ≅ ν_Y^* ∘ Rf_!^{ét}` on bounded below complexes.

## Implementation notes

The comparison of the direct images along the proper part is the canonical isomorphism
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso` of blueprint
`theorem-bounded-below-cohomology-comparison`, the base change morphism of right derived functors
induced by the underived base change morphism `ν^* g_* ⟶ g_* ν^*`. All comparisons of this file are
therefore canonical composites of explicit natural isomorphisms; none involves a choice.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The inclusions of the small étale sites into the small pro-étale sites commute with the
localization functors along an open immersion `j : U ⟶ X`: both composites send an étale
`T ⟶ U` to the weakly étale `T ⟶ U ⟶ X`. -/
def toProEtCompOverMapIso :
    MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j) ⋙ toProEt X ≅
      toProEt U ⋙ MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) :=
  Iso.refl _

/-- The restriction along an open immersion `j : U ⟶ X` commutes with the comparison
restriction `ν_*`: `j^{ét,*} ∘ ν_{X,*} ≅ ν_{U,*} ∘ j^{proét,*}`, both being restriction along
the two equal composites of `AlgebraicGeometry.ProEtale.toProEtCompOverMapIso`. -/
noncomputable def comparisonLowerStarOpenImmersionRestrictionIso :
    ν_*(X)[A] ⋙ Etale.openImmersionRestriction A j ≅
      ProEtale.openImmersionRestriction A j ⋙ ν_*(U)[A] :=
  Iso.refl _

/-- Blueprint `proposition-comparison-immersions--1`: Comparison of extension by zero with
the site morphism.

The extension by zero along an open immersion `j : U ⟶ X` commutes with the comparison
`ν^*`: `ν_X^* ∘ j^{ét}_! ≅ j^{proét}_! ∘ ν_U^*`, naturally in the étale sheaf. Both sides are
left adjoint to the two sides of
`AlgebraicGeometry.ProEtale.comparisonLowerStarOpenImmersionRestrictionIso`, which are equal
(both are restriction of sections along `U ⟶ X`), and the isomorphism is its conjugate. -/
noncomputable def openImmersionLowerShriekComparisonUpperStarIso :
    Etale.openImmersionLowerShriek A j ⋙ ν^*(X)[A] ≅
      ν^*(U)[A] ⋙ ProEtale.openImmersionLowerShriek A j :=
  ((conjugateIsoEquiv
    ((Etale.openImmersionLowerShriekAdjunction A j).comp (comparisonAdjunction A X))
    ((comparisonAdjunction A U).comp (ProEtale.openImmersionLowerShriekAdjunction A j))).symm
      (comparisonLowerStarOpenImmersionRestrictionIso A j)).symm

end OpenImmersion

section LowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g]

/-- Blueprint `theorem-bounded-below-cohomology-comparison`, the comparison direct image, on the
unbounded derived categories restricted to bounded below complexes: for a quasi-compact
quasi-separated `g`, `Rg_*^{proét} ∘ ν_Z^* ≅ ν_Y^* ∘ Rg_*^{ét}` as functors `D⁺(Z_ét) ⥤ D(Y_proét)`.
It is the inverse of the canonical isomorphism
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso`, transported
along the inclusions of the bounded below derived categories. -/
noncomputable def rightDerivedLowerStarComparisonIso :
    DerivedCategory.Plus.ι ⋙ D(ν^*(Z)[A]) ⋙ R(ProEtale.lowerStar A g) ≅
      DerivedCategory.Plus.ι ⋙ R(Etale.lowerStar A g) ⋙ D(ν^*(Y)[A]) :=
  Functor.isoWhiskerRight (ν^*(Z)[A]).mapDerivedCategoryPlusCompatibility.symm _ ≪≫
    Functor.isoWhiskerLeft D+(ν^*(Z)[A])
      (ProEtale.lowerStar A g).rightDerivedFunctorPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarComparisonPlusIso g A).symm
      DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerLeft R+(Etale.lowerStar A g)
      (ν^*(Y)[A]).mapDerivedCategoryPlusCompatibility ≪≫
    Functor.isoWhiskerRight (Etale.lowerStar A g).rightDerivedFunctorPlusCompatibility _

end LowerStar

section LowerShriek

variable {X Y : Scheme.{u}}

/-- The compact-support comparison for a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
`Rf_!^{proét}(c) ∘ ν_X^* ≅ ν_Y^* ∘ Rf_!^{ét}(c)` as functors `D⁺(X_ét) ⥤ D(Y_proét)`. It is
`AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparisonUpperStarIso` for the extension by
zero `i_!`, followed by `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso` for the
proper `g`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationComparisonIso {f : X ⟶ Y}
    (c : Compactification f) :
    DerivedCategory.Plus.ι ⋙ D(ν^*(X)[A]) ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification A c ≅
      DerivedCategory.Plus.ι ⋙ Etale.rightDerivedLowerShriekOfCompactification A c ⋙
        D(ν^*(Y)[A]) :=
  have := c.isProper
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryCompIso _ _ ≪≫
            Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComparisonUpperStarIso A c.i).symm ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm) R(ProEtale.lowerStar A c.g) ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlusCompatibility.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+(Etale.openImmersionLowerShriek A c.i)
      (rightDerivedLowerStarComparisonIso A c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlusCompatibility _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι (Functor.associator _ _ _).symm

/-- The compact-support comparison `Rf_!^{proét} ∘ ν_X^* ≅ ν_Y^* ∘ Rf_!^{ét}` as functors
`D⁺(X_ét) ⥤ D(Y_proét)`, for the chosen compactification of `f`
(proof of blueprint `theorem-existence-exceptional-inverse-image` (c)). -/
noncomputable def rightDerivedLowerShriekComparisonIso (f : X ⟶ Y) [HasCompactification f] :
    DerivedCategory.Plus.ι ⋙ D(ν^*(X)[A]) ⋙ ProEtale.rightDerivedLowerShriek A f ≅
      DerivedCategory.Plus.ι ⋙ Etale.rightDerivedLowerShriek A f ⋙ D(ν^*(Y)[A]) :=
  rightDerivedLowerShriekOfCompactificationComparisonIso A
    (HasCompactification.compactification f)

end LowerShriek

end AlgebraicGeometry.ProEtale

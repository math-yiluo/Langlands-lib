/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The comparison pullback `ν^*` commutes with pullbacks

For a morphism of schemes `g : Z ⟶ Y`, the restrictions `ν_*` from pro-étale to étale sheaves
commute with the pushforwards: `ν_{Y,*} ∘ g_*^{proét} = g_*^{ét} ∘ ν_{Z,*}`, both being
restriction of sections along the base change `V ↦ V ×_Y Z` of étale `Y`-schemes. Hence their
left adjoints commute: `g^*_{proét} ∘ ν_Y^* ≅ ν_Z^* ∘ g^*_{ét}`
(`AlgebraicGeometry.ProEtale.comparisonUpperStarUpperStarIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The restriction `ν_*` commutes with the pushforwards: both composites are restriction of
sections along the base change of étale `Y`-schemes. -/
noncomputable def lowerStarComparisonLowerStarIso :
    ProEtale.lowerStar A g ⋙ comparisonLowerStar A Y ≅
      comparisonLowerStar A Z ⋙ Etale.lowerStar A g :=
  Iso.refl _

/-- **`ν^*` commutes with pullbacks**: `g^*_{proét} ∘ ν_Y^* ≅ ν_Z^* ∘ g^*_{ét}`, the conjugate of
`AlgebraicGeometry.ProEtale.lowerStarComparisonLowerStarIso`. -/
noncomputable def comparisonUpperStarUpperStarIso :
    comparisonUpperStar A Y ⋙ ProEtale.upperStar A g ≅
      Etale.upperStar A g ⋙ comparisonUpperStar A Z :=
  (conjugateIsoEquiv ((Etale.upperStarLowerStarAdjunction A g).comp (comparisonAdjunction A Z))
    ((comparisonAdjunction A Y).comp (ProEtale.upperStarLowerStarAdjunction A g))).symm
      (lowerStarComparisonLowerStarIso A g).symm

end AlgebraicGeometry.ProEtale

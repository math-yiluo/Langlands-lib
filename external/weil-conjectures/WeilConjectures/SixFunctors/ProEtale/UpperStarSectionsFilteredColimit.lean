/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Sections of pullbacks of filtered colimits of pro-étale sheaves

Let `c` be a colimit cocone of a filtered diagram `F : K ⥤ Sh(X_proét, Ab)`, `p : Y ⟶ X` a
morphism of schemes and `W` an object of the pro-étale site of `Y` with quasi-compact
quasi-separated underlying space. Then `(p^* c.pt)(W) = colim_k (p^* F_k)(W)`
(`AlgebraicGeometry.ProEtale.isColimitUpperStarSections`): `p^*` is a left adjoint, so it
preserves colimits, and sections over `W` commute with filtered colimits
(`AlgebraicGeometry.Scheme.ProEt.isColimitSectionsOfIsColimit`).

For weakly étale `p` the pullback is restriction along the localisation functor
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), whose sections over `W` are
those over `W → Y → X`; the same statement then holds for the restriction
(`AlgebraicGeometry.ProEtale.isColimitLocalizationRestrictionSections`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme Scheme.ProEt

variable {X Y : Scheme.{u}} {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
  {F : K ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} {c : Cocone F}

/-- **Sections of the pullback of a filtered colimit** over a quasi-compact quasi-separated
object: `(p^* c.pt)(W) = colim_k (p^* F_k)(W)`. -/
noncomputable def isColimitUpperStarSections (p : Y ⟶ X) (hc : IsColimit c) (W : Y.ProEt)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    IsColimit ((abSectionsFunctor W).mapCocone ((p)^*[AddCommGrpCat.{u + 1}].mapCocone c)) :=
  isColimitSectionsOfIsColimit (isColimitOfPreserves _ hc) W

/-- **Sections of the restriction of a filtered colimit along a weakly étale morphism** over a
quasi-compact quasi-separated object: `(c.pt|_Y)(W) = colim_k (F_k|_Y)(W)`. -/
noncomputable def isColimitLocalizationRestrictionSections (p : Y ⟶ X) (h : WeaklyEtale p)
    (hc : IsColimit c) (W : Y.ProEt) [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    IsColimit ((abSectionsFunctor W).mapCocone
      ((ProEtale.localizationRestriction AddCommGrpCat.{u + 1} p h).mapCocone c)) :=
  have : CompactSpace ((MorphismProperty.Over.map ⊤ h).obj W).left :=
    inferInstanceAs (CompactSpace W.left)
  have : QuasiSeparatedSpace ((MorphismProperty.Over.map ⊤ h).obj W).left :=
    inferInstanceAs (QuasiSeparatedSpace W.left)
  isColimitSectionsOfIsColimit hc ((MorphismProperty.Over.map ⊤ h).obj W)

end AlgebraicGeometry.ProEtale

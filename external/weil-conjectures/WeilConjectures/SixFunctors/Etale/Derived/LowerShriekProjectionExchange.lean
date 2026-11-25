/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The projection map commutes with the exchange map `Ex_!`

For torsion coefficients, the projection map `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)`
(`AlgebraicGeometry.Etale.projectionMap`) does not depend on the compactification: the
comparison isomorphisms `Rf_!(c) ≅ Rf_!(d)` intertwine the projection maps
(`Etale.projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso`).
Consequently the projection map commutes with the compactly supported base change map
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`)
and the tensor comparisons of the derived pullbacks
(`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

-- Give instance search the canonical larger-universe model of the small étale site.
local instance essentiallySmall_etale_projectionExchange (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- statements specialised here: otherwise the monoidal structures on sheaves and derived categories
-- found by instance search differ from the specialised ones, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Independence

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]

/-- The comparison isomorphisms `Rf_!(c) ≅ Rf_!(d)` intertwine the projection maps. -/
lemma projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
    (c d : Compactification f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((projectionMapOfCompactification _ c).app K).app L ≫
        (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom.app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) =
      ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekOfCompactificationIso Λ c d).hom.app K)).app L ≫
        ((projectionMapOfCompactification _ d).app K).app L := by
  have h₁ := projectionMapOfCompactification_comparison _ (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d) K L
  have h₂ := projectionMapOfCompactification_comparison _ (Compactification.infSnd c d)
    (Compactification.isPullback_infSnd c d) K L
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁]
  let e := asIso (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ)
    (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))
  have h₂' : ((projectionMapOfCompactification _ (c.inf d)).app K).app L ≫
      e.inv.app (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) =
      ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map (e.inv.app K)).app L ≫
        ((projectionMapOfCompactification _ d).app K).app L := by
    rw [← Iso.app_inv, Iso.comp_inv_eq, Iso.app_hom, Category.assoc]
    erw [h₂]
    rw [← NatTrans.comp_app_assoc, ← Functor.map_comp]
    erw [Iso.inv_hom_id_app]
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  exact congrArg (_ ≫ ·) h₂'

end Independence

section Exchange

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

-- The generic compatibility theorems specialised below braid étale sheaves through
-- `Etale.sheafBraidedCategory`; use it here as well so that the specialisations match them
-- syntactically rather than up to an expensive unfolding of the symmetric structure.
attribute [local instance 20000] Etale.sheafBraidedCategory

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : CommSq g' f' f g) (c : Compactification f) (c' : Compactification f') (q : c'.Z ⟶ c.Z)
  (hi : IsPullback g' c'.i c.i q) (hp : CommSq q c'.g c.g g)
  [HasCompactification f'] [QuasiCompact f']

/-- The exchange map `Lg^* Rf_!(c) ⟶ R(f')_! Lg'^*` for a compactification `c'` of the base change
lying over `c`: `rightDerivedLowerShriekOfCompactificationBaseChangeMap'` followed by the
comparison isomorphism `Rf'_!(c') ≅ R(f')_!`. For `c` the chosen compactification of `f` and
`c' = c.ofIsPullback sq` it is `rightDerivedLowerShriekBaseChangeMap`. -/
noncomputable def rightDerivedLowerShriekBaseChangeMap' :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ⟶
      L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')_![ModuleCat.{u + 1} Λ] :=
  rightDerivedLowerShriekOfCompactificationBaseChangeMap' _ c c' q hi hp ≫
    Functor.whiskerLeft _ (rightDerivedLowerShriekIso Λ c').hom

lemma rightDerivedLowerShriekBaseChangeMap_eq [HasCompactification f] (sq : IsPullback g' f' f g) :
    rightDerivedLowerShriekBaseChangeMap Λ sq =
      rightDerivedLowerShriekBaseChangeMap' Λ (HasCompactification.compactification f)
        ((HasCompactification.compactification f).ofIsPullback sq)
        (pullback.fst (HasCompactification.compactification f).g g)
        ((HasCompactification.compactification f).isPullback_i_ofIsPullback sq)
        (IsPullback.of_hasPullback (HasCompactification.compactification f).g g).toCommSq :=
  rfl

/-- The projection map commutes with the exchange map `rightDerivedLowerShriekBaseChangeMap'`. -/
theorem projectionMapOfCompactification_rightDerivedLowerShriekBaseChangeMap'
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map (((projectionMapOfCompactification _ c).app K).app L) ≫
        (rightDerivedLowerShriekBaseChangeMap' Λ c c' q hi hp).app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((leftDerivedUpperStarTensorComparison _ g').app K).app
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).obj (L((g')^*[ModuleCat.{u + 1} Λ]).obj K)).map
            (derivedSquareUpperStarIsoInvApp _ sq L)) =
      ((leftDerivedUpperStarTensorComparison _ g).app
          ((Rf_!(c)[ModuleCat.{u + 1} Λ]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekBaseChangeMap' Λ c c' q hi hp).app K)).app
            (L((g)^*[ModuleCat.{u + 1} Λ]).obj L) ≫
        ((projectionMap _ f').app (L((g')^*[ModuleCat.{u + 1} Λ]).obj K)).app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj L) := by
  have h := projectionMapOfCompactification_baseChange_comp' (ModuleCat.{u + 1} Λ) sq c c' q hi hp
    (HasCompactification.compactification f') (rightDerivedLowerShriekIso Λ c').hom
    (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso Λ c'
      (HasCompactification.compactification f')) K L
  exact h

/-- **The projection map commutes with the exchange map `Ex_!`**: for a cartesian square
`g' ≫ f = f' ≫ g`, the square
```
Lg^*(Rf_!K ⊗ᴸ L) ──Lg^* PF──▶ Lg^*Rf_!(K ⊗ᴸ Lf^*L) ──Ex_!──▶ Rf'_!Lg'^*(K ⊗ᴸ Lf^*L)
       │                                                          │
       ▼                                                          ▼
Lg^*Rf_!K ⊗ᴸ Lg^*L ──Ex_! ⊗ 1──▶ Rf'_!Lg'^*K ⊗ᴸ Lg^*L ──PF──▶ Rf'_!(Lg'^*K ⊗ᴸ Lf'^*Lg^*L)
```
commutes, where the vertical arrows are the tensor comparisons of the derived pullbacks, the
right one followed by `Lg'^*Lf^* ≅ Lf'^*Lg^*`. -/
theorem projectionMap_rightDerivedLowerShriekBaseChangeMap [HasCompactification f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map (((projectionMap _ f).app K).app L) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((leftDerivedUpperStarTensorComparison _ g').app K).app
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).obj (L((g')^*[ModuleCat.{u + 1} Λ]).obj K)).map
            (derivedSquareUpperStarIsoInvApp _ sq.toCommSq L)) =
      ((leftDerivedUpperStarTensorComparison _ g).app
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K)).app
            (L((g)^*[ModuleCat.{u + 1} Λ]).obj L) ≫
        ((projectionMap _ f').app (L((g')^*[ModuleCat.{u + 1} Λ]).obj K)).app
          (L((g)^*[ModuleCat.{u + 1} Λ]).obj L) := by
  exact projectionMapOfCompactification_rightDerivedLowerShriekBaseChangeMap' Λ sq.toCommSq
    (HasCompactification.compactification f)
    ((HasCompactification.compactification f).ofIsPullback sq)
    (pullback.fst (HasCompactification.compactification f).g g)
    ((HasCompactification.compactification f).isPullback_i_ofIsPullback sq)
    (IsPullback.of_hasPullback (HasCompactification.compactification f).g g).toCommSq K L

end Exchange

end Etale

end AlgebraicGeometry

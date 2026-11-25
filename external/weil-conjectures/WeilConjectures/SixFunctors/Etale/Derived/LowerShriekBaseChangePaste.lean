/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-!
# Pasting laws for the compactly supported base change map

For torsion coefficients `Λ`, the compactly supported base change map
`Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`)
is compatible with pasting cartesian squares, in both directions:

```
X'' --w'--> X' --v'--> X                X' --vX--> X
 |          |          |                |          |
f''   sq₂   f'   sq₁   f                f'   sqf   f
 ↓          ↓          ↓                ↓          ↓
Y'' --w---> Y' --v---> Y                Y' --vY--> Y
                                        |          |
                                        g'   sqg   g
                                        ↓          ↓
                                        Z' --vZ--> Z
```

- horizontally, `Ex_!` of the outer square is `Lw^*` of `Ex_!(sq₁)` followed by `Ex_!(sq₂)`, up
  to the composition isomorphisms `L(w ≫ v)^* ≅ Lw^* Lv^*` and `L(w' ≫ v')^* ≅ Lw'^* Lv'^*`
  (`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`);
- vertically, `Ex_!` of the outer square along `f ≫ g` is `Ex_!(sqg)` followed by `Rg'_!` of
  `Ex_!(sqf)`, up to the composition isomorphisms `Rf_! ⋙ Rg_! ≅ R(f ≫ g)_!` and
  `Rf'_! ⋙ Rg'_! ≅ R(f' ≫ g')_!` (`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`).

Both are transported from the pasting laws of the compact support formalism
(`AlgebraicGeometry.Etale.unboundedEtaleCompactSupportBaseChange_paste_horiz` and
`AlgebraicGeometry.Etale.unboundedEtaleCompactSupportBaseChange_paste_vert`), which are stated
for the derived pullbacks `D(g^*)` induced by the exact functors `g^*`, along the comparison
isomorphisms `Lg^* ≅ D(g^*)`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`).

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_horiz`: horizontal pasting.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap_paste_vert`: vertical pasting.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The comparison isomorphisms `Lg^* ≅ D(g^*)` intertwine the composition isomorphism
`L(g₁₂)^* ≅ Lg₂^* ⋙ Lg₁^*` with the composition isomorphism `D(g₁₂^*) ≅ D(g₂^*) ⋙ D(g₁^*)`
induced by `AlgebraicGeometry.Etale.upperStarComp`. -/
lemma leftDerivedUpperStarComp_hom_app_comp_isoMapDerivedCategory
    {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    (K : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A g₁).hom.app (L((g₂)^*[A]).obj K) ≫
          D((g₁)^*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A g₂).hom.app K) =
      (leftDerivedUpperStarIsoMapDerivedCategory A g₁₂).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp A g₁ g₂ g₁₂ hg) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app K := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

end Comparison

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- `Ex_!` at an object, in terms of its transport
`AlgebraicGeometry.Etale.unboundedEtaleCompactSupportBaseChange` along `Lg^* ≅ D(g^*)`. -/
private lemma rightDerivedLowerShriekBaseChangeMap_app_eq {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X} [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app K =
      (leftDerivedUpperStarIsoMapDerivedCategory _ g).hom.app
          (R(f)_![ModuleCat.{u + 1} Λ].obj K) ≫
        (unboundedEtaleCompactSupportBaseChange Λ sq).app K ≫
          R(f')_![ModuleCat.{u + 1} Λ].map
            ((leftDerivedUpperStarIsoMapDerivedCategory _ g').inv.app K) := by
  simp [unboundedEtaleCompactSupportBaseChange, ← Functor.map_comp]

/-- **Horizontal pasting of the compactly supported base change maps**: for two cartesian
squares `sq₁ : v' ≫ f = f' ≫ v` and `sq₂ : w' ≫ f' = f'' ≫ w` side by side, with outer
square `sq₃ : v₀' ≫ f = f'' ≫ v₀` where `v₀ = w ≫ v` and `v₀' = w' ≫ v'`, the exchange map
`Ex_!(sq₃)` is `Lw^*` of `Ex_!(sq₁)` followed by `Ex_!(sq₂)`, up to the composition
isomorphisms of the derived pullbacks:

```
L(v₀)^* Rf_! ≅ Lw^* Lv^* Rf_! ⟶ Lw^* Rf'_! Lv'^* ⟶ Rf''_! Lw'^* Lv'^* ≅ Rf''_! L(v₀')^*
```

(blueprint: `sk-def-sf-exchanges`) -/
theorem rightDerivedLowerShriekBaseChangeMap_paste_horiz
    {X X' X'' Y Y' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v₀ : Y'' ⟶ Y} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    {v₀' : X'' ⟶ X} [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w) (sq₃ : IsPullback v₀' f'' f v₀)
    (hv : v₀ = w ≫ v) (hv' : v₀' = w' ≫ v')
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComp _ w v v₀ hv).hom.app (R(f)_![ModuleCat.{u + 1} Λ].obj K) ≫
        L((w)^*[ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekBaseChangeMap Λ sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq₂).app
          (L((v')^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R(f'')_![ModuleCat.{u + 1} Λ].map
          ((leftDerivedUpperStarComp _ w' v' v₀' hv').inv.app K) =
      (rightDerivedLowerShriekBaseChangeMap Λ sq₃).app K := by
  subst hv hv'
  have hc := leftDerivedUpperStarComp_hom_app_comp_isoMapDerivedCategory _ w v (w ≫ v) rfl
    (R(f)_![ModuleCat.{u + 1} Λ].obj K)
  have hc' :=
    leftDerivedUpperStarComp_hom_app_comp_isoMapDerivedCategory _ w' v' (w' ≫ v') rfl K
  have h := congr_app (unboundedEtaleCompactSupportBaseChange_paste_horiz Λ sq₁ sq₂ sq₃) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at h
  rw [rightDerivedLowerShriekBaseChangeMap_app_eq sq₁,
    rightDerivedLowerShriekBaseChangeMap_app_eq sq₂,
    rightDerivedLowerShriekBaseChangeMap_app_eq sq₃, h]
  change _ = _ ≫ (unboundedEtaleUpperStarCompIso Λ w v).hom.app _ at hc
  change _ = _ ≫ (unboundedEtaleUpperStarCompIso Λ w' v').hom.app _ at hc'
  have hinv : D((w')^*[ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarIsoMapDerivedCategory _ v').inv.app K) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory _ w').inv.app
        (L((v')^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        (leftDerivedUpperStarComp _ w' v' (w' ≫ v') rfl).inv.app K =
      (unboundedEtaleUpperStarCompIso Λ w' v').inv.app K ≫
        (leftDerivedUpperStarIsoMapDerivedCategory _ (w' ≫ v')).inv.app K := by
    rw [← cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory _ (w' ≫ v')).hom.app K ≫
      (unboundedEtaleUpperStarCompIso Λ w' v').hom.app K), ← hc']
    simp only [Functor.comp_obj, NatTrans.naturality_assoc, Category.assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% hc']
    simp
  simp only [Functor.map_comp, Category.assoc]
  have n₁ := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) w).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory _ v).hom.app (R(f)_![ModuleCat.{u + 1} Λ].obj K))
  have n₂ := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) w).hom.naturality
    ((unboundedEtaleCompactSupportBaseChange Λ sq₁).app K)
  have n₃ := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) w).hom.naturality
    (R(f')_![ModuleCat.{u + 1} Λ].map ((leftDerivedUpperStarIsoMapDerivedCategory _ v').inv.app K))
  have hE := (unboundedEtaleCompactSupportBaseChange Λ sq₂).naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory _ v').inv.app K)
  simp only [Functor.comp_map] at hE
  rw [reassoc_of% n₃, reassoc_of% hE, reassoc_of% n₂, reassoc_of% n₁,
    ← Functor.map_comp (R(f'')_![ModuleCat.{u + 1} Λ])
      ((unboundedEtaleUpperStarCompIso Λ w' v').inv.app K), ← hinv, ← reassoc_of% hc]
  simp only [Functor.map_comp]

/-- **Vertical pasting of the compactly supported base change maps**: for two stacked
cartesian squares `sqf : vX ≫ f = f' ≫ vY` and `sqg : vY ≫ g = g' ≫ vZ`, with outer square
`sqgf` along `f ≫ g`, the exchange map `Ex_!(sqgf)` is `Ex_!(sqg)` followed by `Rg'_!` of
`Ex_!(sqf)`, up to the composition isomorphisms
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`:

```
LvZ^* Rg_! Rf_! ⟶ Rg'_! LvY^* Rf_! ⟶ Rg'_! Rf'_! LvX^*
      ≅                                  ≅
LvZ^* R(f ≫ g)_! ----------------> R(f' ≫ g')_! LvX^*
```

(blueprint: `sk-def-sf-exchanges`) -/
theorem rightDerivedLowerShriekBaseChangeMap_paste_vert
    {X X' Y Y' Z Z' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((vZ)^*[ModuleCat.{u + 1} Λ]).map ((unboundedEtaleLowerShriekCompIso Λ f g).hom.app K) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sqgf).app K =
      (rightDerivedLowerShriekBaseChangeMap Λ sqg).app (R(f)_![ModuleCat.{u + 1} Λ].obj K) ≫
        R(g')_![ModuleCat.{u + 1} Λ].map ((rightDerivedLowerShriekBaseChangeMap Λ sqf).app K) ≫
        (unboundedEtaleLowerShriekCompIso Λ f' g').hom.app
          (L((vX)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  let H := R(f' ≫ g')_![ModuleCat.{u + 1} Λ]
  let R := R(g')_![ModuleCat.{u + 1} Λ]
  let uZ := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) vZ
  let uX := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) vX
  let a := unboundedEtaleLowerShriekCompIso Λ f g
  let a' := unboundedEtaleLowerShriekCompIso Λ f' g'
  have h := congr_app (unboundedEtaleCompactSupportBaseChange_paste_vert Λ sqf sqg sqgf) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, unboundedEtaleCompactSupportBaseChange, Functor.map_comp,
    Category.assoc] at h
  apply (cancel_epi (uZ.inv.app (R(g)_![ModuleCat.{u + 1} Λ].obj
    (R(f)_![ModuleCat.{u + 1} Λ].obj K)))).mp
  apply (cancel_mono (H.map (uX.hom.app K))).mp
  have hn := uZ.inv.naturality (a.hom.app K)
  erw [← reassoc_of% hn]
  simp only [Category.assoc]
  erw [h]
  have ha := a'.hom.naturality (uX.hom.app K)
  simp only [Functor.comp_map] at ha
  erw [ha]
  erw [← R.map_comp_assoc, Iso.hom_inv_id_app, R.map_id, Category.id_comp]

end Etale

end AlgebraicGeometry

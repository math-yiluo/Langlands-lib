/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareCube
public import WeilConjectures.CategoryTheory.Adjunction.ComparisonMateTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionMapDerived
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.MorphismDefs
import WeilConjectures.AlgebraicGeometry.EtaleExactExchangeComparison

/-!
# Transport of unbounded base change along the site comparison

For a Cartesian square of schemes

```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```

and `L ∈ D(X_ét, Λ)` (unbounded), the étale exchange map `Lg^* Rf_* L ⟶ Rf'_* Lg'^* L`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) and the pro-étale exchange map at `ν_X^* L`
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`) are identified through the comparison
`ν^*`: this is `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap_unbounded`, the
unbounded analogue of `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`. The
direct image comparisons are `AlgebraicGeometry.ProEtale.unboundedDirectImageComparisonMap`, the
pullback comparisons `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIsoUnbounded`.
Consequently (`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_comparisonUpperStar`)
the pro-étale exchange map at `ν_X^* L` is an isomorphism whenever the étale one at `L` and the
two relevant unbounded direct image comparison maps are.

## Implementation details

The proof transports mates along comparison functors
(`CategoryTheory.mateEquiv_app_comparison_transport`). Its inputs are the compatibility of the
unbounded direct image comparison with the counits, which holds by construction, and the
commutativity of the cube of pullback comparisons. The latter is reduced to the underived
coherence `AlgebraicGeometry.ProEtale.comparison_square_component_of_commRing`: exact derivation
preserves commutative cubes (`CategoryTheory.Functor.mapDerivedCategorySquareIso_cube`), and
replacing the induced functors `D(-)` by the derived pullbacks `L(-)` conjugates the cube
(`CategoryTheory.cube_conjugation`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor


namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The unbounded comparison `L(f^*) ν_X^* ≅ ν_Y^* L(f^*)` between the étale and the
pro-étale derived pullbacks along `f : X ⟶ Y`, as functors `D(Y_ét) ⥤ D(X_proét)`: both
derived pullbacks are identified with the functors induced by the exact pullbacks, which
commute with the comparison by `comparisonUpperStarCompUpperStarIso`. -/
noncomputable def leftDerivedUpperStarComparisonIsoUnbounded {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(Etale.upperStar (ModuleCat.{u + 1} Λ) f) ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ≅
      D(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙ L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) :=
  Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ f) _ ≪≫
    Functor.mapDerivedCategorySquareIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ f).symm

/-- The unbounded direct image comparison map is compatible with the counits of the étale
and the pro-étale derived adjunctions `Lf^* ⊣ Rf_*`. -/
theorem leftDerivedUpperStarComparisonIsoUnbounded_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIsoUnbounded Λ f).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        (unboundedDirectImageComparisonMap Λ f K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) =
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have hb : (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.map
        (unboundedDirectImageComparisonMap Λ f K) ≫
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        f).mapDerivedCategoryRightDerivedAdjunction.counit.app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) =
      (unboundedDirectImagePullbackIso Λ f).hom.app
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
          ((Etale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryRightDerivedAdjunction.counit.app K) := by
    have h := (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      f).mapDerivedCategoryRightDerivedAdjunction.homEquiv_counit
      (g := unboundedDirectImageComparisonMap Λ f K)
    rw [← h]
    exact Equiv.symm_apply_apply _ _
  simp only [derivedUpperStarLowerStarAdjunction, Etale.derivedUpperStarLowerStarAdjunction,
    Adjunction.derivedAdjunction_eq_ofNatIsoLeft, Adjunction.ofNatIsoLeft_counit,
    leftDerivedUpperStarComparisonIsoUnbounded, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Iso.symm_inv, Category.assoc, Functor.map_comp,
    leftDerivedUpperStarIsoMapDerivedCategory, Etale.leftDerivedUpperStarIsoMapDerivedCategory]
  rw [(Functor.leftDerivedFunctorIsoMapDerivedCategory
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)).hom.naturality_assoc
    (unboundedDirectImageComparisonMap Λ f K), Iso.inv_hom_id_app_assoc, hb]
  simp [unboundedDirectImagePullbackIso, Functor.mapDerivedCategoryNatIso_symm]

/-- The étale derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square,
expressed through the functors induced by the exact pullbacks and the underived square
isomorphism. -/
theorem Etale.derivedSquareUpperStarIso_eq_mapDerivedCategorySquareIso
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq =
      (Functor.isoWhiskerLeft L(Etale.upperStar (ModuleCat.{u + 1} Λ) g)
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ f') ≪≫
        Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ g)
          D(Etale.upperStar (ModuleCat.{u + 1} Λ) f')) ≪≫
      Functor.mapDerivedCategorySquareIso
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) ≪≫
      (Functor.isoWhiskerLeft L(Etale.upperStar (ModuleCat.{u + 1} Λ) f)
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ g') ≪≫
        Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ f)
          D(Etale.upperStar (ModuleCat.{u + 1} Λ) g')).symm := by
  rw [← Etale.squareUpperStarIso_eq _ sq]
  refine Iso.ext ((Etale.derivedSquareUpperStarIso_eq_exact _ sq).trans ?_)
  ext M
  simp [Etale.exactDerivedSquareUpperStarIso]

/-- Transport of the pro-étale derived pullback along an equality of morphisms is induced by
the transport of the underived pullback. -/
theorem leftDerivedUpperStarCongr_eq {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) :
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) h =
      leftDerivedUpperStarIsoMapDerivedCategory _ f₁ ≪≫
        Functor.mapDerivedCategoryNatIso
          (eqToIso (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} Λ)) h)) ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory _ f₂).symm := by
  subst h
  ext M
  simp [Functor.mapDerivedCategoryNatIso_refl]

/-- The pro-étale derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative
square, expressed through the functors induced by the exact pullbacks and the underived square
isomorphism. -/
theorem leftDerivedUpperStarSquareIso_eq_mapDerivedCategorySquareIso
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq =
      (Functor.isoWhiskerLeft L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)
          (leftDerivedUpperStarIsoMapDerivedCategory _ f') ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ g)
          D(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f')) ≪≫
      Functor.mapDerivedCategorySquareIso
        ((ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) ≪≫
      (Functor.isoWhiskerLeft L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
          (leftDerivedUpperStarIsoMapDerivedCategory _ g') ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ f)
          D(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')).symm := by
  ext M
  simp [leftDerivedUpperStarSquareIso, leftDerivedUpperStarComp, leftDerivedUpperStarCongr_eq,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm]

/-- The underived comparison pullbacks commute with the étale and the pro-étale square
isomorphisms of a Cartesian square, written with `Etale.upperStarComp` and
`ProEtale.upperStarComp`: the two pasted isomorphisms `g^* f'^* ν_{X'}^* ≅ ν_Y^* f^* g'^*`
agree, that is, the cube formed by the two rows of comparison squares
```
  Sh(Y_ét) ───g^*──▶ Sh(Y'_ét) ───f'^*──▶ Sh(X'_ét)
     │                   │                    │
   ν_Y^*              ν_{Y'}^*             ν_{X'}^*
     ▼                   ▼                    ▼
  Sh(Y_proét) ─g^*─▶ Sh(Y'_proét) ─f'^*─▶ Sh(X'_proét)

  Sh(Y_ét) ───f^*──▶ Sh(X_ét) ────g'^*──▶ Sh(X'_ét)
     │                   │                    │
   ν_Y^*               ν_X^*               ν_{X'}^*
     ▼                   ▼                    ▼
  Sh(Y_proét) ─f^*─▶ Sh(X_proét) ──g'^*─▶ Sh(X'_proét)
```
(`comparisonUpperStarCompUpperStarIso`), glued along the étale square isomorphism on top and the
pro-étale square isomorphism at the bottom, commutes. -/
theorem comparisonUpperStarCompUpperStarIso_square
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) :
    Functor.isoWhiskerLeft (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f').symm ≪≫
      Functor.isoWhiskerRight (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f') ≪≫
      Functor.isoWhiskerLeft ν^*(Y)[ModuleCat.{u + 1} Λ]
        ((ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) =
    Functor.isoWhiskerRight
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) ν^*(X')[ModuleCat.{u + 1} Λ] ≪≫
      Functor.isoWhiskerLeft (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g').symm ≪≫
      Functor.isoWhiskerRight (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g') := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have he : comparisonSquareEtalePath Λ cs = comparisonSquareProEtalePath Λ cs :=
    comparisonSquarePaths_eq (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs)
      (comparison_square_component_of_commRing Λ cs)
  exact he.symm

/-- The unbounded comparison isomorphisms `L(-^*) ν^* ≅ ν^* L(-^*)` commute with the étale and
the pro-étale derived square isomorphisms of a Cartesian square: the cube
```
  D(Y_ét) ────Lg^*──▶ D(Y'_ét) ────Lf'^*──▶ D(X'_ét)
     │                   │                    │
    ν^*                 ν^*                  ν^*
     ▼                   ▼                    ▼
  D(Y_proét) ─Lg^*─▶ D(Y'_proét) ─Lf'^*─▶ D(X'_proét)

  D(Y_ét) ────Lf^*──▶ D(X_ét) ─────Lg'^*──▶ D(X'_ét)
     │                   │                    │
    ν^*                 ν^*                  ν^*
     ▼                   ▼                    ▼
  D(Y_proét) ─Lf^*─▶ D(X_proét) ──Lg'^*─▶ D(X'_proét)
```
formed by the two rows of squares `leftDerivedUpperStarComparisonIsoUnbounded`, glued along
`Etale.derivedSquareUpperStarIso` on top and `leftDerivedUpperStarSquareIso` at the bottom,
commutes. -/
theorem leftDerivedUpperStarComparisonIsoUnbounded_square
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(X')[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
      (leftDerivedUpperStarComparisonIsoUnbounded Λ g').hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
        ((leftDerivedUpperStarComparisonIsoUnbounded Λ f).hom.app M) =
    (leftDerivedUpperStarComparisonIsoUnbounded Λ f').hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarComparisonIsoUnbounded Λ g).hom.app M) ≫
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
        (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj M) := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have hcube := Functor.mapDerivedCategorySquareIso_cube
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f').symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g').symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
      eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
      Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f)
    ((ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
      eqToIso (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
      ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) g' f)
    (comparisonUpperStarCompUpperStarIso_square Λ sq)
  have h := cube_conjugation
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f')
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g')
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f')
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g')
    _ _ _ _ _ _ (fun M ↦ hcube M) M
  rw [Etale.derivedSquareUpperStarIso_eq_mapDerivedCategorySquareIso,
    leftDerivedUpperStarSquareIso_eq_mapDerivedCategorySquareIso]
  exact h

/-- **Transport of the unbounded exchange map along the site comparison.** For a Cartesian
square
```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```
and `L ∈ D(X_ét, Λ)`, conjugating the étale exchange map `Lg^* Rf_* L ⟶ Rf'_* Lg'^* L` by the
comparison maps `ν_{Y'}^* Lg^* Rf_* L ≅ Lg^* ν_Y^* Rf_* L ⟶ Lg^* Rf_* ν_X^* L` and
`ν_{Y'}^* Rf'_* Lg'^* L ⟶ Rf'_* ν_{X'}^* Lg'^* L ≅ Rf'_* Lg'^* ν_X^* L` (built from
`AlgebraicGeometry.ProEtale.unboundedDirectImageComparisonMap` and
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIsoUnbounded`) gives the pro-étale
exchange map at `ν_X^* L`. -/
theorem comparison_derivedBaseChangeMap_unbounded
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(Y')[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) ≫
      unboundedDirectImageComparisonMap Λ f'
        (L(Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj L) ≫
      R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarComparisonIsoUnbounded Λ g').hom.app L) =
    (leftDerivedUpperStarComparisonIsoUnbounded Λ g).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).map
        (unboundedDirectImageComparisonMap Λ f L) ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj L) :=
  mateEquiv_app_comparison_transport
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (leftDerivedUpperStarComparisonIsoUnbounded Λ f)
    (leftDerivedUpperStarComparisonIsoUnbounded Λ f')
    (leftDerivedUpperStarComparisonIsoUnbounded Λ g)
    (leftDerivedUpperStarComparisonIsoUnbounded Λ g')
    (unboundedDirectImageComparisonMap Λ f) (unboundedDirectImageComparisonMap Λ f')
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    (leftDerivedUpperStarComparisonIsoUnbounded_counit Λ f)
    (leftDerivedUpperStarComparisonIsoUnbounded_counit Λ f')
    (leftDerivedUpperStarComparisonIsoUnbounded_square Λ sq) L

/-- For a Cartesian square of schemes and `L ∈ D(X_ét, Λ)`, the pro-étale exchange map
`Lg^* Rf_* ν_X^* L ⟶ Rf'_* Lg'^* ν_X^* L` is an isomorphism as soon as the étale exchange map
`Lg^* Rf_* L ⟶ Rf'_* Lg'^* L` is, and the unbounded direct image comparison maps
`ν_Y^* Rf_* L ⟶ Rf_* ν_X^* L` and `ν_{Y'}^* Rf'_* Lg'^* L ⟶ Rf'_* ν_{X'}^* Lg'^* L` are
isomorphisms. -/
theorem isIso_derivedBaseChangeMap_app_comparisonUpperStar
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))
    (hf : IsIso (unboundedDirectImageComparisonMap Λ f L))
    (hf' : IsIso (unboundedDirectImageComparisonMap Λ f'
      (L(Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj L))) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L)) := by
  have h := comparison_derivedBaseChangeMap_unbounded Λ sq L
  have : IsIso ((leftDerivedUpperStarComparisonIsoUnbounded Λ g).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).map
        (unboundedDirectImageComparisonMap Λ f L) ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj L)) := by
    rw [← h]
    infer_instance
  rw [← Category.assoc] at this
  exact IsIso.of_isIso_comp_left ((leftDerivedUpperStarComparisonIsoUnbounded Λ g).hom.app
    (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).map
        (unboundedDirectImageComparisonMap Λ f L)) _

end AlgebraicGeometry.ProEtale

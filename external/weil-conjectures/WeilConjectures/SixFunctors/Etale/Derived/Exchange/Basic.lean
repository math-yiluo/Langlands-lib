/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero

/-!
# The unbounded exchange morphism

For a commutative square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

the *exchange morphism* `Ex_K : Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` on the unbounded derived categories
`D(-_ét)` is the mate of the derived square isomorphism under the derived adjunctions
`Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`; it is `AlgebraicGeometry.Etale.derivedBaseChangeMap`.

This file records it as the exchange morphism `AlgebraicGeometry.Etale.unboundedExchange`,
its naturality, its agreement with the bounded below exchange morphism
`AlgebraicGeometry.Etale.baseChange` on `D⁺`, and the identification of its cohomology sheaves
at a sheaf `F` with the degree-`q` base change maps
`AlgebraicGeometry.Etale.baseChangeHomologyMap` (`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F`).

## Main declarations

- `AlgebraicGeometry.Etale.unboundedExchange` (`definition-derived-base-change-map`).
- `AlgebraicGeometry.Etale.unboundedExchange_naturality` (`lem-kun-unbounded-exchange-natural`).
- `AlgebraicGeometry.Etale.ι_map_baseChange_app` (`lem-kun-unbounded-exchange-agrees`), with the
  arrow isomorphism `AlgebraicGeometry.Etale.baseChangeArrowIsoUnboundedExchange` and the degree
  zero statement `AlgebraicGeometry.Etale.nonempty_arrowIso_homology_zero_unboundedExchange`.
- `AlgebraicGeometry.Etale.homologyArrowIsoBaseChangeHomologyMap`
  (`corollary-open-direct-image-over-field--2`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Blueprint `definition-derived-base-change-map`: the unbounded derived exchange morphism.

For a commutative (in practice cartesian) square `g' ≫ f = f' ≫ g` and `K` in `D(X_ét)`, the
exchange morphism `Ex_K : Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is the mate, under the derived
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*` on the unbounded derived categories, of the
composite `Lf'^* Lg^* Rf_* K ≅ Lg'^* Lf^* Rf_* K ⟶ Lg'^* K` of the square isomorphism `θ` and
`Lg'^*` of the counit `ε_f`. It is `AlgebraicGeometry.Etale.derivedBaseChangeMap`, of which this
is the component at `K`; its adjoint description is
`AlgebraicGeometry.Etale.derivedUpperStar_map_unboundedExchange_counit`. -/
noncomputable abbrev unboundedExchange (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (L((g)^*[A])).obj ((R((f)_*[A])).obj K) ⟶ (R((f')_*[A])).obj ((L((g')^*[A])).obj K) :=
  (derivedBaseChangeMap A sq).app K

/-- The exchange morphism `Ex_K` is the mate of `θ` followed by `Lg'^*(ε_f)`: its adjoint
`Lf'^* Lg^* Rf_* K ⟶ Lg'^* K` is that composite. -/
@[reassoc]
lemma derivedUpperStar_map_unboundedExchange_counit (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (L((f')^*[A])).map (unboundedExchange A sq K) ≫
        (derivedUpperStarLowerStarAdjunction A f').counit.app ((L((g')^*[A])).obj K) =
      (derivedSquareUpperStarIso A sq).hom.app ((R((f)_*[A])).obj K) ≫
        (L((g')^*[A])).map ((derivedUpperStarLowerStarAdjunction A f).counit.app K) :=
  derivedUpperStar_map_derivedBaseChangeMap_app_counit A sq K

/-- Blueprint `lem-kun-unbounded-exchange-natural`: the unbounded exchange morphism is natural
in `K`: for `φ : K ⟶ K'` in `D(X_ét)` the square formed by `Ex_K`, `Ex_K'`, `Lg^* Rf_* φ` and
`Rf'_* Lg'^* φ` commutes. -/
@[reassoc]
lemma unboundedExchange_naturality (sq : CommSq g' f' f g)
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K') :
    (L((g)^*[A])).map ((R((f)_*[A])).map φ) ≫ unboundedExchange A sq K' =
      unboundedExchange A sq K ≫ (R((f')_*[A])).map ((L((g')^*[A])).map φ) :=
  (derivedBaseChangeMap A sq).naturality φ

open _root_.DerivedCategory

/-- Blueprint `lem-kun-unbounded-exchange-agrees`: on a bounded below object `K` the unbounded
exchange morphism `Ex_K` is the bounded below derived exchange morphism
`AlgebraicGeometry.Etale.baseChange` of the square, modulo the identifications `Lg^* ≅ D(g^*)`
of the derived pullbacks and `R⁺f_* ⋙ ι ≅ ι ⋙ Rf_*` of the derived pushforwards.
For sheaves placed in degree `0` it is the underived exchange morphism in degree `0`:
`AlgebraicGeometry.Etale.nonempty_arrowIso_homology_zero_unboundedExchange`. -/
lemma ι_map_baseChange_app (sq : CommSq g' f' f g) (K : Plus (Sheaf X.smallEtaleTopology A)) :
    Plus.ι.map ((Etale.baseChange A sq).app K) =
      D((g)^*[A]).map (((f)_*[A]).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.app _ ≫
        unboundedExchange A sq (Plus.ι.obj K) ≫
        R((f')_*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app _) ≫
        ((f')_*[A]).rightDerivedFunctorPlusCompatibility.inv.app
          (((g')^*[A]).mapDerivedCategoryPlus.obj K) := by
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  exact ι_map_derivedBaseChangeMapPlus_app A sq K

/-- The image in `D(Y'_ét)` of the bounded below exchange morphism at `K` is isomorphic, as an
arrow, to the unbounded exchange morphism at `K`. -/
noncomputable def baseChangeArrowIsoUnboundedExchange (sq : CommSq g' f' f g)
    (K : Plus (Sheaf X.smallEtaleTopology A)) :
    Arrow.mk (Plus.ι.map ((Etale.baseChange A sq).app K)) ≅
      Arrow.mk (unboundedExchange A sq (Plus.ι.obj K)) :=
  Arrow.isoMk
    (D((g)^*[A]).mapIso (((f)_*[A]).rightDerivedFunctorPlusCompatibility.app K) ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.app _)
    (((f')_*[A]).rightDerivedFunctorPlusCompatibility.app
        (((g')^*[A]).mapDerivedCategoryPlus.obj K) ≪≫
      R((f')_*[A]).mapIso ((leftDerivedUpperStarIsoMapDerivedCategory A g').symm.app _)) (by
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Arrow.mk_hom,
        Category.assoc]
      rw [ι_map_baseChange_app]
      simp [← Functor.map_comp])

/-- The unbounded exchange morphism is an isomorphism at a bounded below object `K` if and only
if the bounded below exchange morphism `AlgebraicGeometry.Etale.baseChange` is one at `K`. -/
lemma isIso_unboundedExchange_ι_obj_iff (sq : CommSq g' f' f g)
    (K : Plus (Sheaf X.smallEtaleTopology A)) :
    IsIso (unboundedExchange A sq (Plus.ι.obj K)) ↔ IsIso ((Etale.baseChange A sq).app K) := by
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  exact isIso_derivedBaseChangeMap_app_ι_obj_iff A sq K

end Etale

section Cohomology

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

open _root_.DerivedCategory

/-- Blueprint `corollary-open-direct-image-over-field--2`: the cohomology of the derived base change
map. For a cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

and a sheaf `F` of `Λ`-modules on `T_ét`, the morphism induced on `q`-th cohomology sheaves by
the exchange morphism `p^* Rg_* F ⟶ Rh_* e^* F` of `AlgebraicGeometry.Etale.unboundedExchange`
is, as an arrow, the base change morphism `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of
`AlgebraicGeometry.Etale.baseChangeHomologyMap`. -/
noncomputable def Etale.homologyArrowIsoBaseChangeHomologyMap (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Arrow.mk ((homologyFunctor _ q).map (Etale.unboundedExchange _ sq.toCommSq
      (Plus.ι.obj ((Plus.singleFunctor _ 0).obj F)))) ≅
      Arrow.mk (Etale.baseChangeHomologyMap Λ sq q F) :=
  ((homologyFunctor _ q).mapArrow.mapIso
    (Etale.baseChangeArrowIsoUnboundedExchange _ sq.toCommSq
      ((Plus.singleFunctor _ 0).obj F))).symm

/-- The degree-`q` base change map at `F` is an isomorphism if and only if the exchange morphism
of `AlgebraicGeometry.Etale.unboundedExchange` at `F` is an isomorphism on `q`-th cohomology
sheaves. -/
lemma Etale.isIso_baseChangeHomologyMap_iff_isIso_homology_unboundedExchange
    (sq : IsPullback e h g p) (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) ↔
      IsIso ((homologyFunctor _ q).map (Etale.unboundedExchange _ sq.toCommSq
        (Plus.ι.obj ((Plus.singleFunctor _ 0).obj F)))) :=
  (Arrow.isIso_iff_isIso_of_isIso (Etale.homologyArrowIsoBaseChangeHomologyMap Λ sq q F).hom).symm

/-- Blueprint `lem-kun-unbounded-exchange-agrees`, for sheaves: in degree `0` the exchange
morphism of `AlgebraicGeometry.Etale.unboundedExchange` at a sheaf `F` placed in degree `0` is,
as an arrow, the underived exchange morphism `p⁻¹ g_* F ⟶ h_* e⁻¹ F` of
`AlgebraicGeometry.Etale.baseChangeMap`. -/
theorem Etale.nonempty_arrowIso_homology_zero_unboundedExchange (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (Arrow.mk ((homologyFunctor _ 0).map (Etale.unboundedExchange _ sq.toCommSq
      (Plus.ι.obj ((Plus.singleFunctor _ 0).obj F)))) ≅
      Arrow.mk ((Etale.baseChangeMap _ sq.toCommSq).app F)) :=
  (Etale.nonempty_arrowIso_baseChangeHomologyMap_zero Λ sq F).map
    ((Etale.homologyArrowIsoBaseChangeHomologyMap Λ sq 0 F) ≪≫ ·)

end Cohomology

end AlgebraicGeometry

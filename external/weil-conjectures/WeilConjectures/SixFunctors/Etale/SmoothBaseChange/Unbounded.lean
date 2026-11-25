/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# Smooth base change on the unbounded derived categories

Consider a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `g` smooth and `f` quasi-compact, quasi-separated and locally of finite type, `Y` locally of
finite type over a separably closed field `k`, and a coefficient ring `Λ` killed by an integer
invertible on `Y`. This file upgrades the smooth base change theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth` to the unbounded derived
categories: the derived base change map

`Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

of `D(-_ét, Λ)` is an isomorphism (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_smooth`).

The argument is the one of the unbounded proper base change theorem
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`, through
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isIso_baseChangeMap`:

* in degree `0` the smooth base change theorem says that the underived base change map
  `g^* f_* ⟶ f'_* g'^*` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_smooth`);
* in positive degrees it says that `g'^*` of an injective sheaf is `f'_*`-acyclic;
* the higher direct images along `f'` vanish, at each geometric point of `Y'`, above a bound
  only depending on the point: over an affine open neighbourhood `V` of the point, smooth base
  change along the open immersion `V ⟶ Y'` identifies them with the higher direct images along
  `X' ×_{Y'} V ⟶ V`, which vanish above twice the dimension of the quasi-compact scheme
  `X' ×_{Y'} V` (`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace Etale

/-- If the exponent of `Λ` is invertible on `S`, every sheaf of `Λ`-modules is torsion of orders
invertible on `S`. -/
lemma isTorsionSheafOfInvertibleOrder_of_hasInvertibleExponent (S : Scheme.{u})
    [HasInvertibleExponent Λ S] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheafOfInvertibleOrder S F := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  exact .of_natCast_eq_zero Λ n hn.ne' hΛ hu F

/-- If the exponent of `Λ` is invertible on some scheme, `Λ` is torsion as an additive group. -/
lemma isAddTorsion_of_hasInvertibleExponent (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    IsAddTorsion Λ := by
  obtain ⟨n, hn, hΛ, -⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  intro a
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The degree-`q` smooth base change map at a sheaf `F`, read as a map
`g^* R^q f_* F ⟶ R^q f'_* g'^* F` between the classical higher direct images. Its source is
identified with `g^*` of `R^q f_* F` and its target with `R^q f'_*` of `g'^* F`. -/
noncomputable def baseChangeHomologyMapSourceIso (p : X ⟶ Y) (q : ℕ)
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h : X' ⟶ Y) :
    (Etale.baseChangeSourceFunctor Λ p h q).obj F ≅
      (p)^*[ModuleCat.{u + 1} Λ].obj ((((h)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F) :=
  (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).symm.app
      ((h)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
    (p)^*[ModuleCat.{u + 1} Λ].mapIso
      ((h)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso F q)

/-- The target of the degree-`q` base change map at `F` is `R^q h_*` of `e^* F`. -/
noncomputable def baseChangeHomologyMapTargetIso (e : Y ⟶ X') (h : Y ⟶ X) (q : ℕ)
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChangeTargetFunctor Λ e h q).obj F ≅
      (((h)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj ((e)^*[ModuleCat.{u + 1} Λ].obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((h)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
        ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F)) ≪≫
    (h)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso _ q

section

variable [HasInvertibleExponent Λ Y] [Smooth g] [QuasiCompact f] [QuasiSeparated f]

/-- **Smooth base change in degree `0`**: for a cartesian square with `g` smooth and `f`
quasi-compact and quasi-separated, and a coefficient ring `Λ` whose exponent is invertible on
`Y`, the underived base change map `g^* f_* ⟶ f'_* g'^*` is an isomorphism. This is the degree
`0` case of `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth`, through
`AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_zero`. -/
theorem isIso_baseChangeMap_of_smooth (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  have := isTorsionSheafOfInvertibleOrder_of_hasInvertibleExponent Λ Y F
  have := Etale.isIso_baseChangeHomologyMap_of_smooth Λ g f g' f' sq 0 F
  obtain ⟨e⟩ := Etale.nonempty_arrowIso_baseChangeHomologyMap_zero Λ sq F
  exact (Arrow.isIso_hom_iff_isIso_hom_of_isIso e.hom).1 this

/-- **Smooth base change and injectives**: for a cartesian square with `g` smooth and `f`
quasi-compact and quasi-separated, and a coefficient ring `Λ` whose exponent is invertible on
`Y`, the pullback `g'^* I` of an injective sheaf `I` on `X` is `f'_*`-acyclic: by smooth base
change `R^q f'_* g'^* I ≅ g^* R^q f_* I = 0` for `q > 0`. -/
theorem rightAcyclic_upperStar_of_smooth (sq : IsPullback g' f' f g)
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
    ((f')_*[ModuleCat.{u + 1} Λ]).rightAcyclic ((g')^*[ModuleCat.{u + 1} Λ].obj I) := by
  intro q
  have := isTorsionSheafOfInvertibleOrder_of_hasInvertibleExponent Λ Y I
  have := Etale.isIso_baseChangeHomologyMap_of_smooth Λ g f g' f' sq (q + 1 : ℕ) I
  have hz : IsZero ((g)^*[ModuleCat.{u + 1} Λ].obj
      ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived (q + 1)).obj I)) :=
    Functor.map_isZero _ (Functor.isZero_rightDerived_obj_injective_succ _ q I)
  exact hz.of_iso ((baseChangeHomologyMapTargetIso Λ g' f' (q + 1) I).symm ≪≫
    (asIso (Etale.baseChangeHomologyMap Λ sq (q + 1 : ℕ) I)).symm ≪≫
    baseChangeHomologyMapSourceIso Λ g (q + 1) I f)

end

/-- **Higher direct images have pointwise bounded amplitude**: let `k` be a separably closed
field, `f : X ⟶ Y` a quasi-compact, quasi-separated morphism locally of finite type, `Y` locally
of finite type over `k`, and `Λ` a coefficient ring whose exponent is invertible on `Y`. For every
point `y` of `Y` there is `d` such that `t^* R^q f_* G = 0` for every `q > d` and every étale sheaf
`G` of `Λ`-modules on `X`, where `t : Spec Ω ⟶ Y` is the geometric point at `y`.

Choose an affine open neighbourhood `V` of `y`. Smooth base change along the open immersion
`V ⟶ Y` identifies the restriction of `R^q f_* G` to `V` with `R^q` of the direct image along
`X ×_Y V ⟶ V`, which vanishes for `q > 2 dim (X ×_Y V)`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`), `X ×_Y V` being quasi-compact
and locally of finite type over `k`, hence of finite dimension. -/
theorem exists_isZero_upperStar_rightDerived_lowerStar {k : Type u} [Field k] [IsSepClosed k]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y] (y : Y) :
    ∃ d : ℕ, ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((Y.algClosurePoint y)^*[ModuleCat.{u + 1} Λ].obj
        (((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q |>.obj G)) := by
  have hΛ := isAddTorsion_of_hasInvertibleExponent Λ Y
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : IsAffine V := hV
  let j := V.ι
  let t := Y.algClosurePoint y
  have hrange : Set.range t.base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    simpa [t] using hyV
  let t' := IsOpenImmersion.lift j t hrange
  have ht : t' ≫ j = t := IsOpenImmersion.lift_fac j t hrange
  let sq := IsPullback.of_hasPullback f j
  let P := pullback f j
  let aP : P ⟶ Spec (.of k) := pullback.snd f j ≫ j ≫ aY
  have : LocallyOfFiniteType aP := inferInstance
  have : QuasiCompact aP := inferInstance
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_locallyOfFiniteType aP
  refine ⟨2 * d, fun G q hq ↦ ?_⟩
  have := isTorsionSheafOfInvertibleOrder_of_hasInvertibleExponent Λ Y G
  have := Etale.isIso_baseChangeHomologyMap_of_smooth Λ j f (pullback.fst f j)
    (pullback.snd f j) sq q G
  have hvan := Etale.isZero_higherDirectImage_of_two_mul_lt hΛ (pullback.snd f j) aP (j ≫ aY)
    rfl d hd ((pullback.fst f j)^*[ModuleCat.{u + 1} Λ].obj G) q (by omega)
  have hV' : IsZero ((j)^*[ModuleCat.{u + 1} Λ].obj
      ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj G)) :=
    hvan.of_iso (((baseChangeHomologyMapSourceIso Λ j q G f).symm ≪≫
      asIso (Etale.baseChangeHomologyMap Λ sq q G) ≪≫
      baseChangeHomologyMapTargetIso Λ (pullback.fst f j) (pullback.snd f j) q G) ≪≫
      ((pullback.snd f j)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso
        _ q).symm)
  exact (Functor.map_isZero (t')^*[ModuleCat.{u + 1} Λ] hV').of_iso
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) t' j t ht.symm).app _)

/-- **Smooth base change on the unbounded derived categories.** Let `k` be a separably closed
field, `Y` a scheme locally of finite type over `k`, and `Λ` a coefficient ring whose exponent is
invertible on `Y`. For a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `g` smooth and `f` quasi-compact, quasi-separated and locally of finite type, the derived
base change map `Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` on the unbounded derived categories
`D(-_ét, Λ)` is an isomorphism.

This is the unbounded upgrade of the smooth base change theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth` (blueprint
`theorem-smooth-base-change-classical-torsion--1`), by the argument of
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`: the
underived base change map is an isomorphism (`isIso_baseChangeMap_of_smooth`), `g'^*` of an
injective sheaf is `f'_*`-acyclic (`rightAcyclic_upperStar_of_smooth`), and `f'_*` has pointwise
bounded cohomological amplitude (`exists_isZero_upperStar_rightDerived_lowerStar`), so that it
carries exact complexes of acyclic sheaves to exact complexes. -/
theorem isIso_derivedBaseChangeMap_of_smooth {k : Type u} [Field k] [IsSepClosed k]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y] [Smooth g]
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
    isIso_baseChangeMap_of_smooth Λ sq
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : QuasiSeparated f' :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
  have : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : HasInvertibleExponent Λ Y' := HasInvertibleExponent.of_hom g
  refine Etale.isIso_derivedBaseChangeMap_of_isIso_baseChangeMap _ sq.toCommSq
    (fun M hM hM' ↦ ?_) (fun I _ ↦ rightAcyclic_upperStar_of_smooth Λ sq I)
  choose d hd using exists_isZero_upperStar_rightDerived_lowerStar Λ f' (g ≫ aY)
  exact hM.map_of_rightAcyclic_of_forall_isZero _
    (fun y ↦ Etale.upperStar (ModuleCat.{u + 1} Λ) (Y'.algClosurePoint y))
    (Etale.isZero_of_forall_isZero_upperStar_algClosurePoint Λ) d hd hM'

end Etale

end AlgebraicGeometry

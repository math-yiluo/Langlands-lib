/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Integral.BaseChange

/-!
# Integral base changes of the base-change map

Two operations on a Cartesian square do not change whether its degree-`q` base-change map
`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism, as long as the morphism involved is
integral:

- replacing the bottom right corner `T` by `T'` along an integral surjective `π : T' ⟶ T`,
  provided `BC(p, Λ, q - 1)` holds
  (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective`);
- replacing the base `S'` of `p'` by `S''` along an integral `π : S'' ⟶ S'` through which
  `g` factors (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom`).

Both rest on the exactness of the direct image along an integral morphism,
`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`, and on base change
along an integral morphism,
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom`: in each case the
direct image along `π` (resp. along its base change `π'`) identifies the two base-change maps,
which is recorded in `AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar`
and `AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_comp`. Both are read off
from the vertical pasting law `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert` of
the derived base-change maps.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective`:
  integral surjective base change on the target.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom`: integral base
  change on the source.

## References

- Stacks Project, Lemma 59.88.3, <https://stacks.math.columbia.edu/tag/0F04>
- Stacks Project, Lemma 59.88.4, <https://stacks.math.columbia.edu/tag/0F05>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The degree-`q` base-change map at `F` is, as an arrow, the degree-`q` homology of the
derived base-change map `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus` at `F` placed in
degree `0`. -/
lemma Etale.arrow_mk_baseChangeHomologyMap {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Arrow.mk (Etale.baseChangeHomologyMap Λ sq q F) = Arrow.mk
      ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  rw [Etale.baseChangeHomologyMap, Etale.baseChangeHomologyNatTrans_eq,
    Etale.baseChange_eq_derivedBaseChangeMapPlus]
  exact Arrow.mk_whiskerLeft_whiskerRight_app _ _ _ _

section Target

variable {X S T Y T' Y' : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
  {e' : Y' ⟶ T'} {h' : Y' ⟶ X}

/-- The direct image along an integral morphism `π : T' ⟶ T` identifies base-change maps:
for Cartesian squares over `g : T ⟶ S` and over `π ≫ g`, the base-change map of the first
square at `π_* F'` is isomorphic, as an arrow, to the base-change map of the second square at
`F'`.

Write `h' = π'' ≫ h` with `π'' : Y' ⟶ Y` the base change of `π`. By the vertical pasting law
the derived base-change map of the square over `π ≫ g` at `F'` is the one of the square over
`g` at `Rπ_* F'`, followed by `Rh_*` of the derived base-change map of the square of `π''`
over `π`, modulo the composition isomorphisms of the derived pushforwards. The latter is an
isomorphism (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom`), and
`Rπ_* F' = π_* F'` as `π_*` is exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`). This is the
identification in the proof of blueprint `lemma-integral-changes-source-base--1`. -/
theorem Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar (sq : IsPullback e h g p)
    (π : T' ⟶ T) [IsIntegralHom π] (sq' : IsPullback e' h' (π ≫ g) p) (q : ℤ)
    (F' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (Arrow.mk
      (Etale.baseChangeHomologyMap Λ sq q ((π)_*[ModuleCat.{u + 1} Λ].obj F')) ≅
        Arrow.mk (Etale.baseChangeHomologyMap Λ sq' q F')) := by
  obtain ⟨π'', hπ''e, rfl⟩ : ∃ π'' : Y' ⟶ Y, π'' ≫ e = e' ≫ π ∧ π'' ≫ h = h' :=
    ⟨sq.lift (e' ≫ π) h' (by simp [sq'.w]), sq.lift_fst _ _ _, sq.lift_snd _ _ _⟩
  have sq₁ : IsPullback e' π'' π e := IsPullback.of_bot sq' hπ''e.symm sq
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ π
  have := Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom Λ sq₁
  have hfac := NatTrans.congr_app (Etale.derivedBaseChangeMapPlus_paste_vert
    (ModuleCat.{u + 1} Λ) sq₁.toCommSq sq.toCommSq sq'.toCommSq)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F')
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hfac
  -- `Rπ_* (F'[0]) ≅ (π_* F')[0]`, the direct image along `π` being exact
  let ι : R+((π)_*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F') ≅
        (DerivedCategory.Plus.singleFunctor _ 0).obj ((π)_*[ModuleCat.{u + 1} Λ].obj F') :=
    ((π)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app _ ≪≫
      (((π)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F'
  refine ⟨eqToIso (Etale.arrow_mk_baseChangeHomologyMap Λ sq q _) ≪≫
    (Arrow.isoMapApp _ _ ι).symm ≪≫ ?_ ≪≫
    eqToIso (Etale.arrow_mk_baseChangeHomologyMap Λ sq' q F').symm⟩
  rw [hfac]
  simp only [Functor.map_comp]
  exact (Arrow.isoOfIsIsoComp _ _ _).symm

/-- Blueprint `lemma-integral-changes-source-base--1`: Integral surjective base change on the
target.

Assume `BC(p, Λ, q - 1)` for some `q ≥ 1`. Let `g : T ⟶ S` be quasi-compact and
quasi-separated, `π : T' ⟶ T` integral and surjective, and consider Cartesian squares over `g`
and over `π ≫ g`. If the base-change map of the square over `π ≫ g` is an isomorphism at
`π⁻¹ F`, then the base-change map of the square over `g` is an isomorphism at `F`.

Since `π` is surjective, `F ⟶ π_* π⁻¹ F` is injective
(`AlgebraicGeometry.Etale.mono_unit_app_of_surjective`), so by
`AlgebraicGeometry.Etale.mono_cokernelMap` the cokernel of the base-change map at `F` embeds
into the one at `π_* π⁻¹ F`. The latter vanishes, the base-change map at `π_* π⁻¹ F` being
identified with the one over `π ≫ g` at `π⁻¹ F` by
`AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar`. The base-change
map at `F` is therefore surjective, and it is injective by
`AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`. -/
@[stacks 0F04]
theorem Etale.isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) (π : T' ⟶ T) [IsIntegralHom π] (hπ : Function.Surjective π.base)
    (sq' : IsPullback e' h' (π ≫ g) p) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsIso (Etale.baseChangeHomologyMap Λ sq' q ((π)^*[ModuleCat.{u + 1} Λ].obj F))) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  obtain ⟨φ⟩ := Etale.nonempty_arrowIso_baseChangeHomologyMap_lowerStar Λ sq π sq' q
    ((π)^*[ModuleCat.{u + 1} Λ].obj F)
  have : IsIso (Etale.baseChangeHomologyMap Λ sq q
      ((π)_*[ModuleCat.{u + 1} Λ].obj ((π)^*[ModuleCat.{u + 1} Λ].obj F))) :=
    (Arrow.isIso_iff_isIso_of_isIso φ.hom).2 hF
  have := Etale.mono_baseChangeHomologyMap Λ q hq hprev sq F
  have := Etale.mono_unit_app_of_surjective Λ π hπ F
  have hc := Etale.mono_cokernelMap Λ q hq hprev sq
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).unit.app F)
  have : Epi (Etale.baseChangeHomologyMap Λ sq q F) :=
    Preadditive.epi_of_isZero_cokernel _ (@IsZero.of_mono _ _ _ _ _ _ hc (isZero_cokernel_of_epi
      (Etale.baseChangeHomologyMap Λ sq q
        ((π)_*[ModuleCat.{u + 1} Λ].obj ((π)^*[ModuleCat.{u + 1} Λ].obj F)))))
  exact isIso_of_mono_of_epi _

end Target

section Source

variable {X' S' S'' X'' T Y : Scheme.{u}} {p' : X' ⟶ S'} {p'' : X'' ⟶ S''} {π' : X'' ⟶ X'}
  {g' : T ⟶ S''} {e : Y ⟶ T} {h'' : Y ⟶ X''}

/-- The direct image along the base change `π' : X'' ⟶ X'` of an integral morphism
`π : S'' ⟶ S'` identifies base-change maps: for a Cartesian square over `g' : T ⟶ S''` for
the base change `p''` of `p'` along `π`, the base-change map of the pasted square over
`g' ≫ π` is isomorphic, as an arrow, to the image under `π'_*` of the base-change map of the
square over `g'`.

By the vertical pasting law the derived base-change map of the pasted square over `g' ≫ π` is
the derived base-change map of the square of `π'` over `π` at `Rg'_* F`, followed by `Rπ'_*` of
the derived base-change map of the square over `g'`, modulo the composition isomorphisms of the
derived pushforwards. The former is an isomorphism
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom`), and `Rπ'_*`
commutes with the homology functors as `π'_*` is exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom`). This is the
identification in the proof of blueprint `lemma-integral-changes-source-base--2`. -/
theorem Etale.nonempty_arrowIso_baseChangeHomologyMap_comp (π : S'' ⟶ S') [IsIntegralHom π]
    (hπ : IsPullback π' p'' p' π) (sq'' : IsPullback e h'' g' p'')
    (sq : IsPullback e (h'' ≫ π') (g' ≫ π) p') (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (Arrow.mk (Etale.baseChangeHomologyMap Λ sq q F) ≅
      Arrow.mk ((π')_*[ModuleCat.{u + 1} Λ].map (Etale.baseChangeHomologyMap Λ sq'' q F))) := by
  have : IsIntegralHom π' := MorphismProperty.of_isPullback hπ.flip inferInstance
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ π'
  have := Etale.isIso_derivedBaseChangeMapPlus_of_isIntegralHom Λ hπ.flip
  have hfac := NatTrans.congr_app (Etale.derivedBaseChangeMapPlus_paste_vert
    (ModuleCat.{u + 1} Λ) sq''.toCommSq hπ.flip.toCommSq sq.toCommSq)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hfac
  -- `H^q ∘ Rπ'_* ≅ π'_* ∘ H^q`, the direct image along `π'` being exact
  let N : R+((π')_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q ≅
      DerivedCategory.Plus.homologyFunctor _ q ⋙ (π')_*[ModuleCat.{u + 1} Λ] :=
    Functor.isoWhiskerRight
        ((π')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _ ≪≫
      (((π')_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).symm
  refine ⟨eqToIso (Etale.arrow_mk_baseChangeHomologyMap Λ sq q F) ≪≫ ?_ ≪≫
    Arrow.isoOfNatIso N
      (Arrow.mk ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq''.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≪≫
    eqToIso (congrArg ((π')_*[ModuleCat.{u + 1} Λ]).mapArrow.obj
      (Etale.arrow_mk_baseChangeHomologyMap Λ sq'' q F)).symm⟩
  rw [hfac]
  simp only [Functor.map_comp]
  rw [← Category.assoc]
  exact Arrow.isoOfIsIsoComp _ _ _

/-- Blueprint `lemma-integral-changes-source-base--2`: Integral base change on the source.

Let `π : S'' ⟶ S'` be integral, `p'' : X'' ⟶ S''` the base change of `p' : X' ⟶ S'` along
`π`, and consider a Cartesian square for `p''` over `g' : T ⟶ S''` and the pasted Cartesian
square for `p'` over `g' ≫ π`. Then the base-change map of the pasted square at `F` is an
isomorphism if and only if the base-change map of the square over `g'` is.

The blueprint states the forward implication; the converse is what the proof of blueprint
`lemma-reduction-curve-over-normal-base--1` uses. By
`AlgebraicGeometry.Etale.nonempty_arrowIso_baseChangeHomologyMap_comp` the first map is the
image under `π'_*` of the second, and `π'_*` is conservative
(`AlgebraicGeometry.Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom`), `π'` being
integral as a base change of `π`. -/
@[stacks 0F05]
theorem Etale.isIso_baseChangeHomologyMap_iff_of_isIntegralHom (π : S'' ⟶ S') [IsIntegralHom π]
    (hπ : IsPullback π' p'' p' π) (sq'' : IsPullback e h'' g' p'')
    (sq : IsPullback e (h'' ≫ π') (g' ≫ π) p') (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) ↔
      IsIso (Etale.baseChangeHomologyMap Λ sq'' q F) := by
  obtain ⟨φ⟩ := Etale.nonempty_arrowIso_baseChangeHomologyMap_comp Λ π hπ sq'' sq q F
  rw [Arrow.isIso_iff_isIso_of_isIso φ.hom]
  have : IsIntegralHom π' := MorphismProperty.of_isPullback hπ.flip inferInstance
  have := Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom Λ π'
  exact ⟨fun _ ↦ isIso_of_reflects_iso _ (π')_*[ModuleCat.{u + 1} Λ], fun _ ↦ inferInstance⟩

end Source

end AlgebraicGeometry

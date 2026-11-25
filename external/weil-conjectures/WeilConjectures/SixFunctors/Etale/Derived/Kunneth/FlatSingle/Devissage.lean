/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.FiniteGood
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.BaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.FilteredColimit
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Coefficients
public import WeilConjectures.ConstructibleSheaf.FiniteTypePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Degreewise
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.FlatLowerStar

/-!
# Dévissage of the flat sheaf in the base change map

For a commutative square `h ≫ f' = e ≫ g` with `h` quasi-compact and quasi-separated, and
`p : X' ⟶ X` with `X` of finite type over a field, consider the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* 𝓔 ⊗ᴸ Lf'^* Rg_* 𝓕 ⟶ Rh_* (Lh^* Lp^* 𝓔 ⊗ᴸ Le^* 𝓕)`

for sheaves `𝓔` on `X` and `𝓕` on `T` placed in degree `0`. If it is an isomorphism for the
pushforwards `𝓔 = π_* Λ` along finite morphisms `π : Xᵢ ⟶ X`, it is an isomorphism for every
flat `𝓔` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_singleFunctor_of_flat_of_lowerStar`).

This is the dévissage of the proof of blueprint `lemma-kunneth-field-coefficients--1`: reduce `𝓕` to
sheaves killed by the Jacobson radical `J` of `Λ` (long exact sequences, both sides being
triangulated in `𝓕`), replace `𝓔` by `𝓔 / J𝓔` (the homology sheaves of both sides only depend on it,
`𝓔` being flat), write it as a filtered colimit of constructible sheaves (blueprint
`lemma-finiteness-small-etale-topoi--1`,
`AlgebraicGeometry.Etale.exists_isColimit_isConstructibleSheaf`), embed a constructible sheaf killed
by `J` into a finite sum of pushforwards `π_* M` along finite morphisms
(`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_locallyOfFiniteType`) and shift
dimensions; the modules `M` killed by `J` are direct summands of free `Λ ⧸ J`-modules.

## Main statements

- `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_lowerStar_unit`: the case `𝓔 = π_* Λ`.
- `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_singleFunctor_of_flat_of_lowerStar`: the
  dévissage.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The pullback along `p` of the pushforward of the unit along a finite `π : Xᵢ ⟶ X`, placed in
degree `0`, is the derived pushforward of the unit along the base change `π' : X'ᵢ ⟶ X'`. -/
noncomputable def leftDerivedUpperStarSingleFunctorLowerStarUnitIso {X X' Xᵢ X'ᵢ : Scheme.{u}}
    (p : X' ⟶ X) (π : Xᵢ ⟶ X) [IsFinite π] (pᵢ : X'ᵢ ⟶ Xᵢ) (π' : X'ᵢ ⟶ X')
    (sqπ : IsPullback pᵢ π' π p) :
    L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))) ≅
      R((π')_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _) :=
  have : IsIso (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqπ.toCommSq) :=
    isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sqπ
  L((p)^*[ModuleCat.{u + 1} Λ]).mapIso
      (((Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory _ π).app _ ≪≫
        (((π)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
      R((π)_*[ModuleCat.{u + 1} Λ]).mapIso (singleFunctorObjUnitIso _ _)) ≪≫
    asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqπ.toCommSq).app (𝟙_ _)) ≪≫
    R((π')_*[ModuleCat.{u + 1} Λ]).mapIso (leftDerivedUpperStarUnitIso _ pᵢ)

/-- The case `𝓔 = π_* Λ`, `π` finite, of blueprint `lemma-kunneth-field-coefficients--1` for single
sheaves (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_rightDerivedLowerStar_unit`, with
blueprint `lemma-kunneth-field-coefficients--1` for `X` and for `Xᵢ`). -/
theorem isIso_tensorBaseChangeMap_lowerStar_unit {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    {Xᵢ : Scheme.{u}} (π : Xᵢ ⟶ X) [IsFinite π]
    (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))
      ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) := by
  have sqπ := IsPullback.of_hasPullback π p
  have sq := IsPullback.of_hasPullback (pullback.snd π p) h
  have : IsFinite (pullback.snd π p) := MorphismProperty.of_isPullback sqπ inferInstance
  refine (NatTrans.isIso_app_iff_of_iso (tensorBaseChangeMapLeft (ModuleCat.{u + 1} Λ) h e f' g
    sq₂.w ((DerivedCategory.singleFunctor _ 0).obj 𝓕))
    (leftDerivedUpperStarSingleFunctorLowerStarUnitIso Λ p π _ _ sqπ)).2 ?_
  exact isIso_tensorBaseChangeMap_rightDerivedLowerStar_unit Λ h e f' g sq₂.w _ _ _ sq _
    (isIso_derivedBaseChangeMap_app_singleFunctor Λ a b p f' h e g sq₁ sq₂ 𝓕)
    (isIso_derivedBaseChangeMap_app_upperStar_singleFunctor Λ a b p f' h e g sq₁ sq₂ π _ _ sqπ
      _ _ sq 𝓕)

section

-- Use the instance paths of the constructions for a general coefficient category, see
-- `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Degreewise`.
attribute [local instance 10000] Abelian.toPreadditive SymmetricCategory.toBraidedCategory

/-- **Dévissage of the flat sheaf**, for coefficient sheaves killed by the Jacobson radical `J` of
`Λ`: for `X` of finite type over a field and `h` quasi-compact and quasi-separated, if the base
change map `Lp^* 𝓔 ⊗ᴸ Lf'^* Rg_* 𝓕 ⟶ Rh_* (Lh^* Lp^* 𝓔 ⊗ᴸ Le^* 𝓕)` is an isomorphism for the
pushforwards `𝓔 = π_* Λ` along finite morphisms `π`, it is an isomorphism for every flat `𝓔` and
every sheaf `𝓕` killed by `J`. The homology sheaves of both sides then only depend on `𝓔 / J𝓔`,
which is a filtered colimit of constructible sheaves killed by `J` (blueprint
`lemma-finiteness-small-etale-topoi--1`), and these embed into finite sums of pushforwards along
finite morphisms of constant sheaves killed by `J`, direct summands of sums of `π_* (Λ ⧸ J)`. -/
theorem isIso_tensorBaseChangeMap_singleFunctor_of_flat_of_lowerStar_of_smul_eq_zero
    {K : Type u} [Field K]
    {X X' S' T Y : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact h]
    [QuasiSeparated h] (w : h ≫ f' = e ≫ g)
    (hgood : ∀ {Xᵢ : Scheme.{u}} (π : Xᵢ ⟶ X) [IsFinite π]
      (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
        (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))
        ((DerivedCategory.singleFunctor _ 0).obj 𝓕)))
    (𝓔 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h𝓔 : ObjectProperty.flat 𝓔)
    (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h𝓕 : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 𝓕 = 0) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓔))
      ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) := by
  rw [isIso_tensorBaseChangeMap_iff_forall_isIso_tensorBaseChangeHomologyMap
    (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 𝓔 h𝓔]
  intro q
  refine isIso_tensorBaseChangeHomologyMap_app_of_cokernel_lowerStar Λ p h e f' g w 𝓕 a h𝓕
    (fun π _ q ↦ ?_) q 𝓔
  rw [← isIso_tensorBaseChangeHomologyMap_app_iff_cokernel_smulDesc Λ p h e f' g w 𝓕 h𝓕]
  have hU : ObjectProperty.flat ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _)) :=
    flat_lowerStar_obj_tensorUnit_of_isFinite Λ π
  have h₁ := hgood π 𝓕
  have h₂ := (isIso_tensorBaseChangeMap_iff_forall_isIso_tensorBaseChangeHomologyMap
    (ModuleCat.{u + 1} Λ) p h e f' g w 𝓕 _ hU).1
  exact h₂ h₁ q

end

/-- **Dévissage of the flat sheaf** in the proof of blueprint `lemma-kunneth-field-coefficients--1`:
for `X` of finite type over a field, `h` quasi-compact and quasi-separated, if the base change map
`Lp^* 𝓔 ⊗ᴸ Lf'^* Rg_* 𝓕 ⟶ Rh_* (Lh^* Lp^* 𝓔 ⊗ᴸ Le^* 𝓕)` is an isomorphism for the
pushforwards `𝓔 = π_* Λ` along finite morphisms `π` and every sheaf `𝓕`, it is an isomorphism for
every flat sheaf `𝓔` and every sheaf `𝓕`
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_singleFunctor_of_smul_eq_zero`). -/
theorem isIso_tensorBaseChangeMap_singleFunctor_of_flat_of_lowerStar {K : Type u} [Field K]
    {X X' S' T Y : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact h]
    [QuasiSeparated h] (w : h ≫ f' = e ≫ g)
    (hgood : ∀ {Xᵢ : Scheme.{u}} (π : Xᵢ ⟶ X) [IsFinite π]
      (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
        (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))
        ((DerivedCategory.singleFunctor _ 0).obj 𝓕)))
    (𝓔 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h𝓔 : ObjectProperty.flat 𝓔)
    (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓔))
      ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) :=
  isIso_tensorBaseChangeMap_singleFunctor_of_smul_eq_zero h e f' g w _
    (fun 𝓕 h𝓕 ↦ isIso_tensorBaseChangeMap_singleFunctor_of_flat_of_lowerStar_of_smul_eq_zero Λ
      a p f' h e g w hgood 𝓔 h𝓔 𝓕 h𝓕) 𝓕

end Etale

end AlgebraicGeometry

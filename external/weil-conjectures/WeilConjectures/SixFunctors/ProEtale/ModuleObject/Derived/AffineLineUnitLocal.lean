/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.CategoryTheory.Adjunction.UnitIsIsoTransfer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# The unit of the affine line is pro-étale local

Let `Λ` be a commutative condensed ring and, for a scheme `X`, let `p_X : 𝔸¹_X ⟶ X` be the affine
line. This file shows that the invertibility of the unit `K ⟶ Rp_{X*} Lp_X^* K` of the derived
adjunction `Lp_X^* ⊣ Rp_{X*}` of module objects is a pro-étale local property of `K`:

* along a weakly étale `g : W ⟶ X`, `Lg^*` of the unit at `K` is invertible if and only if the
  unit of `p_W` at `Lg^* K` is, by weakly étale base change
  (`ProEtale.CondensedRing.isIso_leftDerivedUpperStar_map_affineLineUnit_app_iff`);
* the unit at `K` is invertible as soon as the units at the pullbacks of `K` to the members of a
  pro-étale cover are (`ProEtale.CondensedRing.isIso_affineLineUnit_app_of_cover`).

Consequently, if the unit of `p_X` is invertible at the unit `Λ_X`, it is invertible at every
complex `M[0]` for a module object `M` which is pro-étale locally a finite direct sum of copies of
`Λ` (`ProEtale.CondensedRing.isIso_affineLineUnit_app_singleFunctor_of_cover`): the form in
which homotopy invariance for lisse sheaves reduces to the constant sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The unit of the affine line and weakly étale pullback.** For a weakly étale `g : W ⟶ X`,
`Lg^*` of the unit `K ⟶ Rp_{X*} Lp_X^* K` of the affine line `p_X : 𝔸¹_X ⟶ X` is invertible if and
only if the unit of `p_W` at `Lg^* K` is: by weakly étale base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`) for the cartesian square of `p_X`
along `g`, and the compatibility of the units with the base change morphism. -/
lemma isIso_leftDerivedUpperStar_map_affineLineUnit_app_iff {W X : Scheme.{u}} (g : W ⟶ X)
    [WeaklyEtale g]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso (L((g)^*⟦Λ⟧).map
        ((derivedUpperStarLowerStarAdjunction Λ (𝔸(ULift.{u} (Fin 1); X) ↘ X)).unit.app K)) ↔
      IsIso ((derivedUpperStarLowerStarAdjunction Λ (𝔸(ULift.{u} (Fin 1); W) ↘ W)).unit.app
        ((L((g)^*⟦Λ⟧)).obj K)) := by
  let sq := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g
  have : WeaklyEtale (AffineSpace.map (ULift.{u} (Fin 1)) g) :=
    MorphismProperty.of_isPullback (P := @WeaklyEtale) sq.flip inferInstance
  have h := isIso_baseChangeMap_of_weaklyEtale Λ sq
  rw [baseChangeMap] at h
  exact Adjunction.isIso_map_unit_app_iff_of_isIso_exchangeRight_app _ _
    (pullbackSquareComparison Λ sq.toCommSq) K

/-- **The unit of the affine line is pro-étale local**: the unit `K ⟶ Rp_{X*} Lp_X^* K` of the
affine line over `X` is invertible as soon as the units of the affine lines over the members
`gᵢ : Uᵢ ⟶ X` of a pro-étale cover are invertible at the pullbacks `Lgᵢ^* K`. -/
lemma isIso_affineLineUnit_app_of_cover {X : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h : ∀ i, IsIso ((derivedUpperStarLowerStarAdjunction Λ
      (𝔸(ULift.{u} (Fin 1); 𝒰.X i) ↘ 𝒰.X i)).unit.app ((L((𝒰.f i)^*⟦Λ⟧)).obj K))) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ (𝔸(ULift.{u} (Fin 1); X) ↘ X)).unit.app K) :=
  isIso_of_forall_isIso_leftDerivedUpperStar_map 𝒰 _ fun i ↦
    have : WeaklyEtale (𝒰.f i) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
    (isIso_leftDerivedUpperStar_map_affineLineUnit_app_iff Λ (𝒰.f i) K).2 (h i)

/-- The Zariski form of `ProEtale.CondensedRing.isIso_affineLineUnit_app_of_cover`: the unit of
the affine line over `X` is invertible at `K` as soon as the units of the affine lines over the
members `jᵢ : Uᵢ ⟶ X` of an open cover are invertible at the restrictions `Ljᵢ^* K`. -/
lemma isIso_affineLineUnit_app_of_openCover {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} X)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h : ∀ i, IsIso ((derivedUpperStarLowerStarAdjunction Λ
      (𝔸(ULift.{u} (Fin 1); 𝒰.X i) ↘ 𝒰.X i)).unit.app ((L((𝒰.f i)^*⟦Λ⟧)).obj K))) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ (𝔸(ULift.{u} (Fin 1); X) ↘ X)).unit.app K) :=
  isIso_affineLineUnit_app_of_cover Λ
    (𝒰.weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage) K h

/-- If the unit of the affine line over `X` is invertible at the unit object `Λ_X`, then so is
the unit of the affine line over `W` at `Λ_W`, for every weakly étale `g : W ⟶ X`: `Lg^* Λ_X ≅
Λ_W`. -/
lemma isIso_affineLineUnit_app_tensorUnit_of_weaklyEtale {W X : Scheme.{u}} (g : W ⟶ X)
    [WeaklyEtale g]
    [IsIso ((derivedUpperStarLowerStarAdjunction Λ (𝔸(ULift.{u} (Fin 1); X) ↘ X)).unit.app
      (𝟙_ _))] :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ (𝔸(ULift.{u} (Fin 1); W) ↘ W)).unit.app
      (𝟙_ _)) := by
  have h := (isIso_leftDerivedUpperStar_map_affineLineUnit_app_iff Λ g (𝟙_ _)).1 inferInstance
  exact (NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarUnitIso Λ g)).1 h

/-- **Homotopy invariance for locally free module objects from the constant case.** Let `M` be a
module object over `Λ_X` which is pro-étale locally a finite direct sum of copies of `Λ`: there is
a pro-étale cover `gᵢ : Uᵢ ⟶ X` with `gᵢ^* M ≅ Λ_{Uᵢ}^{nᵢ}`. If the unit of the affine line over
`X` is invertible at `Λ_X`, it is invertible at `M` placed in degree `0`. -/
theorem isIso_affineLineUnit_app_singleFunctor_of_cover {X : Scheme.{u}}
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hM : ∀ i, ∃ n : ℕ, Nonempty ((𝒰.f i)^*⟦Λ⟧.obj M ≅ ⨁ fun _ : Fin n ↦ 𝟙_ _))
    [IsIso ((derivedUpperStarLowerStarAdjunction Λ (𝔸(ULift.{u} (Fin 1); X) ↘ X)).unit.app
      (𝟙_ _))] :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ (𝔸(ULift.{u} (Fin 1); X) ↘ X)).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  refine isIso_affineLineUnit_app_of_cover Λ 𝒰 _ fun i ↦ ?_
  have : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  have := isIso_affineLineUnit_app_tensorUnit_of_weaklyEtale Λ (𝒰.f i)
  obtain ⟨n, ⟨e⟩⟩ := hM i
  let S := DerivedCategory.singleFunctor
    (Mod (Sheaf (ProEt.topology (𝒰.X i)) Ab.{u + 1}) (condensedRingObj Λ (𝒰.X i))) 0
  let e' : (L((𝒰.f i)^*⟦Λ⟧)).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      ⨁ fun _ : Fin n ↦ 𝟙_ _ :=
    (leftDerivedUpperStarIsoMapDerivedCategory Λ (𝒰.f i)).app _ ≪≫
      ((𝒰.f i)^*⟦Λ⟧.mapDerivedCategorySingleFunctor 0).app M ≪≫ S.mapIso e ≪≫
      S.mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ DerivedCategory.singleFunctorObjUnitIso _
  rw [NatTrans.isIso_app_iff_of_iso _ e']
  exact NatTrans.isIso_app_biproduct _ _ fun _ ↦ inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing

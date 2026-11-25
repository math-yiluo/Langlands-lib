/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import WeilConjectures.AlgebraicGeometry.FreeParameterScalarMaps
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

set_option linter.privateModule false

/-! # Normalized non-flat derived pullback comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

private instance scalarSixRing_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X :=
  Λ.comm

private instance scalarSixMap_isMonHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

private def scalarSixScalarAdjunction {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (Z : Scheme.{u}) :
    scalarSixChange a Z ⊣
      (Mod.comap (D := Sheaf (ProEt.topology Z) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).mapDerivedCategory :=
  Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)

set_option maxHeartbeats 100000 in
-- Keep the derived adjunction data folded in this component comparison.
private theorem scalarSixPullHom_isIso_app {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    IsIso ((scalarSixPullHom a f).app K) := by
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  have he : (scalarSixPullHom a f).app K =
      FreeParameterEvaluation.scalarPullComparison
        (Mon.mk Λ.X) (Mon.mk Λ'.X) a.hom.hom f K := by
    dsimp only [scalarSixPullHom, scalarSixChange, scalarSixAdjunctionLeft,
      scalarSixPull,
      FreeParameterEvaluation.scalarPullComparison, Adjunction.pushHomOfComapIso]
  rw [he]
  exact FreeParameterEvaluation.scalarPullComparison_isIso
    (Mon.mk Λ.X) (Mon.mk Λ'.X) a.hom.hom f K

@[reducible] private def scalarSixOrdinaryRestrictionTower
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (Z : Scheme.{u}) :
    Mod.comap (D := Sheaf (ProEt.topology Z) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom Z) ≅
      Mod.comap (D := Sheaf (ProEt.topology Z) Ab.{u + 1})
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom Z) ⋙
        Mod.comap (D := Sheaf (ProEt.topology Z) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z) :=
  Mod.comapCongr (C := Sheaf (ProEt.topology Z) Ab.{u + 1})
        (coefficientMap_comp (Λ := Λ.X) (Λ' := Λ'.X) (Λ'' := Λ''.X)
    a.hom.hom b.hom.hom Z) ≪≫
    Mod.comapComp (C := Sheaf (ProEt.topology Z) Ab.{u + 1})
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)
      (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom Z)

private theorem scalarSixComapCongr_inv_hom
    {V : Type*} [Category V] [MonoidalCategory V]
    {A B : V} [MonObj A] [MonObj B] {f g : A ⟶ B}
    [IsMonHom f] [IsMonHom g] (h : f = g) (M : Mod V B) :
    ((Mod.comapCongr h).inv.app M).hom = 𝟙 M.X := by
  rfl

private theorem scalarSixHorizontalMateTower
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {L₀ : A₀ ⥤ B₀} {L₁ : A₁ ⥤ B₁} {L₂ : A₂ ⥤ B₂}
    {R₀ : B₀ ⥤ A₀} {R₁ : B₁ ⥤ A₁} {R₂ : B₂ ⥤ A₂}
    (s₀ : L₀ ⊣ R₀) (s₁ : L₁ ⊣ R₁) (s₂ : L₂ ⊣ R₂)
    {U₀₁ : A₀ ⥤ A₁} {U₁₂ : A₁ ⥤ A₂} {U₀₂ : A₀ ⥤ A₂}
    {V₀₁ : B₀ ⥤ B₁} {V₁₂ : B₁ ⥤ B₂} {V₀₂ : B₀ ⥤ B₂}
    (α : TwoSquare U₀₁ L₀ L₁ V₀₁) (β : TwoSquare U₁₂ L₁ L₂ V₁₂)
    (δ : TwoSquare U₀₂ L₀ L₂ V₀₂)
    (d₀₁ : TwoSquare R₀ V₀₁ U₀₁ R₁)
    (d₁₂ : TwoSquare R₁ V₁₂ U₁₂ R₂)
    (d₀₂ : TwoSquare R₀ V₀₂ U₀₂ R₂)
    (h₀₁ : mateEquiv s₀ s₁ α = d₀₁)
    (h₁₂ : mateEquiv s₁ s₂ β = d₁₂)
    (h₀₂ : mateEquiv s₀ s₂ δ = d₀₂)
    (tY : U₀₂ ≅ U₀₁ ⋙ U₁₂) (tX : V₀₂ ≅ V₀₁ ⋙ V₁₂)
    (hd : TwoSquare.vComp d₀₁ d₁₂ =
      (d₀₂.whiskerRight tY.inv).whiskerLeft tX.hom) (N : A₀) :
    L₂.map (tY.hom.app N) ≫ β.app (U₀₁.obj N) ≫ V₁₂.map (α.app N) =
      δ.app N ≫ tX.hom.app (L₀.obj N) := by
  have h : TwoSquare.hComp α β =
      (δ.whiskerTop tY.inv).whiskerBottom tX.hom := by
    apply (mateEquiv s₀ s₂).injective
    rw [mateEquiv_vcomp s₀ s₁ s₂, mateEquiv_whiskerTop_whiskerBottom,
      h₀₁, h₁₂, h₀₂]
    exact hd
  have hN := congrArg (fun q ↦ q.app N) h
  simp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hN
  have hh := congrArg (fun z ↦ L₂.map (tY.hom.app N) ≫ z) hN
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at hh
  rw [L₂.map_id (U₀₂.obj N), Category.id_comp] at hh
  exact hh

set_option maxHeartbeats 30000 in
-- Bound elaboration while keeping the geometric adjunction data folded.
private theorem scalarSixOrdinaryRestrictionTowerSquare
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ModuleRingedComparison.internalModules Λ''.X Y) :
    (upperStar Λ.X f).map ((scalarSixOrdinaryRestrictionTower a b Y).hom.app N) ≫
        (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom Y)).obj N) ≫
        (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).map
          ((comapUpperStarIso (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom f).inv.app N) =
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom f).inv.app N ≫
        (scalarSixOrdinaryRestrictionTower a b X).hom.app ((upperStar Λ''.X f).obj N) := by
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsMonHom b.hom.hom := b.hom.isMonHom_hom
  have : IsMonHom (a ≫ b).hom.hom := (a ≫ b).hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  have : IsCommMonObj Λ''.X := Λ''.comm
  apply scalarSixHorizontalMateTower
    (upperStarLowerStarAdjunction Λ''.X f)
    (upperStarLowerStarAdjunction Λ'.X f) (upperStarLowerStarAdjunction Λ.X f)
    (.mk _ _ _ _ (comapUpperStarIso (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom f).inv)
    (.mk _ _ _ _ (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)
    (.mk _ _ _ _ (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom f).inv)
    (.mk _ _ _ _ (comapLowerStarIso (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom f).hom)
    (.mk _ _ _ _ (comapLowerStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).hom)
    (.mk _ _ _ _ (comapLowerStarIso (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom f).hom)
    (comapUpperStarIso_mate (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom f)
    (comapUpperStarIso_mate (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)
    (comapUpperStarIso_mate (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom f)
    (scalarSixOrdinaryRestrictionTower a b Y) (scalarSixOrdinaryRestrictionTower a b X)
    ?_ N
  refine NatTrans.ext (funext fun M ↦ ?_)
  apply Mod.hom_ext
  simp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Mod.comp_hom',
    Mod.id_hom', Mod.comap_map_hom, Functor.comp_obj,
    comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom]
  simp only [scalarSixOrdinaryRestrictionTower, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Mod.comp_hom', Mod.comapComp_hom_app_hom,
    Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom,
    scalarSixComapCongr_inv_hom, lowerStar_map_hom]
  change 𝟙 ((f)_*[Ab.{u + 1}].obj M.X) ≫ 𝟙 _ =
    ((𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _) ≫ (f)_*[Ab.{u + 1}].map (𝟙 M.X ≫ 𝟙 M.X)
  simp only [Category.id_comp]
  exact ((f)_*[Ab.{u + 1}].map_id M.X).symm

private theorem scalarSixDerivedSquare_symm
    {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory E]
    {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (q : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    Functor.mapDerivedCategorySquareIso q.symm =
      (Functor.mapDerivedCategorySquareIso q).symm := by
  apply Iso.ext
  exact Functor.square_symm_hom q

private theorem scalarSixDerivedRestrictionTowerSquare
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso (scalarSixOrdinaryRestrictionTower a b Y) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm) (scalarSixPull Λ f) ≪≫
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (Mod.comap (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X)
            b.hom.hom Y)).mapDerivedCategory
          (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (derivedComapUpperStarIso (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom f).symm
          (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategory ≪≫
        Functor.associator _ _ _) =
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom f).symm ≪≫
        Functor.isoWhiskerLeft (scalarSixPull Λ'' f)
          (Functor.mapDerivedCategoryNatIso (scalarSixOrdinaryRestrictionTower a b X) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm) := by
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsMonHom b.hom.hom := b.hom.isMonHom_hom
  have : IsMonHom (a ≫ b).hom.hom := (a ≫ b).hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  have : IsCommMonObj Λ''.X := Λ''.comm
  simpa only [derivedComapUpperStarIso, scalarSixPull,
    scalarSixDerivedSquare_symm, Functor.mapDerivedCategorySquareIso] using
    Functor.mapDerivedCategorySquareIso_comp
    (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom Y))
    (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y))
    (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom Y))
    (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (coefficientMap (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom X))
    (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))
    (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom X))
    (upperStar Λ''.X f) (upperStar Λ'.X f) (upperStar Λ.X f)
    (comapUpperStarIso (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom f).symm
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom f).symm
    (scalarSixOrdinaryRestrictionTower a b Y) (scalarSixOrdinaryRestrictionTower a b X)
    (scalarSixOrdinaryRestrictionTowerSquare a b f)

attribute [local irreducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  Mod.derivedExtendRestrictAdjunction Mod.extendScalars

set_option maxHeartbeats 30000 in
-- Bound elaboration while keeping the scalar adjunction data folded.
attribute [local semireducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  Mod.derivedExtendRestrictAdjunction Mod.extendScalars

end AlgebraicGeometry.ProEtale.CondensedRing

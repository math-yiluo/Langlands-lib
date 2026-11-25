/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterScalarMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.ComapUpperStarIsoComposition
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
public import WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization

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

private theorem scalarSixDerivedNatIso_trans
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso d := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_trans e d

private theorem scalarSixMateTower
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {L₀₁ : A₀ ⥤ A₁} {L₁₂ : A₁ ⥤ A₂} {L₀₂ : A₀ ⥤ A₂}
    {U₀₁ : A₁ ⥤ A₀} {U₁₂ : A₂ ⥤ A₁} {U₀₂ : A₂ ⥤ A₀}
    {M₀₁ : B₀ ⥤ B₁} {M₁₂ : B₁ ⥤ B₂} {M₀₂ : B₀ ⥤ B₂}
    {V₀₁ : B₁ ⥤ B₀} {V₁₂ : B₂ ⥤ B₁} {V₀₂ : B₂ ⥤ B₀}
    (aY : L₀₁ ⊣ U₀₁) (bY : L₁₂ ⊣ U₁₂) (cY : L₀₂ ⊣ U₀₂)
    (aX : M₀₁ ⊣ V₀₁) (bX : M₁₂ ⊣ V₁₂) (cX : M₀₂ ⊣ V₀₂)
    (F₀ : A₀ ⥤ B₀) (F₁ : A₁ ⥤ B₁) (F₂ : A₂ ⥤ B₂)
    (e₀₁ : F₁ ⋙ V₀₁ ≅ U₀₁ ⋙ F₀)
    (e₁₂ : F₂ ⋙ V₁₂ ≅ U₁₂ ⋙ F₁)
    (e₀₂ : F₂ ⋙ V₀₂ ≅ U₀₂ ⋙ F₀)
    (tY : U₀₂ ≅ U₁₂ ⋙ U₀₁) (tX : V₀₂ ≅ V₁₂ ⋙ V₀₁)
    (ht : Functor.isoWhiskerRight tY F₀ ≪≫
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft U₁₂ e₀₁.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e₁₂.symm V₀₁ ≪≫ Functor.associator _ _ _) =
      e₀₂.symm ≪≫ Functor.isoWhiskerLeft F₂ tX) (K : A₀) :
    ((conjugateIsoEquiv cX (aX.comp bX)).symm tX).hom.app (F₀.obj K) ≫
        (Adjunction.pushHomOfComapIso cY cX e₀₂).app K =
      M₁₂.map ((Adjunction.pushHomOfComapIso aY aX e₀₁).app K) ≫
        (Adjunction.pushHomOfComapIso bY bX e₁₂).app (L₀₁.obj K) ≫
          F₂.map (((conjugateIsoEquiv cY (aY.comp bY)).symm tY).hom.app K) := by
  let α := TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso aY aX e₀₁)
  let β := TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso bY bX e₁₂)
  let δ := TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso cY cX e₀₂)
  let τY := (conjugateIsoEquiv cY (aY.comp bY)).symm tY
  let τX := (conjugateIsoEquiv cX (aX.comp bX)).symm tX
  have h : (TwoSquare.vComp α β).whiskerLeft τY.hom =
      δ.whiskerRight τX.hom := by
    apply (mateEquiv cY (aX.comp bX)).injective
    rw [conjugateEquiv_mateEquiv_vcomp cY (aY.comp bY) (aX.comp bX),
      mateEquiv_conjugateEquiv_vcomp cY cX (aX.comp bX),
      mateEquiv_hcomp aY aX bY bX]
    simp only [α, β, δ, Adjunction.pushHomOfComapIso,
      Equiv.apply_symm_apply, τY, τX, conjugateIsoEquiv_symm_apply_hom]
    refine NatTrans.ext (funext fun M ↦ ?_)
    have hh := congrArg (fun e ↦ e.hom.app M) ht
    simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hh
  have hK := congrArg (fun q ↦ q.app K) h
  simpa only [α, β, δ, τX, τY, TwoSquare.vComp, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.assoc, Category.id_comp, Category.comp_id] using hK.symm

attribute [local irreducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  Mod.derivedExtendRestrictAdjunction Mod.extendScalars

set_option maxHeartbeats 30000 in
-- Bound elaboration while keeping the scalar adjunction data folded.
private theorem scalarSixPullHomTower
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixTower a b X).hom.app ((scalarSixPull Λ f).obj K) ≫
        (scalarSixPullHom (a ≫ b) f).app K =
      (scalarSixChange b X).map ((scalarSixPullHom a f).app K) ≫
        (scalarSixPullHom b f).app ((scalarSixChange a Y).obj K) ≫
          (scalarSixPull Λ'' f).map ((scalarSixTower a b Y).hom.app K) := by
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsMonHom b.hom.hom := b.hom.isMonHom_hom
  have : IsMonHom (a ≫ b).hom.hom := (a ≫ b).hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  have : IsCommMonObj Λ''.X := Λ''.comm
  have ht := scalarSixDerivedRestrictionTowerSquare a b f
  simp only [scalarSixOrdinaryRestrictionTower,
    scalarSixDerivedNatIso_trans, Iso.trans_assoc] at ht
  dsimp only [scalarSixTower, scalarSixPullHom]
  exact scalarSixMateTower
    (scalarSixScalarAdjunction a Y) (scalarSixScalarAdjunction b Y)
    (scalarSixScalarAdjunction (a ≫ b) Y)
    (scalarSixScalarAdjunction a X) (scalarSixScalarAdjunction b X)
    (scalarSixScalarAdjunction (a ≫ b) X)
    (scalarSixPull Λ f) (scalarSixPull Λ' f) (scalarSixPull Λ'' f)
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)
    (derivedComapUpperStarIso (Λ := Λ'.X) (Λ' := Λ''.X) b.hom.hom f)
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ''.X) (a ≫ b).hom.hom f)
    _ _ ht K

private theorem scalarSixTransposePasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (S₀ : A₀ ⥤ B₀) (S₁ : A₁ ⥤ B₁) (S₂ : A₂ ⥤ B₂)
    (U₀ : B₀ ⥤ A₀) (U₁ : B₁ ⥤ A₁) (U₂ : B₂ ⥤ A₂)
    (a₀ : S₀ ⊣ U₀) (a₁ : S₁ ⊣ U₁) (a₂ : S₂ ⊣ U₂)
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (P : B₀ ⥤ B₁) (Q : B₁ ⥤ B₂)
    (r₀₁ : F ⋙ S₁ ⟶ S₀ ⋙ P) (r₁₂ : G ⋙ S₂ ⟶ S₁ ⋙ Q)
    (d₀₁ : U₀ ⋙ F ⟶ P ⋙ U₁) (d₁₂ : U₁ ⋙ G ⟶ Q ⋙ U₂)
    (N : A₀)
    (h₀₁ : a₁.unit.app (F.obj N) ≫ U₁.map (r₀₁.app N) =
      F.map (a₀.unit.app N) ≫ d₀₁.app (S₀.obj N))
    (h₁₂ : a₂.unit.app (G.obj (F.obj N)) ≫ U₂.map (r₁₂.app (F.obj N)) =
      G.map (a₁.unit.app (F.obj N)) ≫ d₁₂.app (S₁.obj (F.obj N))) :
    a₂.unit.app (G.obj (F.obj N)) ≫
        U₂.map (r₁₂.app (F.obj N) ≫ Q.map (r₀₁.app N)) =
      G.map (F.map (a₀.unit.app N)) ≫
        G.map (d₀₁.app (S₀.obj N)) ≫ d₁₂.app (P.obj (S₀.obj N)) := by
  have hn := d₁₂.naturality (r₀₁.app N)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Functor.map_comp]
  rw [reassoc_of% h₁₂, ← hn, ← G.map_comp_assoc, h₀₁, G.map_comp, Category.assoc]

private theorem scalarSixReverseComposition
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (S₀ : A₀ ⥤ B₀) (S₁ : A₁ ⥤ B₁) (S₂ : A₂ ⥤ B₂)
    (U₀ : B₀ ⥤ A₀) (U₁ : B₁ ⥤ A₁) (U₂ : B₂ ⥤ A₂)
    (a₀ : S₀ ⊣ U₀) (a₁ : S₁ ⊣ U₁) (a₂ : S₂ ⊣ U₂)
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (H : A₀ ⥤ A₂)
    (P : B₀ ⥤ B₁) (Q : B₁ ⥤ B₂) (R : B₀ ⥤ B₂)
    (r₀₁ : F ⋙ S₁ ⟶ S₀ ⋙ P) (r₁₂ : G ⋙ S₂ ⟶ S₁ ⋙ Q)
    (r₀₂ : H ⋙ S₂ ⟶ S₀ ⋙ R)
    (d₀₁ : U₀ ⋙ F ⟶ P ⋙ U₁) (d₁₂ : U₁ ⋙ G ⟶ Q ⋙ U₂)
    (d₀₂ : U₀ ⋙ H ⟶ R ⋙ U₂) (a : H ≅ F ⋙ G) (b : R ≅ P ⋙ Q)
    (N : A₀)
    (h₀₁ : a₁.unit.app (F.obj N) ≫ U₁.map (r₀₁.app N) =
      F.map (a₀.unit.app N) ≫ d₀₁.app (S₀.obj N))
    (h₁₂ : a₂.unit.app (G.obj (F.obj N)) ≫ U₂.map (r₁₂.app (F.obj N)) =
      G.map (a₁.unit.app (F.obj N)) ≫ d₁₂.app (S₁.obj (F.obj N)))
    (h₀₂ : a₂.unit.app (H.obj N) ≫ U₂.map (r₀₂.app N) =
      H.map (a₀.unit.app N) ≫ d₀₂.app (S₀.obj N))
    (hd : d₀₂.app (S₀.obj N) ≫ U₂.map (b.hom.app (S₀.obj N)) =
      a.hom.app (U₀.obj (S₀.obj N)) ≫
        G.map (d₀₁.app (S₀.obj N)) ≫ d₁₂.app (P.obj (S₀.obj N))) :
    S₂.map (a.hom.app N) ≫ r₁₂.app (F.obj N) ≫ Q.map (r₀₁.app N) =
      r₀₂.app N ≫ b.hom.app (S₀.obj N) := by
  apply (a₂.homEquiv _ _).injective
  conv_lhs => rw [a₂.homEquiv_naturality_left]
  conv_rhs => rw [a₂.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit, Functor.comp_obj]
  rw [scalarSixTransposePasting S₀ S₁ S₂ U₀ U₁ U₂ a₀ a₁ a₂ F G P Q
    r₀₁ r₁₂ d₀₁ d₁₂ N h₀₁ h₁₂, h₀₂]
  rw [Category.assoc, hd]
  have hn := a.hom.naturality (a₀.unit.app N)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map] at hn
  simpa only [Functor.id_obj, Functor.comp_obj, Category.assoc] using congrArg
    (fun t ↦ t ≫ G.map (d₀₁.app (S₀.obj N)) ≫ d₁₂.app (P.obj (S₀.obj N))) hn.symm

attribute [local semireducible] Mod.derivedExtendMapDerivedCategoryAdjunction
  Mod.derivedExtendRestrictAdjunction Mod.extendScalars

set_option maxHeartbeats 70000 in
-- The kernel checks the concrete exact-square specialization, including its typeclass data.
private theorem scalarSixRestrictionComp
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ'.X W)) :
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (f ≫ g)).inv.app N ≫
        (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategory.map
          ((scalarSixPullComp Λ' f g).hom.app N) =
      (scalarSixPullComp Λ f g).hom.app
          ((Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom W)).mapDerivedCategory.obj N) ≫
        (scalarSixPull Λ f).map ((derivedComapUpperStarIso
          (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom g).inv.app N) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixPull Λ' g).obj N) := by
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  have hq (M : ModuleRingedComparison.internalModules Λ'.X W) :
      (upperStar Λ.X f).map ((comapUpperStarIso
          (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom g).inv.app M) ≫
        (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((upperStar Λ'.X g).obj M) =
      (upperStarComp Λ.X f g).inv.app
          ((Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
            (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom W)).obj M) ≫
        (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (f ≫ g)).inv.app M ≫
        (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).map
            ((upperStarComp Λ'.X f g).hom.app M) := by
    have h := comapUpperStarIso_comp (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f g M
    have hi := Functor.square_reverse (upperStar Λ.X f)
      ((upperStarComp Λ.X f g).app
        ((Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom W)).obj M))
      ((comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).app
        ((upperStar Λ'.X g).obj M))
      ((comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom g).app M)
      ((comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (f ≫ g)).inv.app M ≫
        (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).map
            ((upperStarComp Λ'.X f g).hom.app M)) (𝟙 _) (by
              simpa only [Category.assoc, Category.comp_id, Iso.app_hom,
                Functor.comp_obj] using h.symm)
    simpa only [Category.assoc, Category.id_comp, Iso.app_inv,
      Functor.comp_obj] using hi.symm
  simpa only [derivedComapUpperStarIso, scalarSixPullComp, scalarSixPull,
    scalarSixDerivedSquare_symm, Iso.symm_hom] using
    Functor.exactSquare_comp_inverse
      (upperStar Λ'.X g) (upperStar Λ'.X f) (upperStar Λ'.X (f ≫ g))
      (upperStar Λ.X g) (upperStar Λ.X f) (upperStar Λ.X (f ≫ g))
      (Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom W))
      (Mod.comap (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y))
      (Mod.comap (D := Sheaf (ProEt.topology X) Ab.{u + 1})
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom g).symm
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (f ≫ g)).symm
      (upperStarComp Λ'.X f g) (upperStarComp Λ.X f g)
      (fun M ↦ by
        have hh := hq M
        have he := congrArg (fun z ↦
          (upperStarComp Λ.X f g).hom.app
            ((Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
              (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom W)).obj M) ≫ z) hh
        simpa only [Category.assoc, Iso.hom_inv_id_app_assoc,
          Iso.symm_hom, Functor.comp_obj] using he.symm) N

set_option maxHeartbeats 30000 in
-- Bound elaboration while keeping the scalar adjunction data folded.
private theorem scalarSixPullHomComp
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :
    (scalarSixPullHom a (f ≫ g)).app K ≫
        (scalarSixPullComp Λ' f g).hom.app ((scalarSixChange a W).obj K) =
      (scalarSixChange a X).map ((scalarSixPullComp Λ f g).hom.app K) ≫
        (scalarSixPullHom a f).app ((scalarSixPull Λ g).obj K) ≫
          (scalarSixPull Λ' f).map ((scalarSixPullHom a g).app K) := by
  have : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  let adj (Z : Scheme.{u}) := scalarSixScalarAdjunction a Z
  dsimp only [scalarSixPullHom]
  exact (scalarSixReverseComposition _ _ _ _ _ _ (adj W) (adj Y) (adj X)
    (scalarSixPull Λ g) (scalarSixPull Λ f) (scalarSixPull Λ (f ≫ g))
    (scalarSixPull Λ' g) (scalarSixPull Λ' f) (scalarSixPull Λ' (f ≫ g))
    (scalarSixPullHom a g) (scalarSixPullHom a f) (scalarSixPullHom a (f ≫ g))
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom g).inv
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (f ≫ g)).inv
    (scalarSixPullComp Λ f g) (scalarSixPullComp Λ' f g) K
    (unit_mateEquiv_symm (adj W) (adj Y) (.mk _ _ _ _
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom g).inv) K).symm
    (unit_mateEquiv_symm (adj Y) (adj X) (.mk _ _ _ _
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)
          ((scalarSixPull Λ g).obj K)).symm
    (unit_mateEquiv_symm (adj W) (adj X) (.mk _ _ _ _
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (f ≫ g)).inv) K).symm
    (scalarSixRestrictionComp a f g ((scalarSixChange a W).obj K))).symm

/-- The canonical non-flat scalar mate is invertible and satisfies both coherences.

Source: blueprint det-prop-scalar-six-pullback.proof.md, (1) and (3);
Stacks, Cohomology on Sites, Tags 0G7E and 0D6D.
(blueprint: lem-sfb-scalar-six-derived-pullback-normalization).

Proof: the generic inverse-mate unit formula identifies each component of the specified
scalarSixPullHom with the existing free-parameter scalar pullback comparison. Its
non-flat invertibility theorem therefore makes scalarSixPullHom invertible. Use asIso
for theta, so its normalization is reflexivity. For geometric composition, use the
ordinary comapUpperStarIso composition equation and exact derived square composition.
The unit-mate pasting calculation transposes this to the displayed theta composition
law. For a coefficient tower, take geometric mates of the ordinary restriction
comparisons. Their direct-image mates and the restriction compositor have identity
underlying sheaf maps, so faithfulness of the module forgetful functor proves their
pasting equation. Apply exact derived square composition and then scalar mates. The
conjugate of derived restriction transitivity is precisely scalarSixTower by its
definition. Thus its square is the required theta/tower equation. -/
theorem scalarSixPullbackData_exists : Nonempty ScalarSixPullbackData.{u} := by
  have (Λ Λ' : ScalarSixRing.{u}) (a : Λ ⟶ Λ') (X Y : Scheme.{u}) (f : X ⟶ Y) :
      IsIso (scalarSixPullHom a f) := by
    have (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :=
      scalarSixPullHom_isIso_app a f K
    exact NatIso.isIso_of_isIso_app _
  exact ⟨{
    theta := fun a _ _ f ↦ asIso (scalarSixPullHom a f)
    thetaNormalization := fun _ _ _ _ ↦ rfl
    composition := scalarSixPullHomComp
    tower := scalarSixPullHomTower }⟩

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian

/-! # Internal Hom and weakly etale coefficient pullback

Source: the localization calculation for internal Hom, blueprint stratum Hom step 3.
(blueprint: lem-proetale-pullback-internal-hom)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

attribute [local irreducible] Mod.monoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing
universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
private noncomputable def concreteIhomIso
    (R : C) [MonObj R] [IsCommMonObj R] (M : Mod C R) :
    ihom M ≅ Mod.ihom' R M :=
  (ihom.adjunction M).rightAdjointUniq
    ((Mod.ihom'Adjunction R M).ofNatIsoLeft
      (Mod.relativeTensorRightIso M ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight M).symm))

omit [MonoidalPreadditive C] in
private lemma tensorπ_concreteTensorIso
    (R : C) [MonObj R] [IsCommMonObj R]
    (M P : Mod C R) :
    (Mod.tensorLeftπ M P).hom ≫ ((Mod.relativeTensorRightIso M).hom.app P).hom =
      Mod.tensorObjπ P M := by
  change (Mod.tensorLeftπ M P ≫ (Mod.relativeTensorRightIso M).hom.app P).hom = _
  have h : Mod.tensorLeftπ M P ≫ (Mod.relativeTensorRightIso M).hom.app P =
      Mod.relativeTensorπ P M := by
    change colimit.ι _ WalkingParallelPair.one ≫
      (HasColimit.isoOfNatIso _ ≪≫ _).hom = _
    simp only [Iso.trans_hom]
    erw [HasColimit.ι_isoOfNatIso_hom_assoc,
      IsColimit.comp_coconePointUniqueUpToIso_hom]
    simp [diagramIsoParallelPair, Mod.relativeTensorCofork]
  exact congrArg Mod.Hom.hom h

omit [MonoidalPreadditive C] in
private lemma concreteIhomIso_embedding
    (R : C) [MonObj R] [IsCommMonObj R]
    (M N : Mod C R) :
    ((concreteIhomIso R M).hom.app N).hom ≫
      (equalizer.ι (Mod.homModPre (Mod.act M.X) N) (Mod.homModB R M N)).hom =
      curry (Mod.tensorObjπ M ((ihom M).obj N) ≫ ((ihom.ev M).app N).hom) := by
  have h := (ihom.adjunction M).homEquiv_symm_rightAdjointUniq_hom_app
    ((Mod.ihom'Adjunction R M).ofNatIsoLeft
      (Mod.relativeTensorRightIso M ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight M).symm)) N
  have h' := congrArg
    (((Mod.ihom'Adjunction R M).ofNatIsoLeft
      (Mod.relativeTensorRightIso M ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight M).symm)).homEquiv _ _) h
  simp only [Equiv.apply_symm_apply, Adjunction.homEquiv_ofNatIsoLeft_apply] at h'
  change (concreteIhomIso R M).hom.app N = _ at h'
  rw [h']
  simp only [Mod.ihom'Adjunction, Adjunction.mkOfHomEquiv_homEquiv, Equiv.coe_fn_mk]
  rw [Mod.ihomLift_hom_comp_ι]
  congr 1
  simp only [Mod.comp_hom', Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  change (β_ M.X ((ihom M).obj N).X).hom ≫
    (Mod.tensorLeftπ M ((ihom M).obj N)).hom ≫
    ((Mod.relativeTensorRightIso M).hom.app _).hom ≫
    (β_ M ((ihom M).obj N)).inv.hom ≫ ((ihom.ev M).app N).hom = _
  rw [reassoc_of% tensorπ_concreteTensorIso R M ((ihom M).obj N)]
  have hb : Mod.tensorObjπ ((ihom M).obj N) M ≫
      (β_ M ((ihom M).obj N)).inv.hom =
      (β_ M.X ((ihom M).obj N).X).inv ≫ Mod.tensorObjπ M ((ihom M).obj N) := by
    rw [← cancel_mono ((β_ M ((ihom M).obj N)).hom.hom)]
    rw [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id, Mod.id_hom', Category.comp_id]
    change _ = _ ≫ Mod.braidingHomX M ((ihom M).obj N)
    rw [Category.assoc, Mod.tensorObjπ_braidingHomX, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hb, Iso.hom_inv_id_assoc]
private noncomputable def pullbackConcreteIhomIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f] (M : supportModules Λ Y) :
    ihom M ⋙ supportPullback Λ f ≅
      supportPullback Λ f ⋙ ihom ((supportPullback Λ f).obj M) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  let F := supportPullback Λ f
  have : ∀ Z, IsIso (Functor.LaxMonoidal.ihomComparison G Z) :=
    ProEtale.isIso_ihomComparison_upperStar Ab.{u + 1} f
  have (N : supportModules Λ Y) : PreservesLimit
      (parallelPair (Mod.homModPre (Mod.act M.X) N)
        (Mod.homModB (condensedRingObj Λ Y) M N)) (G.mapMod _ ⋙ Mod.comap ρ) :=
    inferInstanceAs (PreservesLimit _ (supportPullback Λ f))
  exact Functor.isoWhiskerRight (concreteIhomIso _ M) F ≪≫
    NatIso.ofComponents (F := Mod.ihom' _ M ⋙ F)
      (G := F ⋙ Mod.ihom' _ (F.obj M)) (fun N ↦
      have := Mod.isIso_mapIhom'Hom G ρ M N
      asIso (Mod.mapIhom'Hom G ρ M N))
      (fun g ↦ Mod.mapIhom'Hom_naturality _ _ M g) ≪≫
    Functor.isoWhiskerLeft F (concreteIhomIso _ (F.obj M)).symm

private lemma pullbackConcreteIhomIso_embedding
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f] (M N : supportModules Λ Y) :
    let G := ProEtale.upperStar Ab.{u + 1} f
    let F := supportPullback Λ f
    ((pullbackConcreteIhomIso Λ f M).hom.app N).hom ≫
      ((concreteIhomIso _ (F.obj M)).hom.app (F.obj N)).hom ≫
        (equalizer.ι (Mod.homModPre (Mod.act (F.obj M).X) (F.obj N))
          (Mod.homModB _ (F.obj M) (F.obj N))).hom =
      G.map (((concreteIhomIso _ M).hom.app N).hom) ≫
        G.map ((equalizer.ι (Mod.homModPre (Mod.act M.X) N)
          (Mod.homModB _ M N)).hom) ≫
        (Functor.LaxMonoidal.ihomComparison G M.X).app N.X := by
  dsimp only
  have hc : (pullbackConcreteIhomIso Λ f M).hom.app N ≫
      (concreteIhomIso _ ((supportPullback Λ f).obj M)).hom.app
        ((supportPullback Λ f).obj N) =
    (supportPullback Λ f).map ((concreteIhomIso _ M).hom.app N) ≫
      Mod.mapIhom'Hom (ProEtale.upperStar Ab.{u + 1} f)
        (asIso (condensedPullbackHom Λ f)).inv M N := by
    simp [pullbackConcreteIhomIso]
  have hc' := congrArg (fun g ↦ (g ≫ equalizer.ι
    (Mod.homModPre (Mod.act ((supportPullback Λ f).obj M).X)
      ((supportPullback Λ f).obj N))
    (Mod.homModB _ ((supportPullback Λ f).obj M)
      ((supportPullback Λ f).obj N))).hom) hc
  simp only [Category.assoc] at hc'
  erw [Mod.mapIhom'Hom_ι (ProEtale.upperStar Ab.{u + 1} f)
    (asIso (condensedPullbackHom Λ f)).inv M N] at hc'
  simpa only [Mod.comp_hom', Mod.mapHomModHom_hom, supportPullback,
    Functor.comp_map, Functor.mapMod, Mod.comap, Mod.homMk] using hc'

/-- Coefficient inverse image is strong monoidal for the relative module tensor.
Source: blueprint stratum Hom lemma, proof step 3, restriction of evaluation.
(blueprint: lem-proetale-pullback-internal-hom). -/
noncomputable instance supportPullback_monoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (supportPullback Λ f).Monoidal := by
  unfold supportPullback
  infer_instance

private lemma supportPullback_tensorπ_μ
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : supportModules Λ Y) :
    Mod.tensorObjπ ((supportPullback Λ f).obj M) ((supportPullback Λ f).obj N) ≫
      (Functor.LaxMonoidal.μ (supportPullback Λ f) M N).hom =
        Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} f) M.X N.X ≫
          (ProEtale.upperStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  change Mod.tensorObjπ ((Mod.comap ρ).obj ((G.mapMod _).obj M))
      ((Mod.comap ρ).obj ((G.mapMod _).obj N)) ≫
    (Mod.comapTensorIso ρ ((G.mapMod _).obj M) ((G.mapMod _).obj N)).hom.hom ≫
      (G.mapModTensorIso M N).hom.hom = _
  rw [Mod.tensorπ_comapTensorIso_hom_hom_assoc,
    Functor.tensorπ_mapModTensorIso_hom_hom]

/-- Weakly etale restriction preserves the canonical internal-Hom comparison.
Source: blueprint stratum Hom lemma, step 3, restriction of sheaf Hom to the local site.
(blueprint: lem-proetale-pullback-internal-hom)

Proof: identify inverse image along f with restriction to the localized pro-etale site.
For each further weakly etale Y-scheme V, the over-category of V in that localized site
is equivalent to the over-category of its image in the original site. Thus restriction
commutes with the end defining internal Hom of abelian sheaves. Internal Hom of module
objects is the equalizer imposing linearity on that abelian internal Hom. Restriction
preserves this equalizer, since it preserves finite limits. Transporting the coefficient
ring along the canonical isomorphism alpha does not change the linearity equation.
The resulting isomorphism is the canonical internal-Hom comparison: uncurry it and
both maps are pullback of evaluation after the tensor comparison. This characterization
also proves naturality in the second module. No finite generation is needed here; the
argument applies on the empty site and to the zero coefficient ring. -/
theorem supportPullback_ihomComparison_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f] (M : supportModules Λ Y) :
    IsIso (Functor.LaxMonoidal.ihomComparison (supportPullback Λ f) M) := by
  let F := supportPullback Λ f
  let G := ProEtale.upperStar Ab.{u + 1} f
  have hcomp (N : supportModules Λ Y) :
      IsIso ((Functor.LaxMonoidal.ihomComparison F M).app N) := by
    let eX := (concreteIhomIso _ (F.obj M)).hom.app (F.obj N)
    let eY := (concreteIhomIso _ M).hom.app N
    let ιX := (equalizer.ι (Mod.homModPre (Mod.act (F.obj M).X) (F.obj N))
      (Mod.homModB _ (F.obj M) (F.obj N))).hom
    let ιY := (equalizer.ι (Mod.homModPre (Mod.act M.X) N)
      (Mod.homModB _ M N)).hom
    have heq : (Functor.LaxMonoidal.ihomComparison F M).app N =
        (pullbackConcreteIhomIso Λ f M).hom.app N := by
      apply (cancel_mono eX).mp
      apply (cancel_mono (equalizer.ι (Mod.homModPre (Mod.act (F.obj M).X) (F.obj N))
        (Mod.homModB _ (F.obj M) (F.obj N)))).mp
      apply Mod.hom_ext
      dsimp only [eX]
      simp only [Mod.comp_hom', Category.assoc]
      erw [pullbackConcreteIhomIso_embedding Λ f M N]
      erw [concreteIhomIso_embedding (condensedRingObj Λ X) (F.obj M) (F.obj N)]
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_curry, uncurry_eq,
        MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← Mod.tensorObjπ_whiskerLeft_assoc]
      rw [← Mod.comp_hom', Functor.LaxMonoidal.ihomComparison_ev, Mod.comp_hom']
      erw [reassoc_of% supportPullback_tensorπ_μ Λ f M ((ihom M).obj N)]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      erw [Functor.LaxMonoidal.ihomComparison_ev G M.X N.X]
      erw [Functor.LaxMonoidal.μ_natural_right_assoc G M.X
        (equalizer.ι (Mod.homModPre (Mod.act M.X) N)
          (Mod.homModB _ M N)).hom]
      erw [Functor.LaxMonoidal.μ_natural_right_assoc G M.X eY.hom]
      change _ = Functor.LaxMonoidal.μ G M.X ((ihom M).obj N).X ≫
        G.map (M.X ◁ eY.hom) ≫ G.map (M.X ◁ ιY) ≫ G.map ((ihom.ev M.X).app N.X)
      rw [← G.map_comp, ← G.map_comp]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← uncurry_eq]
      dsimp only [eY, ιY]
      rw [concreteIhomIso_embedding (condensedRingObj Λ Y) M N, uncurry_curry,
        G.map_comp]
      rfl
    rw [heq]
    infer_instance
  have := hcomp
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.ProEtale.CondensedRing

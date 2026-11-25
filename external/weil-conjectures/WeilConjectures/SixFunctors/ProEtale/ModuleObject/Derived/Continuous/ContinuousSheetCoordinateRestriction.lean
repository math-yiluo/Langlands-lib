/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeSumFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleLatticeSheetMaps
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.ComapUpperStarIsoComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-! # Restricting the forward coordinate equation to an open subscheme

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2.
(blueprint: lem-sfb-continuous-sheet-coordinate-restriction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor Matrix TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem restriction_comparison
    (X Y : Scheme.{u}) (f : Y ⟶ X) [WeaklyEtale f]
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    ∃ e : (((continuousRingModuleEquivalence Y T).functor.obj
        ((upperStar (Profinite.continuousMapRingObj T) f).obj P)).val ≅
      (PresheafOfModules.pushforward (continuousRestrictionMap f T)).obj
        ((continuousRingModuleEquivalence X T).functor.obj P).val),
      ∀ (B : Y.ProEt) (x : ((continuousRingModuleEquivalence Y T).functor.obj
          ((upperStar (Profinite.continuousMapRingObj T) f).obj P)).val.obj (op B)),
        e.hom.app (op B) x =
          (((ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance).hom.app
            P.X).hom.app (op B))
              (((inv (upperStarUnitHom (Profinite.continuousMapRingObj T) f P)).hom.app
                (op B)) x) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
    Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let τ := ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance
  let cX := chartComparison X T
  let cY := chartComparison Y T
  let : IsIso cX := chartComparison_isIso X T
  let : IsIso cY := chartComparison_isIso Y T
  let : NatTrans.IsMonoidal τ.hom := inferInstance
  let φ := condensedPullbackHom (Profinite.continuousMapRingObj T) f
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)
  let C := condensedRingObj (Profinite.continuousMapRingObj T) X
  let : MonObj C := inferInstanceAs
    (MonObj (condensedRingObj (Profinite.continuousMapRingObj T) X))
  have hs : G.map cX ≫ τ.hom.app A = φ ≫ cY := continuousChart_pullback X Y f T
  have hc : (inv cY ≫ inv φ) ≫ τ.hom.app C = L.map (inv cX) := by
    apply (cancel_epi (φ ≫ cY)).mp
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    calc
      τ.hom.app C = G.map cX ≫ τ.hom.app A ≫ L.map (inv cX) := by
        rw [← τ.hom.naturality]
        simp
        rfl
      _ = φ ≫ cY ≫ L.map (inv cX) := by rw [← Category.assoc, hs, Category.assoc]
  let : IsMonHom (τ.hom.app C) := NatTrans.isMonHom_app τ.hom C
  let Q := (G.mapMod C).obj P
  let ψ := inv cY ≫ inv φ
  let e := (CategoryTheory.Functor.mapModNatIso τ C).app P
  let Q' := (Mod.comap ψ).obj Q
  let Q'' := (Mod.comap ψ).obj ((Mod.comap (τ.hom.app C)).obj ((L.mapMod C).obj P))
  let R := continuousMapRingSheaf Y T
  let AY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : IsCommMonObj AY := Sheaf.isCommMonObj_sheafCompose_obj _ R
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let H := (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology Y) AY).functor ⋙
      (ringModuleEquivalenceOfIso Y (reconstructedRingIso Y R).symm).functor
  let e₀ := ((Mod.comap (inv cY)).mapIso ((Mod.extendScalarsIsoComapInv φ).app Q)) ≪≫
    ((Mod.comapComp (inv cY) (inv φ)).app Q).symm ≪≫
      (Mod.comap ψ).mapIso e
  let e₁ : (H.obj Q'').val ≅
      (PresheafOfModules.pushforward (continuousRestrictionMap f T)).obj
        ((continuousRingModuleEquivalence X T).functor.obj P).val := by
    refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
    · refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext m
      let Z' := (MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale f)).op.obj Z
      have ha :
          (CategoryTheory.Functor.LaxMonoidal.μ
            (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
            AY (L.obj P.X)).app Z ≫
            (ψ ▷ _ ≫ (τ.hom.app C) ▷ _ ≫
              CategoryTheory.Functor.LaxMonoidal.μ L C P.X ≫ L.map (Mod.act P.X)).hom.app Z =
          (CategoryTheory.Functor.LaxMonoidal.μ
        (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            A P.X).app Z' ≫ ((inv cX) ▷ P.X ≫ Mod.act P.X).hom.app Z' := by
        have hh : ψ ▷ L.obj P.X ≫ (τ.hom.app C) ▷ L.obj P.X =
            (L.map (inv cX)) ▷ L.obj P.X := by
          rw [← comp_whiskerRight]
          exact congrArg (fun a ↦ a ▷ L.obj P.X) hc
        rw [← Category.assoc (ψ ▷ _) ((τ.hom.app C) ▷ _) _, hh]
        rw [CategoryTheory.Functor.LaxMonoidal.μ_natural_left_assoc L (inv cX) P.X,
          ← CategoryTheory.Functor.map_comp]
        simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
        rw [← Category.assoc]
        erw [CategoryTheory.Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
            (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) Ab.{u + 1}
            (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) A P.X Z]
        rfl
      exact ConcreteCategory.congr_hom ha.symm (r ⊗ₜ[ℤ] m)
    · intro Z W a
      ext m
      rfl
  refine ⟨((SheafOfModules.forget _).mapIso (H.mapIso e₀)) ≪≫ e₁, ?_⟩
  intro B x
  change (((e₀.hom).hom ≫ (𝟙 _)).hom.app (op B)) x = _
  rw [Category.comp_id]
  have hu : ((Mod.extendScalarsIsoComapInv φ).inv.app Q).hom =
      upperStarUnitHom (Profinite.continuousMapRingObj T) f P :=
    extendScalarsIsoComapInv_inv_app_hom (Profinite.continuousMapRingObj T) f Q
  have hv : ((Mod.extendScalarsIsoComapInv φ).hom.app Q).hom =
      inv (upperStarUnitHom (Profinite.continuousMapRingObj T) f P) := by
    apply IsIso.eq_inv_of_inv_hom_id
    rw [← hu, ← Mod.comp_hom', Iso.hom_inv_id_app]
    rfl
  change (((Mod.extendScalarsIsoComapInv φ).hom.app Q).hom ≫
    τ.hom.app P.X).hom.app (op B) x = _
  rw [hv]
  rfl

attribute [local irreducible] upperStar upperStarComp upperStarLowerStarAdjunction

private def transport_presentation
    {X : Scheme.{u}} {A : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {N : Type v} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul A N]
    {Q Q' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)}
    (p : ContinuousFunctionPresentation X A N Q) (i : Q' ≅ Q) :
    ContinuousFunctionPresentation X A N Q' := by
  let e := (SheafOfModules.forget _).mapIso
    ((continuousRingModuleEquivalence X A).functor.mapIso i)
  exact
    { sections := fun B ↦
        ((PresheafOfModules.evaluation _ (op B)).mapIso e).toLinearEquiv.toAddEquiv.trans
          (p.sections B)
      restrict := by
        intro B D a x
        change p.sections D (e.hom.app (op D)
          (((continuousRingModuleEquivalence X A).functor.obj Q').val.map a.op x)) = _
        exact (congrArg (p.sections D)
          (PresheafOfModules.naturality_apply e.hom a.op x)).trans
            (p.restrict B D a (e.hom.app (op B) x))
      smul := by
        intro B a x
        change p.sections B (e.hom.app (op B) (a • x)) = _
        rw [map_smul, p.smul]
        rfl }

private theorem transport_presentation_sections
    {X : Scheme.{u}} {A : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {N : Type v} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul A N]
    {Q Q' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)}
    (p : ContinuousFunctionPresentation X A N Q) (i : Q' ≅ Q)
    (B : X.ProEt) (x : ((continuousRingModuleEquivalence X A).functor.obj Q').val.obj
      (op B)) :
    (transport_presentation p i).sections B x =
      p.sections B (((continuousRingModuleEquivalence X A).functor.map i.hom).val.app
        (op B) x) := rfl

attribute [local irreducible] transport_presentation

private theorem module_functor_map_comp_apply
    {X : Scheme.{u}} {A : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X) ⥤
        SheafOfModules.{u + 1} (continuousMapRingSheaf X A))
    {Q Q' Q'' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)}
    (m : Q ⟶ Q') (n : Q' ⟶ Q'') (B : X.ProEt) (x : (F.obj Q).val.obj (op B)) :
    (F.map n).val.app (op B) ((F.map m).val.app (op B) x) =
      (F.map (m ≫ n)).val.app (op B) x := by
  rw [F.map_comp]
  rfl

private theorem transport_presentation_map
    {X : Scheme.{u}} {A : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {N : Type v} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul A N]
    {Q Q' M M' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)}
    (p : ContinuousFunctionPresentation X A N Q) (i : Q' ≅ Q) (j : M' ≅ M)
    (m : M ⟶ Q) (m' : M' ⟶ Q') (hm : m' ≫ i.hom = j.hom ≫ m)
    (B : X.ProEt) (x : ((continuousRingModuleEquivalence X A).functor.obj M').val.obj
      (op B)) :
    (transport_presentation p i).sections B
        (((continuousRingModuleEquivalence X A).functor.map m').val.app (op B) x) =
      p.sections B (((continuousRingModuleEquivalence X A).functor.map m).val.app
        (op B) (((continuousRingModuleEquivalence X A).functor.map j.hom).val.app
          (op B) x)) := by
  rw [transport_presentation_sections, module_functor_map_comp_apply, hm,
    ← module_functor_map_comp_apply]

private theorem restrict_presentation
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    {A : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {N : Type v} [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul A N]
    {Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)}
    (p : ContinuousFunctionPresentation X A N Q) :
    ∃ p' : ContinuousFunctionPresentation Y A N
        ((upperStar (Profinite.continuousMapRingObj A) f).obj Q),
      ∀ B x, p'.sections B x =
        p.sections ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).obj B)
          ((((ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance).hom.app
            Q.X).hom.app (op B))
              (((inv (upperStarUnitHom (Profinite.continuousMapRingObj A) f Q)).hom.app
                (op B)) x)) := by
  obtain ⟨e, he⟩ := restriction_comparison X Y f A Q
  let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)
  let p' : ContinuousFunctionPresentation Y A N
      ((upperStar (Profinite.continuousMapRingObj A) f).obj Q) :=
    { sections := fun B ↦
        ((PresheafOfModules.evaluation _ (op B)).mapIso e).toLinearEquiv.toAddEquiv.trans
          (p.sections (F.obj B))
      restrict := by
        intro B D a x
        change p.sections (F.obj D) (e.hom.app (op D)
          (((continuousRingModuleEquivalence Y A).functor.obj
            ((upperStar (Profinite.continuousMapRingObj A) f).obj Q)).val.map a.op x)) = _
        rw [PresheafOfModules.naturality_apply]
        change p.sections (F.obj D)
          (((continuousRingModuleEquivalence X A).functor.obj Q).val.map
            (F.map a).op (e.hom.app (op B) x)) = _
        rw [p.restrict]
        rfl
      smul := by
        intro B a x
        change p.sections (F.obj B) (e.hom.app (op B) (a • x)) = _
        rw [map_smul]
        rw [p.smul]
        rfl }
  refine ⟨p', ?_⟩
  intro B x
  change p.sections (F.obj B) (e.hom.app (op B) x) = _
  rw [he]

private theorem restriction_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)} (m : M ⟶ N) :
    ((upperStar (Profinite.continuousMapRingObj A) f).map m).hom ≫
        inv (upperStarUnitHom (Profinite.continuousMapRingObj A) f N) ≫
        (ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance).hom.app N.X =
      inv (upperStarUnitHom (Profinite.continuousMapRingObj A) f M) ≫
        (ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance).hom.app M.X ≫
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
          Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map m.hom := by
  apply (cancel_epi (upperStarUnitHom (Profinite.continuousMapRingObj A) f M)).mp
  rw [upperStarUnitHom_map_hom_assoc, IsIso.hom_inv_id_assoc,
    IsIso.hom_inv_id_assoc]
  exact (ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance).hom.naturality
    m.hom

-- Unfolding the section encoding compares its underlying additive maps.
private theorem restriction_sections_naturality
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)} (m : M ⟶ N)
    (B : Y.ProEt)
    (x : ((continuousRingModuleEquivalence Y A).functor.obj
      ((upperStar (Profinite.continuousMapRingObj A) f).obj M)).val.obj (op B)) :
    (((ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance).hom.app
      N.X).hom.app (op B))
        (((inv (upperStarUnitHom (Profinite.continuousMapRingObj A) f N)).hom.app
          (op B)) (((continuousRingModuleEquivalence Y A).functor.map
            ((upperStar (Profinite.continuousMapRingObj A) f).map m)).val.app (op B) x)) =
      ((continuousRingModuleEquivalence X A).functor.map m).val.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).obj B))
          ((((ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} f inferInstance).hom.app
            M.X).hom.app (op B))
              (((inv (upperStarUnitHom (Profinite.continuousMapRingObj A) f M)).hom.app
                (op B)) x)) := by
  have hn := restriction_naturality f A m
  have hnB := congrArg (fun k ↦ k.hom.app (op B)) hn
  have hx := ConcreteCategory.congr_hom hnB
    (show ((upperStar (Profinite.continuousMapRingObj A) f).obj M).X.obj.obj
      (op B) from x)
  exact hx

private theorem normalization_comp
    (S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
    {X U Y Z : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X) (t : Y ⟶ U)
    (w : t ≫ p = g) (f : Z ⟶ Y) :
    upperStarComp S f g ≪≫
        CategoryTheory.Functor.isoWhiskerRight
          ((eqToIso (congrArg (upperStar S) w)).symm ≪≫ upperStarComp S t p)
          (upperStar S f) ≪≫
        (upperStar S p).associator (upperStar S t) (upperStar S f) =
      ((eqToIso (congrArg (upperStar S)
        ((Category.assoc f t p).trans (congrArg (fun k ↦ f ≫ k) w)))).symm ≪≫
        upperStarComp S (f ≫ t) p) ≪≫
        CategoryTheory.Functor.isoWhiskerLeft (upperStar S p) (upperStarComp S f t) := by
  subst g
  have he {a b : Z ⟶ X} (h : a = b) :
      (eqToIso (congrArg (upperStar S) h)).symm = upperStarCongr S h.symm := by
    cases h
    rfl
  rw [he (Category.assoc f t p)]
  simpa only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl,
    Iso.trans_assoc] using upperStarComp_assoc S f t p

private theorem module_assoc
    {X : Scheme.{u}} {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R]
    {M N P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)}
    (f : M ⟶ N) (g : N ⟶ P) (h : P ⟶ Q) : (f ≫ g) ≫ h = f ≫ g ≫ h :=
  Category.assoc f g h

-- Keep comparison isomorphisms abstract during the categorical calculation.
private theorem sheet_pullback_aux
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {U Y Z : Scheme.{u}}
    (Q : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj S U))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj S Y))
    (N' : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj S Z))
    (v : M ⟶ (Mod.comap (coefficientMap a U)).obj Q)
    (t : Y ⟶ U) (f : Z ⟶ Y)
    (n : (upperStar S t).obj Q ⟶ N)
    (n' : (upperStar S (f ≫ t)).obj Q ⟶ N')
    (q : N' ⟶ (upperStar S f).obj N)
    (hn : (upperStarComp S f t).hom.app Q ≫ (upperStar S f).map n = n' ≫ q) :
    (upperStarComp R f t).hom.app M ≫
        (upperStar R f).map ((upperStar R t).map v ≫
          (comapUpperStarIso a t).inv.app Q ≫
          (Mod.comap (coefficientMap a Y)).map n) =
      (upperStar R (f ≫ t)).map v ≫
        (comapUpperStarIso a (f ≫ t)).inv.app Q ≫
        (Mod.comap (coefficientMap a Z)).map n' ≫
        (Mod.comap (coefficientMap a Z)).map q ≫
        (comapUpperStarIso a f).hom.app N := by
  have hv : (upperStarComp R f t).hom.app M ≫
      (upperStar R f).map ((upperStar R t).map v) =
      (upperStar R (f ≫ t)).map v ≫
        (upperStarComp R f t).hom.app ((Mod.comap (coefficientMap a U)).obj Q) := by
    simpa only [CategoryTheory.Functor.comp_map] using
      ((upperStarComp R f t).hom.naturality v).symm
  have hc : (comapUpperStarIso a f).hom.app ((upperStar S t).obj Q) ≫
      (upperStar R f).map ((Mod.comap (coefficientMap a Y)).map n) =
      (Mod.comap (coefficientMap a Z)).map ((upperStar S f).map n) ≫
        (comapUpperStarIso a f).hom.app N := by
    simpa only [CategoryTheory.Functor.comp_map] using
      ((comapUpperStarIso a f).hom.naturality n).symm
  simp only [CategoryTheory.Functor.map_comp]
  rw [← module_assoc, hv, module_assoc, comapUpperStarIso_comp a f t Q]
  simp only [module_assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [hc, ← CategoryTheory.Functor.map_comp_assoc, hn]
  simp only [CategoryTheory.Functor.map_comp, module_assoc]

private theorem sheet_embedding_eq
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    finiteEtaleLatticeSheetEmbedding a P p M e g t w =
      (upperStar R t).map (latticeIntegralEmbedding a X P p M e) ≫
        (comapUpperStarIso a t).inv.app ((upperStar S p).obj P) ≫
          (Mod.comap (coefficientMap a Y)).map
            (((eqToIso (congrArg (upperStar S) w)).symm ≪≫
              upperStarComp S t p).inv.app P) := by
  subst g
  unfold finiteEtaleLatticeSheetEmbedding
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]

attribute [local irreducible] finiteEtaleLatticeSheetEmbedding latticeIntegralEmbedding
  comapUpperStarIso

-- Checking the pullback coherence involves large module-object comparison terms.
private theorem sheet_pullback
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y Z : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) (f : Z ⟶ Y) :
    (upperStarComp R f t).hom.app M ≫
        (upperStar R f).map (finiteEtaleLatticeSheetEmbedding a P p M e g t w) =
      finiteEtaleLatticeSheetEmbedding a P p M e (f ≫ g) (f ≫ t)
          ((Category.assoc f t p).trans (congrArg (fun k ↦ f ≫ k) w)) ≫
        (Mod.comap (coefficientMap a Z)).map ((upperStarComp S f g).hom.app P) ≫
        (comapUpperStarIso a f).hom.app ((upperStar S g).obj P) := by
  let Q := (upperStar S p).obj P
  let n := (eqToIso (congrArg (upperStar S) w)).symm ≪≫ upperStarComp S t p
  let n' := (eqToIso (congrArg (upperStar S)
    ((Category.assoc f t p).trans (congrArg (fun k ↦ f ≫ k) w)))).symm ≪≫
      upperStarComp S (f ≫ t) p
  have hn : n'.hom.app P ≫ (upperStarComp S f t).hom.app Q =
      (upperStarComp S f g).hom.app P ≫ (upperStar S f).map (n.hom.app P) := by
    as_aux_lemma =>
      have h := congrArg (fun i ↦ i.hom.app P) (normalization_comp S p g t w f)
      simpa only [n, n', Q, Iso.trans_hom, NatTrans.comp_app,
        CategoryTheory.Functor.isoWhiskerRight_hom, CategoryTheory.Functor.whiskerRight_app,
        CategoryTheory.Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.whiskerLeft_app,
        CategoryTheory.Functor.associator_hom_app, Category.comp_id] using h.symm
  have hn' : (upperStarComp S f t).hom.app Q ≫ (upperStar S f).map (n.inv.app P) =
      n'.inv.app P ≫ (upperStarComp S f g).hom.app P := by
    as_aux_lemma =>
      apply (cancel_epi (n'.hom.app P)).mp
      rw [← module_assoc, hn, module_assoc, ← CategoryTheory.Functor.map_comp,
        Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
      erw [Category.comp_id, Iso.hom_inv_id_app_assoc]
  rw [sheet_embedding_eq, sheet_embedding_eq]
  simp only [module_assoc]
  exact sheet_pullback_aux a Q M ((upperStar S g).obj P)
    ((upperStar S (f ≫ g)).obj P) (latticeIntegralEmbedding a X P p M e) t f
    (n.inv.app P) (n'.inv.app P) ((upperStarComp S f g).hom.app P) hn'

private def pullback_comap_iso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X Y Z : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (g : Y ⟶ X) (f : Z ⟶ Y) :
    (Mod.comap (coefficientMap a Z)).obj ((upperStar S (f ≫ g)).obj P) ≅
      (upperStar R f).obj
        ((Mod.comap (coefficientMap a Y)).obj ((upperStar S g).obj P)) :=
  (Mod.comap (coefficientMap a Z)).mapIso ((upperStarComp S f g).app P) ≪≫
    (comapUpperStarIso a f).app ((upperStar S g).obj P)

private def pullback_comp_iso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {U Y Z : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (t : Y ⟶ U) (f : Z ⟶ Y) :
    (upperStar R (f ≫ t)).obj M ≅ (upperStar R f).obj ((upperStar R t).obj M) :=
  (upperStarComp R f t).app M

private theorem sheet_pullback_iso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X U Y Z : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (e : (Mod.extendScalars (coefficientMap a U)).obj M ≅ (upperStar S p).obj P)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) (f : Z ⟶ Y) :
    finiteEtaleLatticeSheetEmbedding a P p M e (f ≫ g) (f ≫ t)
        ((Category.assoc f t p).trans (congrArg (fun k ↦ f ≫ k) w)) ≫
      (pullback_comap_iso a P g f).hom =
      (pullback_comp_iso R M t f).hom ≫
        (upperStar R f).map (finiteEtaleLatticeSheetEmbedding a P p M e g t w) := by
  simp only [pullback_comap_iso, pullback_comp_iso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
  exact (sheet_pullback a P p M e g t w f).symm

attribute [local irreducible] pullback_comap_iso pullback_comp_iso

-- Keep both the restriction functor and its comparison abstract in the calculation.
private theorem restricted_relation_via_functor
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    {A : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {N₀ N₁ : Type v} [AddCommGroup N₀] [Module A N₀] [TopologicalSpace N₀]
    [IsTopologicalAddGroup N₀] [ContinuousSMul A N₀]
    [AddCommGroup N₁] [Module A N₁] [TopologicalSpace N₁]
    [IsTopologicalAddGroup N₁] [ContinuousSMul A N₁]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj A) X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj A) Y))
    (ν : F ≅ upperStar (Profinite.continuousMapRingObj A) f)
    {d : ℕ}
    {Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)}
    {M : Fin d → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)}
    (c : ContinuousFunctionPresentation X A N₀ Q)
    (b : ∀ j, ContinuousFunctionPresentation X A N₁ (M j))
    (m : ∀ j, M j ⟶ Q)
    {Q' : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y)}
    {M' : Fin d → Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) Y)}
    (ic : Q' ≅ F.obj Q) (ib : ∀ j, M' j ≅ F.obj (M j))
    (m' : ∀ j, M' j ⟶ Q')
    (hm : ∀ j, m' j ≫ ic.hom = (ib j).hom ≫ F.map (m j))
    (H : ∀ (_j : Fin d) (B : X.ProEt), C(B.left, N₀) → C(B.left, N₁) → Prop)
    (h : ∀ j B x, H j B
      (c.sections B (((continuousRingModuleEquivalence X A).functor.map
        (m j)).val.app (op B) x)) ((b j).sections B x)) :
    ∃ c' : ContinuousFunctionPresentation Y A N₀ Q',
      ∃ b' : ∀ j, ContinuousFunctionPresentation Y A N₁ (M' j),
        ∀ j B x,
          H j ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).obj B)
            (c'.sections B (((continuousRingModuleEquivalence Y A).functor.map
              (m' j)).val.app (op B) x)) ((b' j).sections B x) := by
  obtain ⟨c₀, hc⟩ := restrict_presentation f c
  have hb (j : Fin d) := restrict_presentation f (b j)
  choose b₀ hb using hb
  let i : Q' ≅ (upperStar (Profinite.continuousMapRingObj A) f).obj Q :=
    ic ≪≫ ν.app Q
  let k (j : Fin d) : M' j ≅
      (upperStar (Profinite.continuousMapRingObj A) f).obj (M j) := ib j ≪≫ ν.app (M j)
  have hm' (j : Fin d) : m' j ≫ i.hom = (k j).hom ≫
      (upperStar (Profinite.continuousMapRingObj A) f).map (m j) := by
    dsimp only [i, k, Iso.trans_hom, Iso.app_hom]
    rw [← module_assoc, hm, module_assoc, ν.hom.naturality]
    simp only [module_assoc]
  refine ⟨transport_presentation c₀ i,
    fun j ↦ transport_presentation (b₀ j) (k j), ?_⟩
  intro j B x
  rw [transport_presentation_map c₀ i (k j)
    ((upperStar (Profinite.continuousMapRingObj A) f).map (m j)) (m' j) (hm' j),
    transport_presentation_sections, hc, hb, restriction_sections_naturality f A (m j)]
  exact h j _ _

private abbrev canonical_upperStar
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  upperStar (Profinite.continuousMapRingObj A) f

private theorem integral_star_eq
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    upperStar (integralCoeff l E) f = canonical_upperStar (continuousIntegers l E) f := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Keep the coefficient comparison abstract when applying the restriction construction.
/-- A global coordinate equation for normalized sheet maps persists on every open.
The matrices are arbitrary; freeness and invertibility are not assumed.
Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2;
Bhatt--Scholze, Section 6.8, restriction of continuous coefficients.
(blueprint: lem-sfb-continuous-sheet-coordinate-restriction)

Proof. Restrict the two given continuous-function presentations along W → Y.
The continuous module encoding identifies inverse image along this open immersion
with restriction of its module presheaf, so the restricted coordinate maps are
the same maps on each pro-etale test object B over W, now regarded as an object
over Y. For the rational presentation first use comapUpperStarIso to commute
restriction of scalars with inverse image; then upperStarComp identifies the
rational target with the pullback along W.ι ≫ g. Similarly upperStarComp for
integral coefficients identifies each source with pullback along W.ι ≫ t j.
These transports preserve linearity and the coordinate restriction identities.
The equation (W.ι ≫ t j) ≫ p = W.ι ≫ g follows by associativity and w j.
Naturality of comapUpperStarIso and associativity of upperStarComp identify
the transported global sheet map with finiteEtaleLatticeSheetEmbedding for
these composite arrows. Apply the assumed global equation to B regarded over Y.
Its point is W.ι (B.hom z), giving the displayed formula. On an empty W there
are no points z; the same restriction construction still gives the presentations.
No matrix-continuity, invertibility, rank or scalar-extension claim is needed. -/
theorem continuousSheet_coordinate_restriction
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (p : U ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P)
    (g : Y ⟶ X) (d : ℕ) (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (r : ℕ)
    (c : ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin r → E) ((Mod.comap (coefficientMap (integralScalarMap l E) Y)).obj
          ((upperStar (Profinite.continuousMapRingObj E) g).obj P)))
    (b : ∀ j, ContinuousFunctionPresentation Y (continuousIntegers l E)
        (Fin r → continuousIntegers l E) ((upperStar (integralCoeff l E) (t j)).obj M))
    (G : Fin d → Y → Matrix (Fin r) (Fin r) E)
    (h : ∀ (j : Fin d) (B : Y.ProEt)
      (x : ((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.obj
          ((upperStar (integralCoeff l E) (t j)).obj M)).val.obj (op B)) (z : B.left),
      c.sections B
        (((continuousRingModuleEquivalence Y (continuousIntegers l E)).functor.map
            (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
              g (t j) (w j))).val.app (op B) x) z =
        G j (B.hom z) *ᵥ (fun i ↦ ((b j).sections B x z i : E))) :
      ∀ W : Y.Opens, ∃ w' : ∀ j, (W.ι ≫ t j) ≫ p = W.ι ≫ g,
        ∃ c : ContinuousFunctionPresentation W.toScheme (continuousIntegers l E)
            (Fin r → E) ((Mod.comap
              (coefficientMap (integralScalarMap l E) W.toScheme)).obj
              ((upperStar (Profinite.continuousMapRingObj E) (W.ι ≫ g)).obj P)),
        ∃ b : ∀ j, ContinuousFunctionPresentation W.toScheme (continuousIntegers l E)
            (Fin r → continuousIntegers l E)
            ((upperStar (integralCoeff l E) (W.ι ≫ t j)).obj M),
        ∀ (j : Fin d) (B : W.toScheme.ProEt)
          (x : ((continuousRingModuleEquivalence W.toScheme
            (continuousIntegers l E)).functor.obj
            ((upperStar (integralCoeff l E) (W.ι ≫ t j)).obj M)).val.obj (op B))
          (z : B.left),
          c.sections B
            (((continuousRingModuleEquivalence W.toScheme
              (continuousIntegers l E)).functor.map
              (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
                (W.ι ≫ g) (W.ι ≫ t j) (w' j))).val.app (op B) x) z =
            G j (W.ι (B.hom z)) *ᵥ
              (fun i ↦ ((b j).sections B x z i : E)) := by
  intro W
  let w' (j : Fin d) : (W.ι ≫ t j) ≫ p = W.ι ≫ g :=
    (Category.assoc W.ι (t j) p).trans (congrArg (fun k ↦ W.ι ≫ k) (w j))
  refine ⟨w', ?_⟩
  refine restricted_relation_via_functor W.ι (upperStar (integralCoeff l E) W.ι)
    (eqToIso (integral_star_eq l E W.ι)) c b
    (fun j ↦ finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
      g (t j) (w j))
    (pullback_comap_iso (integralScalarMap l E) P g W.ι)
    (fun j ↦ pullback_comp_iso (integralCoeff l E) M (t j) W.ι)
    (fun j ↦ finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
      (W.ι ≫ g) (W.ι ≫ t j) (w' j))
    (fun j ↦ sheet_pullback_iso (integralScalarMap l E) P p M e g (t j) (w j) W.ι)
    (fun j B a v ↦ ∀ z, a z = G j (B.hom z) *ᵥ (fun i ↦ (v z i : E))) ?_
  intro j B x z
  exact h j B x z

end AlgebraicGeometry.ProEtale.CondensedRing

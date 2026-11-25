/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import WeilConjectures.ProperBaseChange.IntegralCoefficientStrictTowerComparison

/-! # Strict coefficient comparison before derived-limit descent

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tags 03D3, 06YY and 099N(5).
(blueprint: lem-weil-pbc-integral-strict-model-chain-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] completedAdicChangeData HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted pbcIntegralDatum

attribute [local instance] completedReductionModuleTowerFunctor_additive
  completedTowerModulePullback_additive completedModulePullback_additive

private theorem completedTowerZero (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionModuleTowerFunctor W d).PreservesZeroMorphisms := by
  let := completedReductionModuleTowerFunctor_additive W d
  exact Functor.preservesZeroMorphisms_of_additive
    (F := completedReductionModuleTowerFunctor W d)

private theorem pbcTowerZero (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (show pbcModules W (pbcAdicCompletion W d) ⥤
        pbcTowers W (pbcAdicCompletion W d) from
      completedReductionModuleTowerFunctor W d).PreservesZeroMorphisms := by
  exact completedTowerZero W d

private theorem cancelNormalized
    {C : Type*} [Category C] {A B D E F : C}
    {f : A ⟶ B} {g : B ⟶ A} {b : B ⟶ D} {e : D ⟶ E}
    {r : E ⟶ F} {u : A ⟶ F} {v : B ⟶ E}
    (hfg : f ≫ g = 𝟙 A) (hb : b ≫ e = v) (hg : g ≫ u = v ≫ r) :
    f ≫ b ≫ (e ≫ r) = u := by
  rw [← Category.assoc b e, hb, ← hg, ← Category.assoc, hfg, Category.id_comp]

private theorem normalizeFive
    {C : Type*} [Category C] {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {d : E ⟶ F} {e : F ⟶ G}
    {q : A ⟶ E} {r : A ⟶ F} {s : A ⟶ G}
    (h₁ : a ≫ b ≫ c = q) (h₂ : q ≫ d = r) (h₃ : r ≫ e = s) :
    a ≫ b ≫ (c ≫ d ≫ e) = s := by
  rw [← Category.assoc b c, ← Category.assoc, h₁, ← Category.assoc, h₂, h₃]

private def composeModuleComparison
    {C D E K D' E' : Type*}
    [Category C] [Category D] [Category E] [Category K] [Category D'] [Category E']
    (A : C ⥤ D) (R : D ⥤ E) (B : E ⥤ K)
    (L : C ⥤ D') (P : D' ⥤ E') (S : E' ⥤ K) (K₀ : D ⥤ E')
    (e : R ⋙ B ≅ K₀ ⋙ S) (a : L ⋙ P ≅ A ⋙ K₀) :
    A ⋙ R ⋙ B ≅ (L ⋙ P) ⋙ S :=
  NatIso.ofComponents (fun M ↦ e.app (A.obj M) ≪≫ S.mapIso (a.symm.app M)) (by
    intro M N f
    change B.map (R.map (A.map f)) ≫
        (e.hom.app (A.obj N) ≫ S.map (a.inv.app N)) =
      (e.hom.app (A.obj M) ≫ S.map (a.inv.app M)) ≫ S.map (P.map (L.map f))
    have he := e.hom.naturality (A.map f)
    change B.map (R.map (A.map f)) ≫ e.hom.app (A.obj N) =
      e.hom.app (A.obj M) ≫ S.map (K₀.map (A.map f)) at he
    have ha := a.inv.naturality f
    change K₀.map (A.map f) ≫ a.inv.app N =
      a.inv.app M ≫ P.map (L.map f) at ha
    rw [← Category.assoc, he, Category.assoc, ← S.map_comp, ha, S.map_comp,
      ← Category.assoc])

private def chainTripleMapIso
    {C D E K D' E' : Type*}
    [Category C] [Category D] [Category E] [Category K] [Category D'] [Category E']
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E] [HasZeroMorphisms K]
    [HasZeroMorphisms D'] [HasZeroMorphisms E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)
    (F' : C ⥤ D') (G' : D' ⥤ E') (H' : E' ⥤ K)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    [F'.PreservesZeroMorphisms] [G'.PreservesZeroMorphisms] [H'.PreservesZeroMorphisms]
    (e : F ⋙ G ⋙ H ≅ (F' ⋙ G') ⋙ H') :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ⋙
        H.mapHomologicalComplex (.up ℤ) ≅
      F'.mapHomologicalComplex (.up ℤ) ⋙ G'.mapHomologicalComplex (.up ℤ) ⋙
        H'.mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ e.app (P.X i)) (by
      intro i j hij
      exact (e.hom.naturality (P.d i j)).symm)) (by
        intro P Q f
        apply HomologicalComplex.hom_ext
        intro i
        exact e.hom.naturality (f.f i))

/-- The functor of actual pulled reduction towers, using the published module functors.
Source: Stacks 099N(5).
(blueprint: lem-weil-pbc-integral-strict-model-chain-transport). -/
def pbcIntegralActualTowerFunctor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T) :
    CochainComplex (integralTowerModules l E T) ℤ ⥤
      CochainComplex (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ :=
  let F := pbcIntegralTransportComplex T l E ⋙
    completedReductionComplexTowerFunctor T (pbcIntegralDatum l E) ⋙
      (completedTowerModulePullback h (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ)
  { obj := pbcIntegralActualTower l E h
    map := fun f ↦ F.map f
    map_id := fun P ↦ F.map_id P
    map_comp := fun f g ↦ F.map_comp f g }

private theorem completedTowerComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T) :
    ∃ e : completedReductionModuleTowerFunctor T (pbcIntegralDatum l E) ⋙
        completedTowerModulePullback h (pbcIntegralDatum l E) ≅
      completedModulePullback h (pbcIntegralDatum l E) ⋙
        completedReductionModuleTowerFunctor U (pbcIntegralDatum l E),
      ∀ (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) (n : ℕ),
        (completedModulePullback h (pbcIntegralDatum l E)).map
            (((completedReductionModuleUnit (pbcIntegralDatum l E) T).app M).app (op n)) ≫
              (e.hom.app M).app (op n) =
          ((completedReductionModuleUnit (pbcIntegralDatum l E) U).app
            ((completedModulePullback h (pbcIntegralDatum l E)).obj M)).app (op n) := by
  unfold completedTowerModulePullback
  rw [completedModulePullback_eq_exact]
  refine ⟨stratumModuleReductionIso (pbcIntegralDatum l E) h, ?_⟩
  intro M n
  have hs := (stratumModuleReductionIso_exists (pbcIntegralDatum l E) h).exists.choose_spec M
  have hs' := congrArg (fun f ↦ f.app (op n)) hs
  dsimp only [NatTrans.comp_app, AdicCoefficientDatum.constantPullbackIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom, AdicCoefficientDatum.towerModulePull,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app] at hs'
  erw [Category.id_comp] at hs'
  exact hs'

private theorem actualModuleComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (a : PbcProperIntegralPullbackIdentification l E h) :
    ∃ σ : pbcIntegralTransportModules T l E ⋙
          completedReductionModuleTowerFunctor T (pbcIntegralDatum l E) ⋙
            completedTowerModulePullback h (pbcIntegralDatum l E) ≅
        (ordinaryIntegralModulePull l E h ⋙ pbcIntegralTransportModules U l E) ⋙
          completedReductionModuleTowerFunctor U (pbcIntegralDatum l E),
      ∀ (M : integralTowerModules l E T) (n : ℕ),
        a.moduleIso.hom.app M ≫
          (completedModulePullback h (pbcIntegralDatum l E)).map
            (((completedReductionModuleUnit (pbcIntegralDatum l E) T).app
              ((pbcIntegralTransportModules T l E).obj M)).app (op n)) ≫
            (σ.hom.app M).app (op n) =
          ((completedReductionModuleUnit (pbcIntegralDatum l E) U).app
            ((pbcIntegralTransportModules U l E).obj
              ((ordinaryIntegralModulePull l E h).obj M))).app (op n) := by
  obtain ⟨e, he⟩ := completedTowerComparison l E h
  let R := completedReductionModuleTowerFunctor U (pbcIntegralDatum l E)
  let σ := composeModuleComparison (pbcIntegralTransportModules T l E)
    (completedReductionModuleTowerFunctor T (pbcIntegralDatum l E))
    (completedTowerModulePullback h (pbcIntegralDatum l E))
    (ordinaryIntegralModulePull l E h) (pbcIntegralTransportModules U l E) R
    (completedModulePullback h (pbcIntegralDatum l E)) e a.moduleIso
  refine ⟨σ, ?_⟩
  intro M n
  let q := completedReductionModuleUnit (pbcIntegralDatum l E) U
  have hn := NatTrans.congr_app (q.naturality (a.moduleIso.inv.app M)) (op n)
  change a.moduleIso.inv.app M ≫ (q.app _).app (op n) =
    (q.app _).app (op n) ≫ (R.map (a.moduleIso.inv.app M)).app (op n) at hn
  have he' := he ((pbcIntegralTransportModules T l E).obj M) n
  change a.moduleIso.hom.app M ≫ _ ≫
    ((e.hom.app ((pbcIntegralTransportModules T l E).obj M)).app (op n) ≫
      (R.map (a.moduleIso.inv.app M)).app (op n)) = _
  exact cancelNormalized (a.moduleIso.hom_inv_id_app M) he' hn

private theorem augmentationWhiskerIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} {A B : D ⥤ E} {V : C ⥤ E}
    (η : A ⟶ B) (e : F ≅ G) (r : G ⋙ B ≅ V) :
    Functor.whiskerLeft F η ≫ (Functor.isoWhiskerRight e B ≪≫ r).hom =
      Functor.whiskerRight e.hom A ≫ Functor.whiskerLeft G η ≫ r.hom := by
  apply NatTrans.ext
  funext P
  change η.app (F.obj P) ≫ (B.map (e.hom.app P) ≫ r.hom.app P) =
    A.map (e.hom.app P) ≫ η.app (G.obj P) ≫ r.hom.app P
  rw [← Category.assoc, ← η.naturality, Category.assoc]

private theorem ordinaryTowerComparison_unit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) (n : ℕ) :
    (((IntegralOnSlice.augmentation l E U none).app
        ((ordinaryIntegralPullComplex l E h).obj P)).app (op n)) ≫
      (((Functor.isoWhiskerRight (ordinaryAmbientComplexIso l E h)
        (IntegralOnSlice.tower l E U none) ≪≫
          IntegralAmbient.pullTowerIso l E h).hom.app P).app (op n)) =
      (((ordinaryIntegralQuotientAugmentation l E h).app P).app (op n)) := by
  have ho : ordinaryIntegralQuotientAugmentation l E h = ordinaryAugmentation l E h :=
    (ordinaryIntegralQuotientAugmentation_existsUnique l E h).unique
      (ordinaryIntegralQuotientAugmentation_existsUnique l E h).exists.choose_spec
      (ordinaryAugmentation_formula l E h)
  rw [ho]
  exact congrArg (fun α ↦ (α.app P).app (op n))
    (augmentationWhiskerIso (IntegralOnSlice.augmentation l E U none)
      (ordinaryAmbientComplexIso l E h) (IntegralAmbient.pullTowerIso l E h))

/-- Tensor balancing compares the strict towers naturally
on good representatives.
This is entirely a statement about complexes; it does not construct a derived
natural comparison or assert its formula on resolutions.

Source: Bhatt--Scholze, Remark 6.8.15; Stacks 03D3, 06YY and 099N(5).
(blueprint: lem-weil-pbc-integral-strict-model-chain-transport).

Proof: restrict the coefficient isomorphisms to each finite quotient. At level n,
the balanced tensor map takes b tensor (m tensor q) to pi_n(b) times
(1 tensor (m tensor q)), using the normalized coefficient identifications. Its
inverse inserts 1 in the completed scalar factor. The coefficient projection
square makes these maps balanced and proves their inverse identities. Sheafify
the maps and apply them degreewise. The maps commute with differentials and
with maps of input modules because the tensor associators do. Quotient transition
maps take q to its image in the smaller quotient; both composites on pure tensors
therefore coincide. Sheafification uniqueness proves the strict transition and
naturality squares. Thus the level comparisons form the natural tower isomorphism t.
Both augmentations send an adjunction-unit generator m to 1 tensor (m tensor 1).
The module_unit equation for a identifies these generators on the two presentations.
Linearity, restriction compatibility, and generation by the adjunction-unit
sections prove the required augmentation equality on the entire source. -/
theorem pbc_integral_strict_model_chain_transport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (a : PbcProperIntegralPullbackIdentification l E h) :
    ∃ t : (integralOperationsGoodComplex l E T).ι ⋙
        pbcIntegralActualTowerFunctor l E h ⋙
          HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      (integralOperationsGoodComplex l E T).ι ⋙
        integralOperationsPullbackTowerFunctor l E h ⋙
          (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcIntegralTransportComplex U l E),
      ∀ (P : (integralOperationsGoodComplex l E T).FullSubcategory) (n : ℕ),
        (NatTrans.mapHomologicalComplex a.moduleIso.hom (.up ℤ)).app P.obj ≫
            pbcIntegralActualTowerAugmentation l E h P.obj n ≫
              (t.hom.app P).app (op n) =
          (pbcIntegralTransportComplex U l E).map
            (((ordinaryIntegralQuotientAugmentation l E h).app P.obj).app (op n)) := by
  let := pbcTowerZero T (pbcIntegralDatum l E)
  let := pbcTowerZero U (pbcIntegralDatum l E)
  let R : pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
      pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) :=
    completedReductionModuleTowerFunctor U (pbcIntegralDatum l E)
  let RT : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)) ⥤
      pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E)) :=
    completedReductionModuleTowerFunctor T (pbcIntegralDatum l E)
  let B : pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E)) ⥤
      pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) :=
    completedTowerModulePullback h (pbcIntegralDatum l E)
  let : R.PreservesZeroMorphisms := pbcTowerZero U (pbcIntegralDatum l E)
  let : RT.PreservesZeroMorphisms := pbcTowerZero T (pbcIntegralDatum l E)
  let : B.PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ B
      (completedTowerModulePullback_additive h (pbcIntegralDatum l E))
  let L : integralTowerModules l E T ⥤ integralTowerModules l E U :=
    ordinaryIntegralModulePull l E h
  obtain ⟨σ₀, hσ⟩ := actualModuleComparison l E h a
  let σ : pbcIntegralTransportModules T l E ⋙ RT ⋙ B ≅
      (L ⋙ pbcIntegralTransportModules U l E) ⋙ R := σ₀
  let H := HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (T := ℕᵒᵖ) (V := pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E)))
      (c := .up ℤ)
  let : L.PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ L
      (ordinaryIntegralModulePull_additive l E h)
  let v := chainTripleMapIso (pbcIntegralTransportModules T l E) RT B
    L (pbcIntegralTransportModules U l E) R σ
  let s : pbcIntegralActualTowerFunctor l E h ⋙ H ≅
      ordinaryIntegralPullComplex l E h ⋙ pbcIntegralTransportComplex U l E ⋙
        completedReductionComplexTowerFunctor U (pbcIntegralDatum l E) ⋙ H :=
    NatIso.ofComponents (fun P ↦ H.mapIso (v.app P)) (by
      intro P Q f
      exact (Functor.isoWhiskerRight v H).hom.naturality f)
  obtain ⟨c₀, hc⟩ := integralCoefficientStrictTowerComparison l E U
  let F := pbcIntegralTransportComplex U l E
  let W := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F
  let c : F ⋙ completedReductionComplexTowerFunctor U (pbcIntegralDatum l E) ⋙ H ≅
      IntegralOnSlice.tower l E U none ⋙ W := c₀
  let r : ordinaryIntegralPullComplex l E h ⋙ IntegralOnSlice.tower l E U none ≅
      integralOperationsPullbackTowerFunctor l E h :=
    Functor.isoWhiskerRight (ordinaryAmbientComplexIso l E h)
      (IntegralOnSlice.tower l E U none) ≪≫ IntegralAmbient.pullTowerIso l E h
  let t : pbcIntegralActualTowerFunctor l E h ⋙ H ≅
      integralOperationsPullbackTowerFunctor l E h ⋙ W :=
    s ≪≫ Functor.isoWhiskerLeft (ordinaryIntegralPullComplex l E h) c ≪≫
      (Functor.associator (ordinaryIntegralPullComplex l E h)
        (IntegralOnSlice.tower l E U none) W).symm ≪≫ Functor.isoWhiskerRight r W
  refine ⟨Functor.isoWhiskerLeft (integralOperationsGoodComplex l E T).ι t, ?_⟩
  intro P n
  have hr := ordinaryTowerComparison_unit l E h P.obj n
  apply HomologicalComplex.hom_ext
  intro i
  let M := P.obj.X i
  let q := completedReductionModuleUnit (pbcIntegralDatum l E) U
  have hm := hσ M n
  have hci := hc ((ordinaryIntegralPullComplex l E h).obj P.obj) n i
  change (q.app ((pbcIntegralTransportModules U l E).obj
      ((ordinaryIntegralModulePull l E h).obj M))).app (op n) ≫
      ((c.hom.app ((ordinaryIntegralPullComplex l E h).obj P.obj)).app (op n)).f i = _ at hci
  change a.moduleIso.hom.app M ≫
    (completedModulePullback h (pbcIntegralDatum l E)).map
      (((completedReductionModuleUnit (pbcIntegralDatum l E) T).app
        ((pbcIntegralTransportModules T l E).obj M)).app (op n)) ≫
    ((σ.hom.app M).app (op n) ≫
      ((c.hom.app ((ordinaryIntegralPullComplex l E h).obj P.obj)).app (op n)).f i ≫
      (pbcIntegralTransportModules U l E).map (((r.hom.app P.obj).app (op n)).f i)) = _
  have hri := congrArg (fun f ↦ f.f i) hr
  change _ ≫ _ = _ at hri
  have hmap := ((pbcIntegralTransportModules U l E).map_comp
    ((((IntegralOnSlice.augmentation l E U none).app
      ((ordinaryIntegralPullComplex l E h).obj P.obj)).app (op n)).f i)
    (((r.hom.app P.obj).app (op n)).f i)).symm.trans
      (congrArg (pbcIntegralTransportModules U l E).map hri)
  exact normalizeFive hm hci hmap

end WeilConjectures

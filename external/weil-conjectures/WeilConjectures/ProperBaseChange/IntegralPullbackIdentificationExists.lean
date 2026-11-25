/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.SmoothPurity.IntegralAmbient.NormalizedIntegralPullbackTower
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Normalized identification of ordinary integral pullback

Source: Bhatt--Scholze, Lemma 6.5.9(4), Remark 6.8.15; Stacks Tags 0941 and 099N(5).
(blueprint: lem-weil-pbc-integral-pullback-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard constantSheaf
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem coefficientProjection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) (n : ℕ) :
    (purCoefficientIso l E T).hom ≫
        completedIntegralCommRingProjectionUnrestricted l E T n =
      pbcAdicProjection T (pbcIntegralDatum l E) n ≫
        (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).inv ≫
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom := by
  apply (adicLisseForget T).map_injective
  have he := congrArg Iso.hom (purCoefficientIso_existsUnique l E T).exists.choose_spec
  change (adicLisseForget T).map (purCoefficientIso l E T).hom =
    (integralDetailedCoefficientComparison T l E).hom at he
  rw [Functor.map_comp, he]
  change (integralDetailedCoefficientComparison T l E).hom ≫
    limit.π (integralCoefficientSheafSystem l E T) (op n) = _
  exact (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec n

private theorem coefficientDirectProjection {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {U T : Scheme.{u}} (h : U ⟶ T) (n : ℕ) :
    completedCoefficientDirectImageMap h d ≫
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map (pbcAdicProjection U d n) =
      pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv ≫
        coefficientProEtaleDirectRingMap.{u, u} h
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map
          (pbcLevelConstantComparison U d n).hom := by
  let L := proEtaleSheafInverseImage h CommRingCat.{u + 1}
  let G := proEtaleSheafDirectImage h CommRingCat.{u + 1}
  let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  have hp : completedCoefficientMap h d ≫ pbcAdicProjection U d n =
      L.map (pbcAdicProjection T d n) ≫ completedFiniteCoefficientMap h d n := by
    exact limit.lift_π _ (op n)
  dsimp only [completedCoefficientDirectImageMap]
  simp only [Category.assoc]
  change adj.unit.app _ ≫ G.map (completedCoefficientMap h d) ≫ G.map _ = _
  rw [← G.map_comp, hp, G.map_comp]
  erw [adj.unit_naturality_assoc]
  unfold completedFiniteCoefficientMap
  erw [G.map_comp, G.map_comp, adj.unit_naturality_assoc]
  have hconst : adj.unit.app
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).obj
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) ≫
      G.map (proEtaleConstantInverseImageMap h CommRingCat.{u + 1} _) =
      coefficientProEtaleDirectRingMap.{u, u} h
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) := by
    change (adj.homEquiv _ _) (proEtaleConstantInverseImageMap h CommRingCat.{u + 1} _) = _
    exact (adj.homEquiv _ _).apply_symm_apply _
  simpa only [Category.assoc] using congrArg
    (fun k ↦ pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv ≫ k ≫
      G.map (pbcLevelConstantComparison U d n).hom) hconst

private theorem coefficientSquare (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T) :
    (purCoefficientIso l E T).hom ≫ IntegralAmbient.coefficientMap l E h =
      completedCoefficientDirectImageMap h (pbcIntegralDatum l E) ≫
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map
          (purCoefficientIso l E U).hom := by
  let G := proEtaleSheafDirectImage h CommRingCat.{u + 1}
  let cT := purCoefficientIso l E T
  let cU := purCoefficientIso l E U
  have hc : cT.inv ≫ completedCoefficientDirectImageMap h (pbcIntegralDatum l E) ≫
      G.map cU.hom = IntegralAmbient.coefficientMap l E h := by
    apply (IntegralAmbient.coefficientMap_existsUnique l E h).unique
      ?_ (IntegralAmbient.coefficientMap_existsUnique l E h).exists.choose_spec
    intro n
    simp only [Category.assoc]
    change cT.inv ≫ completedCoefficientDirectImageMap h (pbcIntegralDatum l E) ≫
      G.map cU.hom ≫ G.map (completedIntegralCommRingProjectionUnrestricted l E U n) = _
    rw [← G.map_comp]
    dsimp only [cU]
    rw [coefficientProjection, G.map_comp, G.map_comp]
    rw [reassoc_of% (coefficientDirectProjection (pbcIntegralDatum l E) h n)]
    change cT.inv ≫ pbcAdicProjection T (pbcIntegralDatum l E) n ≫
      (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).inv ≫
      coefficientProEtaleDirectRingMap.{u, u} h _ ≫
      G.map (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).hom ≫
      G.map ((pbcLevelConstantComparison U (pbcIntegralDatum l E) n).inv ≫
        (constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom) = _
    rw [← G.map_comp, Iso.hom_inv_id_assoc]
    change cT.inv ≫ pbcAdicProjection T (pbcIntegralDatum l E) n ≫
      (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).inv ≫
      coefficientProEtaleDirectRingMap.{u, u} h _ ≫
      ((proEtaleBaseChange h).sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology T) (ProEt.topology U)).map
          ((constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).map
            (integralCoefficientULift l E n).toCommRingCatIso.hom) = _
    have hn := ordinaryConstantMap_naturality h
      (integralCoefficientULift l E n).toCommRingCatIso.hom
    erw [← hn]
    have hp := coefficientProjection l E T n
    apply (cancel_epi cT.hom).1
    simpa only [cT, Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ coefficientProEtaleDirectRingMap.{u, u} h
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) hp.symm
  have hc' := congrArg (fun k ↦ cT.hom ≫ k) hc
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hc'.symm

private def restrictionRoundTrip
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun V ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app V).hom
        (c.hom.hom.app V).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) V
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj V)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj V))
      (by intro V W f; ext x; rfl)))
    (by intro M N f; ext V x; rfl)

private def restrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp M := by ext V x; rfl

private theorem coefficientRingSquare (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T) :
    (integralDetailedCoefficientComparison T l E).hom ≫
        ordinaryIntegralDirectRingMap l E h =
      pbcActualStructureMap h (pbcIntegralDatum l E) ≫
        (proEtaleSheafDirectImage h RingCat.{u + 1}).map
          (integralDetailedCoefficientComparison U l E).hom := by
  have he (W : Scheme.{u}) : (adicLisseForget W).map (purCoefficientIso l E W).hom =
      (integralDetailedCoefficientComparison W l E).hom := by
    have hw := congrArg Iso.hom (purCoefficientIso_existsUnique l E W).exists.choose_spec
    exact hw
  have hc := congrArg (adicLisseForget T).map (coefficientSquare l E h)
  simp only [Functor.map_comp] at hc
  change (adicLisseForget T).map (purCoefficientIso l E T).hom ≫
      (adicLisseForget T).map (IntegralAmbient.coefficientMap l E h) =
    pbcActualStructureMap h (pbcIntegralDatum l E) ≫
      (proEtaleSheafDirectImage h RingCat.{u + 1}).map
        ((adicLisseForget U).map (purCoefficientIso l E U).hom) at hc
  rw [he T, he U] at hc
  rw [← ordinaryAmbientRingMap l E h]
  exact hc

private def rightSquare (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T) :
    SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison U l E).hom ⋙
        completedModuleDirectImage h (pbcIntegralDatum l E) ≅
      ordinaryIntegralModulePush l E h ⋙ SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom := by
  let F := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison U l E).hom ⋙
      completedModuleDirectImage h (pbcIntegralDatum l E)
  let G := ordinaryIntegralModulePush l E h ⋙ SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        LinearEquiv.toModuleIso (show (F.obj M).val.obj V ≃ₗ[_] (G.obj M).val.obj V from
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ }))
        (fun {V W} f ↦ by ext x; rfl))) (fun f ↦ by ext V x; rfl)
  intro a x
  have hc := congrArg (fun k ↦ (k.hom.app V).hom a) (coefficientRingSquare l E h)
  exact congrArg (fun b ↦ b • (show M.val.obj ((proEtaleBaseChange h).op.obj V) from x))
    hc.symm

private theorem moduleComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T) :
    ∃ e : ordinaryIntegralModulePull l E h ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison U l E).hom ≅
      SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison T l E).hom ⋙
        completedModulePullback h (pbcIntegralDatum l E),
      ∀ (M : integralTowerModules l E T) (V : T.ProEt) (x : M.val.obj (op V)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange h).obj V))
          (((ordinaryIntegralModuleAdjunction l E h).unit.app M).val.app (op V) x) =
        ((pbcActualModuleAdjunction h (pbcIntegralDatum l E)).unit.app
          ((SheafOfModules.restrictScalars.{u + 1}
            (integralDetailedCoefficientComparison T l E).hom).obj M)).val.app (op V) x := by
  let F := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom
  let G := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison U l E).hom
  have : F.IsEquivalence :=
    (restrictionEquivalence (integralDetailedCoefficientComparison T l E)).isEquivalence_functor
  have : G.IsEquivalence :=
    (restrictionEquivalence (integralDetailedCoefficientComparison U l E)).isEquivalence_functor
  obtain ⟨e, he⟩ := IntegralCoefficientPresentation.square_iso
    (pbcActualModuleAdjunction h (pbcIntegralDatum l E))
    (ordinaryIntegralModuleAdjunction l E h) F G (rightSquare l E h)
  refine ⟨e.symm, ?_⟩
  intro M V x
  have hu := congrArg (fun k ↦ k.val.app (op V) x) (he M)
  change (e.hom.app M).val.app (op ((proEtaleBaseChange h).obj V))
    (((pbcActualModuleAdjunction h (pbcIntegralDatum l E)).unit.app (F.obj M)).val.app
      (op V) x) =
    (((ordinaryIntegralModuleAdjunction l E h).unit.app M).val.app (op V) x) at hu
  rw [← hu]
  exact congrArg (fun k ↦ k.val.app (op ((proEtaleBaseChange h).obj V))
    (((pbcActualModuleAdjunction h (pbcIntegralDatum l E)).unit.app (F.obj M)).val.app
      (op V) x)) (e.hom_inv_id_app M)

private theorem derivedSquareComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (R : B ⥤ D) (S : A ⥤ C) (G : C ⥤ D)
    [F.Additive] [R.Additive] [S.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (LG : DerivedCategory C ⥤ DerivedCategory D)
    (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor εF (HomotopyCategory.quasiIso A (.up ℤ))]
    [LG.IsLeftDerivedFunctor εG (HomotopyCategory.quasiIso C (.up ℤ))]
    (e : F ⋙ R ≅ S ⋙ G) :
    ∃ b : LF ⋙ R.mapDerivedCategory ≅ S.mapDerivedCategory ⋙ LG,
      ∀ P : CochainComplex A ℤ,
        b.hom.app (DerivedCategory.Q.obj P) ≫
          LG.map (S.mapDerivedCategoryFactors.hom.app P) ≫
          G.leftDerivedCounitOnComplex LG εG
            ((S.mapHomologicalComplex (.up ℤ)).obj P) =
        R.mapDerivedCategory.map (F.leftDerivedCounitOnComplex LF εF P) ≫
          R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  obtain ⟨ef, hf, _⟩ := exactDerivedCounitComparison F LF εF
  obtain ⟨eg, hg, _⟩ := exactDerivedCounitComparison G LG εG
  let b := Functor.isoWhiskerRight ef R.mapDerivedCategory ≪≫
    Functor.mapDerivedCategorySquareIso e ≪≫
    Functor.isoWhiskerLeft S.mapDerivedCategory eg.symm
  refine ⟨b, ?_⟩
  intro P
  have hgi (K : CochainComplex C ℤ) :
      eg.inv.app (DerivedCategory.Q.obj K) ≫ G.leftDerivedCounitOnComplex LG εG K =
        G.mapDerivedCategoryFactors.hom.app K := by
    rw [← hg K, Iso.inv_hom_id_app_assoc]
  change (R.mapDerivedCategory.map (ef.hom.app (DerivedCategory.Q.obj P)) ≫
      (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      eg.inv.app (S.mapDerivedCategory.obj (DerivedCategory.Q.obj P))) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  rw [← eg.inv.naturality_assoc]
  dsimp only [Functor.comp_obj]
  erw [hgi]
  rw [exactConstantComparison e P]
  simp only [← R.mapDerivedCategory.map_comp_assoc, hf]

private theorem derivedComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {U T : Scheme.{u}} (h : U ⟶ T)
    (e : ordinaryIntegralModulePull l E h ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison U l E).hom ≅
      SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison T l E).hom ⋙
        completedModulePullback h (pbcIntegralDatum l E)) :
    ∃ b : ordinaryIntegralDerivedPull l E h ⋙ integralDetailedTransport U l E ≅
        integralDetailedTransport T l E ⋙ completedOrdinaryPullback h (pbcIntegralDatum l E),
      ∀ P : CochainComplex (integralTowerModules l E T) ℤ,
        b.hom.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryPullback h (pbcIntegralDatum l E)).map
            ((pbcIntegralDetailedTransportFactors T l E).hom.app P) ≫
          completedOrdinaryPullbackComplexCounit h (pbcIntegralDatum l E)
            (((SheafOfModules.restrictScalars.{u + 1}
              (integralDetailedCoefficientComparison T l E).hom).mapHomologicalComplex
                (.up ℤ)).obj P) =
        (integralDetailedTransport U l E).map (ordinaryIntegralPullComplexCounit l E h P) ≫
          (pbcIntegralDetailedTransportFactors U l E).hom.app
            ((ordinaryIntegralPullComplex l E h).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
  let F := ordinaryIntegralModulePull l E h
  let R := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison U l E).hom
  let S := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom
  let G := completedModulePullback h (pbcIntegralDatum l E)
  have : R.IsEquivalence :=
    (restrictionEquivalence (integralDetailedCoefficientComparison U l E)).isEquivalence_functor
  have : PreservesFiniteLimits S := (integralDetailedCoefficientRestriction_exact T l E).1
  have : PreservesFiniteColimits S := (integralDetailedCoefficientRestriction_exact T l E).2
  have : PreservesFiniteLimits G := completedModulePullback_finiteLimits h (pbcIntegralDatum l E)
  have : PreservesFiniteColimits G :=
    completedModulePullback_finiteColimits h (pbcIntegralDatum l E)
  have : PreservesFiniteLimits (F ⋙ R) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (F ⋙ R) := preservesFiniteColimits_of_natIso e.symm
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F R
  have : PreservesFiniteColimits F := preservesFiniteColimits_of_reflects_of_preserves F R
  have : (ordinaryIntegralDerivedPull l E h).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E h)
      (HomotopyCategory.quasiIso (integralTowerModules l E T) (.up ℤ)) := by
    dsimp only [ordinaryIntegralDerivedPull, ordinaryIntegralPullCounit]
    infer_instance
  have := pullbackOrdinaryUniversal h (pbcIntegralDatum l E)
  obtain ⟨b, hb⟩ := derivedSquareComparison F R S G
    (ordinaryIntegralDerivedPull l E h) (completedOrdinaryPullback h (pbcIntegralDatum l E))
    (ordinaryIntegralPullCounit l E h) (completedOrdinaryPullbackCounit h (pbcIntegralDatum l E)) e
  exact ⟨b, hb⟩

/-- Coefficient restriction identifies ordinary module and derived pullback, retaining
both the adjunction-unit generators and the computation counits. This assertion
contains no completed pullback or derived inverse limit comparison.

Source: Bhatt--Scholze, Lemma 6.5.9(4), Remark 6.8.15; Stacks 03D2 and 06YY.
(blueprint: lem-weil-pbc-integral-pullback-identification).

Proof: for each finite quotient, the coefficient comparison is the normalized
ULift quotient isomorphism followed by the constant-sheaf comparison. These commute
with the constant-section direct-image maps. Compose with every quotient projection
and use the limit universal property to identify the completed direct-image ring maps.
Consequently restriction of scalars commutes with module direct image by the identity
on underlying sections. Restriction along the inverse coefficient isomorphisms is
inverse to the specified restriction. Conjugating the two module adjunctions gives
the module pullback isomorphism. The unit identity for the adjunction conjugate,
evaluated on sections, gives module_unit. The coefficient equivalences preserve
flatness and K-flatness, since they identify tensor products and acyclic complexes.
On flat-term K-flat representatives, compose the inverse of the actual pullback
computation counit, the termwise module comparison, the ordinary computation counit
and the exact restriction localization factors. These are natural isomorphisms.
Faithful restriction along good-complex localization descends them to derivedIso;
the defining composite gives derived_counit. Package these four fields. -/
theorem pbc_integral_pullback_identification_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T) :
    Nonempty (PbcProperIntegralPullbackIdentification l E h) := by
  obtain ⟨e, he⟩ := moduleComparison l E h
  -- Exactness supplies the derived comparison on all complexes.
  obtain ⟨b, hb⟩ := derivedComparison l E h e
  refine ⟨{ moduleIso := e
            module_unit := he
            derivedIso := b
            derived_counit := ?_ }⟩
  intro P
  exact hb P.obj

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.MilnorTower
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.AffineScheme
import all Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import all WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.RingTheory.ProEtale.WContractible
import all Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all Mathlib.RingTheory.RingHom.FaithfullyFlat
import all WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-! # The normalized regular unit for arbitrary completed pullback

Source: the constant-sheaf clause of `theorem-grothendieck-lefschetz-trace-formula--8`, expanded in
step 6 of `lem-zl-constant-geometric-stalk-unit`. The finite regular multiplication,
compatible quotient tower and its actual limit cone determine the entire Roos map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConstantPullbackUnitQuasiIsomorphism

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section GeneralPullbackUnitProof
attribute [local irreducible] finiteRegularIso finiteSingleRegularIso
  unrestrictedIntegralReductionExistence limit pullbackUnitLevel

private def stalkFinitePullbackRegularIso {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback.{u, u} l E g n).obj
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n)) ≅
        SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E X n) := by
  let A := CommRingCat.of (ULift.{u + 1, u}
    (Padic.coefficientExtensionRing l E (n + 1)))
  let φ : integralCoefficientSheaf.{u, u} l E Y n ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (integralCoefficientSheaf.{u, u} l E X n) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} g A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} g A
  exact asIso (SheafOfModules.pullbackObjUnitToUnit φ)

private def stalkPullbackLevelRegularIso {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    (constantWeilPullbackTower l E g).obj (op n) ≅
      (CochainComplex.singleFunctor (integralTowerModules l E X) 0).obj
        (quotientUnit l E X n) := by
  let F := integralOperationsLevelPullback.{u, u} l E g n
  let R := SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))
  exact (R.mapHomologicalComplex (.up ℤ)).mapIso
    ((F.mapHomologicalComplex (.up ℤ)).mapIso (finiteSingleRegularIso l E Y n) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app _ ≪≫
      (CochainComplex.singleFunctor _ 0).mapIso (stalkFinitePullbackRegularIso l E g n)) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app _

private theorem stalkFinitePullbackRegularIso_generator {X Y : Scheme.{u}}
    (g : X ⟶ Y) (n : ℕ) (V : Y.ProEt) :
    (stalkFinitePullbackRegularIso l E g n).hom.val.app (op ((proEtaleBaseChange g).obj V))
      (integralOperationsPullbackGenerator l E g n
        (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n)) V
          (1 : (integralCoefficientSheaf.{u, u} l E Y n).obj.obj (op V))) =
      (1 : (integralCoefficientSheaf.{u, u} l E X n).obj.obj
        (op ((proEtaleBaseChange g).obj V))) := by
  let A := CommRingCat.of (ULift.{u + 1, u}
    (Padic.coefficientExtensionRing l E (n + 1)))
  let φ : integralCoefficientSheaf.{u, u} l E Y n ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (integralCoefficientSheaf.{u, u} l E X n) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} g A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} g A
  exact pullbackUnit_one φ V
private theorem stalkPullbackLevelRegularIso_one {X Y : Scheme.{u}}
    (g : X ⟶ Y) (n : ℕ) (V : Y.ProEt) :
    ((stalkPullbackLevelRegularIso l E g n).hom.f 0).val.app
      (op ((proEtaleBaseChange g).obj V))
      (integralOperationsPullbackGenerator l E g n
        (((unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj
          (constantWeilIntegralComplex l E Y)).X 0) V
        (constantWeilReducedUnitSection l E Y n V)) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (quotientUnit l E X n)).inv.val.app
      (op ((proEtaleBaseChange g).obj V))
        (1 : (integralCoefficientSheaf.{u, u} l E X n).obj.obj
          (op ((proEtaleBaseChange g).obj V))) := by
  let F := integralOperationsLevelPullback.{u, u} l E g n
  let A := CommRingCat.of (ULift.{u + 1, u}
    (Padic.coefficientExtensionRing l E (n + 1)))
  let a := (finiteSingleRegularIso l E Y n).hom.f 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))).hom
  have hn := (coefficientProEtaleModuleAdjunction.{u, u} g A).unit.naturality a
  have h := congrArg (fun b ↦ b.val.app (op V)
    (constantWeilReducedUnitSection l E Y n V)) hn
  change integralOperationsPullbackGenerator l E g n
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n)) V
        (a.val.app (op V) (constantWeilReducedUnitSection l E Y n V)) =
    ((F.map a).val.app (op ((proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator l E g n _ V
        (constantWeilReducedUnitSection l E Y n V)) at h
  have ha : a.val.app (op V) (constantWeilReducedUnitSection l E Y n V) =
      (1 : (integralCoefficientSheaf.{u, u} l E Y n).obj.obj (op V)) := by
    change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))).hom.val.app (op V))
      (((finiteSingleRegularIso l E Y n).hom.f 0).val.app (op V) _) = _
    rw [finiteSingleRegularIso_one]
    have he := congrArg (fun f ↦ f.val.app (op V))
      (Iso.inv_hom_id (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))))
    have he' := ConcreteCategory.congr_hom he
      (1 : (integralCoefficientSheaf.{u, u} l E Y n).obj.obj (op V))
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using! he'
  rw [ha] at h
  let R := SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))
  have hf : (stalkPullbackLevelRegularIso l E g n).hom.f 0 =
      R.map (F.map a ≫ (stalkFinitePullbackRegularIso l E g n).hom) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (quotientUnit l E X n)).inv := by
    simp only [stalkPullbackLevelRegularIso, Iso.trans_hom, Functor.mapIso_hom,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
    dsimp only [R, F, a]
    simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [hf]
  change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (quotientUnit l E X n)).inv.val.app
    (op ((proEtaleBaseChange g).obj V))
      ((stalkFinitePullbackRegularIso l E g n).hom.val.app _ ((F.map a).val.app _ _)) = _
  rw [← h, stalkFinitePullbackRegularIso_generator]
attribute [local irreducible] stalkFinitePullbackRegularIso stalkPullbackLevelRegularIso

private theorem stalkPullbackLevelRegularIso_projection {X Y : Scheme.{u}}
    (g : X ⟶ Y) (n : ℕ) :
    pullbackUnitLevel l E g n ≫ (stalkPullbackLevelRegularIso l E g n).hom =
      (CochainComplex.singleFunctor _ 0).map (constantCoefficientProjection l E X n) := by
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  apply regular_hom_ext l E X ((proEtaleBaseChange g).obj T)
    (hT.isTerminalObj (proEtaleBaseChange g) T)
  change ((stalkPullbackLevelRegularIso l E g n).hom.f 0).val.app _
    (((pullbackUnitLevel l E g n).f 0).val.app _ _) = _
  rw [pullbackUnitLevel_generator, stalkPullbackLevelRegularIso_one]
  change _ = (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (quotientUnit l E X n)).inv.val.app _
      ((constantCoefficientProjection l E X n).val.app _
        (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X))).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X))).inv).val.app
              _
              (1 : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj _)))
  simp only [Iso.hom_inv_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  congr 1
  change 1 = (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n).hom.app _ 1 * 1
  simp only [map_one, mul_one]

private def stalkPullbackRegularTowerIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    constantWeilPullbackTower l E g ≅ quotientDiagram l E X ⋙
      CochainComplex.singleFunctor (integralTowerModules l E X) 0 := by
  let S := CochainComplex.singleFunctor (integralTowerModules l E X) 0
  have : PreservesFiniteColimits S :=
    inferInstanceAs (PreservesFiniteColimits
      (HomologicalComplex.single (integralTowerModules l E X) (.up ℤ) 0))
  refine compatibleTowerIso _ _ (constantWeilIntegralComplex l E X)
    (pullbackUnitLevel l E g) (fun n ↦ S.map (quotientProjection l E X n))
    ?_ ?_ (stalkPullbackLevelRegularIso l E g) ?_ ?_
  · intro n
    simpa only [constantWeilPullbackTower, integralOperationsPullbackTowerFunctor,
      Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ] using
        pullbackUnitLevel_transition l E g n
  · intro n
    change S.map (quotientProjection l E X (n + 1)) ≫
      S.map ((quotientDiagram l E X).map (homOfLE n.le_succ).op) = _
    rw [← S.map_comp]
    simpa only [quotientDiagram, Functor.ofOpSequence_map_homOfLE_succ] using
      congrArg S.map (quotientProjection_step l E X n)
  · intro n
    exact stalkPullbackLevelRegularIso_projection l E g n
  · intro n
    have := quotientProjection_epi l E X n
    infer_instance

private def stalkPullbackRegularConeIsLimit {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsLimit (pullbackRegularCone l E g) := by
  let S := CochainComplex.singleFunctor (integralTowerModules l E X) 0
  haveI : PreservesFiniteColimits S :=
    inferInstanceAs (PreservesFiniteColimits
      (HomologicalComplex.single (integralTowerModules l E X) (.up ℤ) 0))
  haveI : PreservesLimitsOfShape ℕᵒᵖ S :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (HomologicalComplex.single (integralTowerModules l E X) (.up ℤ) 0))
  let e := stalkPullbackRegularTowerIso l E g
  apply (IsLimit.postcomposeHomEquiv e (pullbackRegularCone l E g)).toFun
  exact (isLimitOfPreserves S (quotientConeIsLimit l E X)).ofIsoLimit
    (Cone.ext (Iso.refl _) (by
      intro n
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Iso.refl_hom, Category.id_comp]
      exact (stalkPullbackLevelRegularIso_projection l E g n.unop).symm))
private theorem stalkPullbackRoos_epi {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Epi (constantWeilPullbackRoosEndomorphism l E g) := by
  let M := quotientDiagram l E X
  have ht (n : ℕ) : Epi (M.map (homOfLE n.le_succ).op) := by
    simpa only [M, quotientDiagram, Functor.ofOpSequence_map_homOfLE_succ]
      using quotientStep_epi l E X n
  have h := AlgebraicGeometry.ProEtale.milnor_epimorphic.{u, u, _} X
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) M ht
  have : HasCountableProducts (CochainComplex (integralTowerModules l E X) ℤ) :=
    ⟨fun _ _ ↦ HomologicalComplex.instHasLimitsOfShape⟩
  exact singleTower_epi M h.1 _ (stalkPullbackRegularTowerIso l E g)
private theorem stalkChainUnitCandidate_quasiIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    QuasiIso (chainUnitCandidate l E g) := by
  let F := constantWeilPullbackTower l E g
  let P := Fan.mk (∏ᶜ fun n ↦ F.obj (op n)) (fun n ↦ Pi.π _ n)
  obtain ⟨hz, ⟨hk⟩⟩ := AlgebraicGeometry.ProEtale.tower_kernel F
    (pullbackRegularCone l E g) (stalkPullbackRegularConeIsLimit l E g)
    P (productIsProduct _) (pullbackUnitProduct l E g)
    (constantWeilPullbackRoosEndomorphism l E g)
    (fun n ↦ Pi.lift_comp_π (pullbackUnitLevel l E g) n)
    (fun n ↦ (towerTransitionEndomorphism_eq_iff _ _).1 rfl n)
  let S := ShortComplex.mk (pullbackUnitProduct l E g)
    (constantWeilPullbackRoosEndomorphism l E g) hz
  have : Mono S.f := mono_of_isLimit_fork hk
  have : Epi S.g := stalkPullbackRoos_epi l E g
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel hk }
  exact AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S hS
    (by simp [S, pullbackUnitProduct_zero])

end GeneralPullbackUnitProof

/-- Every strict regular unit with the finite generator and zero shifted-component
normalizations is a quasi-isomorphism after localization.

Source: constant-sheaf clause of `theorem-grothendieck-lefschetz-trace-formula--8`, reviewed
expansion step 6 (blueprint: lem-zl-constant-pullback-unit-quasi-isomorphism).

Proof: finite pullback multiplication identifies the regular module with the target
regular module. The base-change functor preserves the terminal object and hence is
final, so the regular-unit multiplication is invertible for arbitrary scheme maps.
Its adjunction generator is one. Naturality and linearity identify every unit projection
with the actual quotient projection. Thus these isomorphisms form an isomorphism of
towers and carry the completed coefficient cone to a limit cone of the pulled tower.
The quotient transitions are epic. The Milnor theorem and the product comparison
make one minus shift epic on the pulled tower of complexes. Its kernel is the limit
cone, so the zero shifted-component cocone lift is a quasi-isomorphism. Uniqueness
of the normalized chain unit identifies the given map with that lift. Localization
therefore makes precisely the given map invertible. This includes empty schemes and
the first positive coefficient quotient. -/
theorem normalizedChainUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E f).obj
          (constantWeilIntegralComplex l E Y))
    (hη :
      (∀ (m : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
          (Pi.π (fun j ↦ (constantWeilPullbackTower l E f).obj (op j)) m).f 0).val.app
            (op ((proEtaleBaseChange f).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange f).obj V)) =
        integralOperationsPullbackGenerator l E f m
          (((unrestrictedIntegralFiniteComplex l E Y m).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y m V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E f)).v i (i - 1) (by omega) = 0)) :
    IsIso (DerivedCategory.Q.map η) := by
  have he : η = chainUnitCandidate l E f :=
    normalized_chainUnit_unique l E f η hη
  rw [he]
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (stalkChainUnitCandidate_quasiIso l E f)

end WeilConjectures.ConstantPullbackUnitQuasiIsomorphism

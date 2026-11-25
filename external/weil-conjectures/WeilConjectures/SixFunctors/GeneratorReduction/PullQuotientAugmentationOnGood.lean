/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SixFunctors.GeneratorReduction.PullQuotientOrdinaryProjection
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
/-! # Pullback transpose on good representatives

Source: current blueprint fix-prop-coherence, primitive comparisons
(blueprint: lem-sf-pull-quotient-augmentation-on-good).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem roosUnit_natural (W : Scheme.{u})
    {P Q : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ} (a : P ⟶ Q) :
    ((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).map a ≫
        pullbackTensorRoosUnit l E W Q =
      pullbackTensorRoosUnit l E W P ≫ integralOperationsRoosMap
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a) := by
  have hz (T : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
      pullbackTensorRoosAugmentation l E W T ≫
        towerTransitionEndomorphism
          (integralOperationsTowerStep
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj T)) = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa using pullbackTensorRoosAugmentation_condition l E W T
  have hn :
      ((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).map a ≫
          pullbackTensorRoosAugmentation l E W Q =
        pullbackTensorRoosAugmentation l E W P ≫ Limits.Pi.map
          (fun n ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app
            (op n)) := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [pullbackTensorRoosAugmentation, Category.assoc, Pi.lift_comp_π, Limits.Pi.map_π,
      Pi.lift_comp_π_assoc]
    exact (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).naturality a
  dsimp only [pullbackTensorRoosUnit, integralOperationsRoosMap]
  rw [arrowConeMap]
  exact completedCoconeLift_natural (integralTowerModules l E W) _ _ _ _
    (integralOperationsRoos_square
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a)) _ _ _ (hz P) (hz Q) hn

private theorem towerUnit_roos (W : Scheme.{u})
    (Z : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    (pullbackTensorConstantLimit l E W).rightDerivedFunctorUnitQ Z ≫
        (pullbackTensorRoosModel l E W).hom.app Z =
      DerivedCategory.Q.map (pullbackTensorRoosUnit l E W Z) := by
  obtain ⟨I, hI, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective Z
  let : I.IsKInjective := hI
  let : QuasiIso a := ha
  let R : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ ⥤
      DerivedCategory (integralTowerModules l E W) :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let : IsIso ((pullbackTensorTowerQ l E W ⋙ coefficientConstantTowerLimit l E W).map a) := by
    change IsIso ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map a))
    infer_instance
  let : IsIso (R.map a) :=
    (NatIso.isIso_map_iff (pullbackTensorRoosModel l E W) a).1 inferInstance
  apply (cancel_mono (R.map a)).1
  have hn := (pullbackTensorRoosModel l E W).hom.naturality a
  change (coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map a) ≫
    (pullbackTensorRoosModel l E W).hom.app I =
      (pullbackTensorRoosModel l E W).hom.app Z ≫ R.map a at hn
  rw [Category.assoc, ← hn, ← Category.assoc]
  erw [← Functor.rightDerivedFunctorUnitQ_naturality]
  have hi := (pullbackTensorRoosModel_existsUnique l E W).exists.choose_spec I
  change (pullbackTensorRoosModel l E W).hom.app I = _ at hi
  rw [Category.assoc, hi, Functor.rightDerivedFunctorUnitQ_eq,
    Iso.inv_hom_id_assoc, ← DerivedCategory.Q.map_comp]
  change _ = DerivedCategory.Q.map (pullbackTensorRoosUnit l E W Z) ≫
    DerivedCategory.Q.map (integralOperationsRoosMap
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a))
  rw [← DerivedCategory.Q.map_comp, roosUnit_natural]

private theorem limitUnit_roos (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    pullbackTensorLimitUnit l E W C ≫ (pullbackTensorLimitRoos l E W C).hom =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app C) ≫
        DerivedCategory.Q.map (pullbackTensorRoosUnit l E W
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) := by
  dsimp only [pullbackTensorLimitUnit, pullbackTensorLimitRoos, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(coefficientConstantTowerLimit l E W).map_id]
  erw [Category.id_comp]
  have h := towerUnit_roos l E W
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)
  exact congrArg (fun k ↦ DerivedCategory.Q.map
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceRestriction l E W ⋙
        pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app C) ≫ k) h

private theorem limitUnit_natural (W : Scheme.{u})
    {C D : CochainComplex (coefficientSequenceModules l E W) ℤ} (a : C ⟶ D) :
    DerivedCategory.Q.map
        (((pullbackTensorOrdinaryLimit l E W).mapHomologicalComplex (.up ℤ)).map a) ≫
        pullbackTensorLimitUnit l E W D =
      pullbackTensorLimitUnit l E W C ≫
        (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map a) := by
  let e := Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E W ⋙
      pullbackTensorConstantLimit l E W)) (.up ℤ)
  have he := e.inv.naturality a
  dsimp only [Functor.comp_map] at he
  have hn := (pullbackTensorConstantLimit l E W).rightDerivedFunctorUnitQ_naturality
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map a)
  have hf := (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.naturality a
  dsimp only [Functor.comp_map] at hf
  dsimp only [pullbackTensorLimitUnit]
  rw [← DerivedCategory.Q.map_comp_assoc]
  erw [he, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  erw [← Functor.map_comp, hf, Functor.map_comp]
  rfl

private theorem reduction_transpose_roos (W : Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
      P.obj ⟶ C) :
    (pullbackTensorCalculus l E W).adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E W).map
          ((pullbackTensorReductionModel l E W).hom.app P ≫ DerivedCategory.Q.map a) ≫
        (pullbackTensorLimitRoos l E W C).hom =
      DerivedCategory.Q.map
        (((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).unit.app
          P.obj ≫
          ((pullbackTensorOrdinaryLimit l E W).mapHomologicalComplex (.up ℤ)).map a ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (coefficientSequenceRestriction l E W ⋙
              pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app C ≫
          pullbackTensorRoosUnit l E W
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) := by
  have h := (pullbackTensorReductionModel_existsUnique l E W).exists.choose_spec P
  change (pullbackTensorCalculus l E W).adjunction.homEquiv _ _
    ((pullbackTensorReductionModel l E W).hom.app P) = _ at h
  rw [Adjunction.homEquiv_unit] at h
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% h]
  erw [← reassoc_of% (limitUnit_natural l E W a)]
  rw [limitUnit_roos]
  simp only [DerivedCategory.Q.map_comp]

private theorem inl_map
    {A : Type*} [Category* A] [Abelian A]
    {K₁ K₂ L₁ L₂ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : φ₁ ≫ b = a ≫ φ₂) (i : ℤ) :
    (CochainComplex.mappingCocone.inl φ₁).v i i (add_zero i) ≫
        ((CochainComplex.mappingCone.map φ₁ φ₂ a b h)⟦(-1 : ℤ)⟧').f i =
      a.f i ≫ (CochainComplex.mappingCocone.inl φ₂).v i i (add_zero i) := by
  simp [CochainComplex.mappingCocone.inl,
    CochainComplex.HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    CochainComplex.mappingCone.map]

private theorem cocone_lifts_map_eq
    {A : Type*} [Category* A] [Abelian A]
    {C D K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex A ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
    (a₁ : K₁ ⟶ K₃) (b₁ : L₁ ⟶ L₃) (a₂ : K₂ ⟶ K₃) (b₂ : L₂ ⟶ L₃)
    (h₁ : φ₁ ≫ b₁ = a₁ ≫ φ₃) (h₂ : φ₂ ≫ b₂ = a₂ ≫ φ₃)
    (α : C ⟶ D) (u : D ⟶ K₁) (v : C ⟶ K₂)
    (hu : u ≫ φ₁ = 0) (hv : v ≫ φ₂ = 0)
    (hn : α ≫ u ≫ a₁ = v ≫ a₂) :
    α ≫ CochainComplex.mappingCocone.lift φ₁ u 0 (by simp [hu]) ≫
        (CochainComplex.mappingCone.map φ₁ φ₃ a₁ b₁ h₁)⟦(-1 : ℤ)⟧' =
      CochainComplex.mappingCocone.lift φ₂ v 0 (by simp [hv]) ≫
        (CochainComplex.mappingCone.map φ₂ φ₃ a₂ b₂ h₂)⟦(-1 : ℤ)⟧' := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f]
  rw [completedCoconeLift_f _ _ _ hu i, completedCoconeLift_f _ _ _ hv i]
  simp only [Category.assoc, inl_map]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun z ↦ z.f i ≫
      (CochainComplex.mappingCocone.inl φ₃).v i i (add_zero i)) hn

private theorem ordinary_roos
    (a : IntegralSystemRealization.OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : OpenFactorCoherence.Pull l E f)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    let R := (OpenFactorCoherence.pullCx l E f).obj P
    let C := ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
      (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P)
    let Z := ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C
    ((pullbackTensorOrdinaryAdjunction l E X).mapHomologicalComplex (.up ℤ)).unit.app R ≫
        ((pullbackTensorOrdinaryLimit l E X).mapHomologicalComplex (.up ℤ)).map
          (a.reductionPullComplex l E f P) ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E X ⋙
            pullbackTensorConstantLimit l E X)) (.up ℤ)).inv.app C ≫
        pullbackTensorRoosUnit l E X Z ≫
        integralOperationsRoosMap (pullbackTensorPullbackTower l E f P).hom =
      IntegralOnSlice.roosUnit l E X none R ≫
        integralOperationsRoosMap (p.tower.hom.app P) := by
  intro R C Z
  let b := ((pullbackTensorOrdinaryAdjunction l E X).mapHomologicalComplex (.up ℤ)).unit.app
    R ≫ ((pullbackTensorOrdinaryLimit l E X).mapHomologicalComplex (.up ℤ)).map
      (a.reductionPullComplex l E f P) ≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceRestriction l E X ⋙
        pullbackTensorConstantLimit l E X)) (.up ℤ)).inv.app C
  have hn : b ≫ pullbackTensorRoosAugmentation l E X Z ≫
        Limits.Pi.map (fun n ↦ (pullbackTensorPullbackTower l E f P).hom.app (op n)) =
      IntegralOnSlice.productAugmentation l E X none R ≫
        Limits.Pi.map (fun n ↦ (p.tower.hom.app P).app (op n)) := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, pullbackTensorRoosAugmentation,
      IntegralOnSlice.productAugmentation, Limits.Pi.map_π, Pi.lift_comp_π_assoc]
    exact pullQuotientOrdinaryProjection l E a f p P n
  have hz : pullbackTensorRoosAugmentation l E X Z ≫
      towerTransitionEndomorphism
        (integralOperationsTowerStep
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj Z)) = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa using pullbackTensorRoosAugmentation_condition l E X Z
  have hr : IntegralOnSlice.productAugmentation l E X none R ≫
      towerTransitionEndomorphism
        (integralOperationsTowerStep ((IntegralOnSlice.tower l E X none).obj R)) = 0 := by
    apply CochainComplex.HomComplex.Cochain.ofHom_injective
    simpa using IntegralOnSlice.roosUnit_condition l E X none R
  change b ≫ pullbackTensorRoosUnit l E X Z ≫ _ = _
  dsimp only [pullbackTensorRoosUnit, IntegralOnSlice.roosUnit, integralOperationsRoosMap]
  erw [arrowConeMap _ _ _ _ _
      (integralOperationsRoos_square (pullbackTensorPullbackTower l E f P).hom),
    arrowConeMap _ _ _ _ _ (integralOperationsRoos_square (p.tower.hom.app P))]
  exact cocone_lifts_map_eq _ _ _ _ _ _ _ _ _ b _ _ hz hr hn

/-- The scalar-adjunction transpose of ordinary pullback/reduction is the
strict pullback of the quotient Roos augmentation on a good complex.
Source: current blueprint fix-prop-coherence.proof.md, maps-used sentence;
Stacks 03D7, 07A6, 0941.

Proof: Expand the reference pullback model. RealizationModel.model and
naturality of the reconstruction unit replace the derived reduction/pullback
comparison by the localization of the ordinary adjoint-conjugate map. The Hom
normalization of pullbackTensorReductionModel identifies its scalar transpose
with the ordinary quotient unit followed by pullbackTensorLimitUnit.
For an arbitrary tower, transport the K-injective normalization of
pullbackTensorRoosModel along a K-injective resolution; naturality of the
ordinary projections and the explicit zero-homotopy cone lift give the required
formula on that resolution and hence on the original tower. Cancel the scalar
restriction localization factors. The remaining ordinary cochain identity is
checked after every product projection by pullQuotientOrdinaryProjection.
The zero second coordinates and the first-coordinate formula for the shifted
mapping-cone map identify the whole Roos lifts. Localize this cochain identity
and compose with the exact ordinary-pullback localization factor. No property
of completionUnit, descent, or Pull.model is used.
(blueprint: lem-sf-pull-quotient-augmentation-on-good). -/
theorem pullQuotientTranspose_onGood
    (system : IntegralSystemRealization.Operations l E)
    (realization : IntegralSystemRealization.RealizationModel l E system)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : OpenFactorCoherence.Pull l E f)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (IntegralSystemRealization.calculus l E X).adjunction.unit.app
        ((IntegralSystemRealization.ringedPull l E f).obj (DerivedCategory.Q.obj P.obj)) ≫
      (coefficientSequenceLimit l E X).map
        ((realization.reductionPull f).hom.app (DerivedCategory.Q.obj P.obj)) ≫
      (pullbackTensorReferencePullbackModel l E f P).hom =
      (IntegralSystemRealization.integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app
          P.obj ≫
        DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none
          ((OpenFactorCoherence.pullCx l E f).obj P.obj)) ≫
        DerivedCategory.Q.map (integralOperationsRoosMap (p.tower.hom.app P.obj)) := by
  let R : (integralOperationsGoodComplex l E X).FullSubcategory :=
    ⟨(OpenFactorCoherence.pullCx l E f).obj P.obj, p.good P.obj P.property⟩
  let C := ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
    (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj)
  let c := (IntegralSystemRealization.integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app
    P.obj
  let v := (realization.reductionPull f).hom.app (DerivedCategory.Q.obj P.obj)
  let m := (IntegralSystemRealization.pull l E f).map
    ((pullbackTensorReductionModel l E Y).hom.app P)
  let d := (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
    (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj)
  let L := coefficientSequenceLimit l E X
  have hm := realization.model f P R.property
  have hn := (IntegralSystemRealization.calculus l E X).adjunction.unit.naturality c
  change c ≫ (pullbackTensorCalculus l E X).adjunction.unit.app
      (DerivedCategory.Q.obj R.obj) =
    (IntegralSystemRealization.calculus l E X).adjunction.unit.app
      ((IntegralSystemRealization.ringedPull l E f).obj (DerivedCategory.Q.obj P.obj)) ≫
      L.map ((pullbackTensorCalculus l E X).reduction.map c) at hn
  calc
    _ = (IntegralSystemRealization.calculus l E X).adjunction.unit.app
          ((IntegralSystemRealization.ringedPull l E f).obj (DerivedCategory.Q.obj P.obj)) ≫
        L.map (v ≫ m ≫ d) ≫ (pullbackTensorLimitRoos l E X C).hom ≫
          DerivedCategory.Q.map
            (integralOperationsRoosMap (pullbackTensorPullbackTower l E f P.obj).hom) := by
      simp only [pullbackTensorReferencePullbackModel, Iso.trans_hom,
        Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc,
        v, m, d, L, C, IntegralSystemRealization.pull, integralOperationsRoosFunctor]
    _ = c ≫ ((pullbackTensorCalculus l E X).adjunction.unit.app
          (DerivedCategory.Q.obj R.obj) ≫
        L.map ((pullbackTensorReductionModel l E X).hom.app R ≫
          DerivedCategory.Q.map (realization.ordinary.reductionPullComplex l E f P.obj)) ≫
        (pullbackTensorLimitRoos l E X C).hom) ≫
          DerivedCategory.Q.map
            (integralOperationsRoosMap (pullbackTensorPullbackTower l E f P.obj).hom) := by
      change v ≫ m ≫ d = _ at hm
      rw [hm, Functor.map_comp]
      simp only [Category.assoc]
      rw [← reassoc_of% hn]
    _ = _ := by
      rw [reduction_transpose_roos]
      simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
      rw [ordinary_roos]

end WeilConjectures.GeneratorReduction

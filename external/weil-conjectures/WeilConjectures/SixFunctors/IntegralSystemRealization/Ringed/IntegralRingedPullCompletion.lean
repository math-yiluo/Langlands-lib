/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullModel
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Normalized completion of one ordinary pullback

Source: Stacks 099N, 07A4; fix-prop-coherence, pullback-model step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open OpenFactorCoherence

private abbrev ordinaryRingedPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModulePullback f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f)

private theorem ringedAmbientRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingDirectImageMap f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) =
        IntegralAmbient.coefficientMap l E f := by
  have h : proEtaleRingDirectImageMap f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) =
        sfCompletedCoefficientMap l E f :=
    (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _ |>.apply_symm_apply _
  rw [h]
  apply (IntegralAmbient.coefficientMap_existsUnique l E f).unique
  · exact (sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec
  · exact (IntegralAmbient.coefficientMap_existsUnique l E f).exists.choose_spec

private def ringedAmbientPushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModuleDirectImage f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f) ≅
        IntegralAmbient.push l E f :=
  SheafOfModules.pushforwardCongr
    (congrArg ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (ringedAmbientRingMap l E f))

private def ringedAmbientPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryRingedPull l E f ≅ IntegralAmbient.pull l E f :=
  (proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).leftAdjointUniq
      ((IntegralAmbient.adjunction l E f).ofNatIsoRight (ringedAmbientPushIso l E f).symm)

private theorem ringedAmbientPullIso_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((ringedAmbientPullIso l E f).hom.app M).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app (op V) x) =
      IntegralAmbient.pullSection l E f M V x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull f))
    ((IntegralAmbient.adjunction l E f).ofNatIsoRight (ringedAmbientPushIso l E f).symm) M
  exact congrArg (fun a ↦ a.val.app (op V) x) h

private def ringedAmbientComplexIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullCx l E f ≅ IntegralAmbient.pullComplex l E f := by
  let := IntegralAmbient.pull_additive l E f
  exact NatIso.mapHomologicalComplex (ringedAmbientPullIso l E f) (.up ℤ)

private theorem ringedPull_good {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Cx l E Y) (hP : IntegralOnSlice.Good l E Y none P) :
    IntegralOnSlice.Good l E X none ((pullCx l E f).obj P) := by
  let ec := (ringedAmbientComplexIso l E f).app P
  have h := IntegralAmbient.pull_good l E f P hP
  exact ⟨SheafOfModules.kFlat_iso_independent
    (completedIntegralCommRingSheafUnrestricted l E X) ec.symm h.1,
    fun i ↦ SheafOfModules.flatOnSite_of_iso
      (completedIntegralCommRingSheafUnrestricted l E X)
      ((HomologicalComplex.eval _ _ i).mapIso ec.symm) (h.2 i)⟩

private def ringedPullTower {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullCx l E f ⋙ IntegralOnSlice.tower l E X none ≅
      integralOperationsPullbackTowerFunctor l E f :=
  Functor.isoWhiskerRight (ringedAmbientComplexIso l E f)
    (IntegralOnSlice.tower l E X none) ≪≫ IntegralAmbient.pullTowerIso l E f

private theorem ringedPullTower_generators {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Cx l E Y) (n : ℕ) (i : ℤ) (V : Y.ProEt)
    (x : (P.X i).val.obj (op V)) :
    ((((ringedPullTower l E f).hom.app P).app (op n)).f i).val.app
        (op ((proEtaleBaseChange f).obj V))
      (IntegralOnSlice.generator l E X none n (((pullCx l E f).obj P).X i)
        (op ((proEtaleBaseChange f).obj V)) 1
        (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull f)).unit.app (P.X i)).val.app
            (op V) x)) =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
  change ((((IntegralAmbient.pullTowerIso l E f).hom.app P).app (op n)).f i).val.app
    (op ((proEtaleBaseChange f).obj V))
    (((IntegralOnSlice.reduction l E X none n).map
      ((ringedAmbientPullIso l E f).hom.app (P.X i))).val.app
        (op ((proEtaleBaseChange f).obj V)) _) = _
  have hg := IntegralOnSlice.generator_map l E X none n
    ((ringedAmbientPullIso l E f).hom.app (P.X i))
    (op ((proEtaleBaseChange f).obj V)) 1
    (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f)).unit.app (P.X i)).val.app (op V) x)
  let q := (((((IntegralAmbient.pullTowerIso l E f).hom.app P).app (op n)).f i).val.app
    (op ((proEtaleBaseChange f).obj V)))
  refine (congrArg (fun z ↦ q z) hg).trans ?_
  have hu := ringedAmbientPullIso_unit l E f (P.X i) V x
  refine (congrArg (fun z ↦ q
    (IntegralOnSlice.generator l E X none n ((IntegralAmbient.pull l E f).obj (P.X i))
      (op ((proEtaleBaseChange f).obj V)) 1 z)) hu).trans ?_
  have h := (IntegralAmbient.pullTowerModel l E f).exists.choose_spec P n i V 1 x
  have hc : IntegralAmbient.finitePullSection l E f n P i V 1 x =
      integralOperationsPullbackGenerator l E f n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) := by
    dsimp only [IntegralAmbient.finitePullSection]
    exact one_smul _ _
  exact h.trans hc

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- The completion presentation of one geometric pullback. No tensor or open
comparison is asserted.
Source: Stacks 099N, 07A4; fix-prop-coherence, pullback-model step
(blueprint: lem-sf-integral-ringed-pull-completion).

Proof: ordinary inverse image and the specified coefficient isomorphism preserve
flat terms and K-flat complexes, hence the good classes in Pull. Associate the
scalar tensors before taking the Roos construction. On every quotient level this
identifies pullback of the quotient tensor with quotient tensor of pullback,
using b tensor (1 tensor x) mapped to 1 tensor (b tensor x). Balancing and
naturality of scalar units show compatibility with every transition, giving the
strict tower isomorphism and its generators equation. Apply the Roos functor to
that isomorphism and descend along good-complex localization. This gives the
comparison from completion of ordinary pullback to integralDerivedPullback.
The descent equation is exactly Pull.model. Assemble these data into Pull.
The identity, empty scheme and zero complex satisfy the same formulas. -/
theorem integralRingedPullCompletion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (OpenFactorCoherence.Pull l E f) := by
  let G := integralOperationsGoodComplex l E Y
  let H := ObjectProperty.lift (IntegralOnSlice.Good l E X none) (G.ι ⋙ pullCx l E f)
    (fun P ↦ ringedPull_good l E f P.obj P.property)
  let e : integralOperationsGoodLocalization l E Y ⋙ star l E f ≅
      H ⋙ IntegralOnSlice.qGood l E X none := by
    with_unfolding_all
      exact Functor.isoWhiskerLeft G.ι
        (ordinaryRingedPull l E f).mapDerivedCategoryFactors
  let b : H ⋙ IntegralOnSlice.roosGood l E X none ≅
      integralOperationsPullbackOnGood l E f := by
    with_unfolding_all
      exact IntegralAmbient.liftedTowerRoosComparison
        (IntegralOnSlice.Good l E X none) G.ι (pullCx l E f)
        (fun P ↦ ringedPull_good l E f P.obj P.property)
        (IntegralOnSlice.tower l E X none) (integralOperationsPullbackTowerFunctor l E f)
        integralOperationsRoosFunctor DerivedCategory.Q (ringedPullTower l E f)
  let ff := Classical.choice (good_whisker_fullyFaithful l E Y (D l E X))
  let a := IntegralAmbient.descendCompletion (integralOperationsGoodLocalization l E Y) ff
    (C l E X) (eta l E X) e (IntegralOnSlice.completionComparison l E X none) b
    (integralDerivedPullbackComparison l E f)
    (fun P ↦ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none P.obj))
    (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec
  refine ⟨{ source_good := fun _ hP ↦ hP
            good := ringedPull_good l E f
            tower := ringedPullTower l E f
            generators := ringedPullTower_generators l E f
            comparison := a.comparison
            model := ?_ }⟩
  intro P hP
  let p : G.FullSubcategory := ⟨P, hP⟩
  have h := a.normalization p
  have hb : b.hom.app p = DerivedCategory.Q.map
      (integralOperationsRoosMap ((ringedPullTower l E f).hom.app P)) := by
    with_unfolding_all
      exact IntegralAmbient.liftedTowerRoosComparison_app
        (IntegralOnSlice.Good l E X none) G.ι (pullCx l E f)
        (fun P ↦ ringedPull_good l E f P.obj P.property)
        (IntegralOnSlice.tower l E X none) (integralOperationsPullbackTowerFunctor l E f)
        integralOperationsRoosFunctor DerivedCategory.Q (ringedPullTower l E f) p
  rw [hb] at h
  with_unfolding_all exact h

end WeilConjectures.IntegralSystemRealization

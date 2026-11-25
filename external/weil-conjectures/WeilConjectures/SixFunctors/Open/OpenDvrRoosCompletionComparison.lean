/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import WeilConjectures.SixFunctors.Open.OpenDvrAugmentedTowerComparison
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedReductionAugmentationIso
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # The normalized DVR quotient completion and integral Roos completion

Source: Stacks Tags 093M and 0941.
(blueprint: lem-sf-open-dvr-roos-completion-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
  IntegralOnSlice.hasDerived integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsSiteSmall integralOperationsCommHasDerivedCategory
  CompletedCoefficientPushforward.modAbelian CompletedCoefficientPushforward.hasDerived in
attribute [local instance 3000] integralTowerHasDerivedCategory in
private theorem dvrRoosRepresentativeComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (Q : IntegralOnSlice.Cx.{u, u} l E T none)
    (B : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ)
    (e : B.asFunctor ≅ (IntegralOnSlice.tower.{u, u} l E T none).obj Q)
    (a : Q ⟶ ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
      (.up ℤ)).obj B)
    (ha : ∀ n : ℕ,
      a ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app B ≫
        e.hom.app (op n) = ((IntegralOnSlice.augmentation.{u, u} l E T none).app Q).app (op n)) :
    ∃ j : (coefficientConstantTowerLimit.{u, u} l E T).obj (DerivedCategory.Q.obj B) ≅
        DerivedCategory.Q.obj (IntegralOnSlice.roos.{u, u} l E T none |>.obj Q),
      (DerivedCategory.Q.map a ≫ derivedLimitComplexComparison
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
        (coefficientConstantTowerLimit.{u, u} l E T)
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B) ≫ j.hom =
        DerivedCategory.Q.map (IntegralOnSlice.roosUnit.{u, u} l E T none Q) := by
  classical
  let A := scalarReductionSource.{u, u} l E T
  let L : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let RF := coefficientConstantTowerLimit.{u, u} l E T
  let η : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  have hηapp (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      derivedLimitComplexComparison L RF L.rightDerivedFunctorUnit I = η.app I := by
    simp [η, derivedLimitComplexComparison, Functor.rightDerivedFunctorUnitQ,
      Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    rfl
  have hη : RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply (CategoryTheory.derives L).isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (L.rightDerivedFunctorUnitQ I.obj)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  let : HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)) :=
    ProEt.products_exact.{u, u, 0} T
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T) ℕ
  obtain ⟨CF, κ, hCF, _⟩ := strictRoosDerivation.{u + 1, u, u, u + 2}
    (ProEt.topology T) (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)
    (fun U x y ↦ completedIntegralCoefficient_mul_commUnrestricted l E T U x y)
  let := hCF
  let limIso := CompletedCoefficientPushforward.limitModelIso (B := A)
  let α := (Functor.isoWhiskerRight limIso.symm DerivedCategory.Q).hom ≫ η
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  let : (DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)).IsLocalization W := by
    dsimp only [W]
    infer_instance
  let : (DerivedCategory.Q (C := ℕᵒᵖ ⥤ ringedSiteModules.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T))).IsLocalization W := by
    exact inferInstanceAs ((DerivedCategory.Q (C := ℕᵒᵖ ⥤ ringedSiteModules.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T))).IsLocalization
        (HomologicalComplex.quasiIso _ (.up ℤ)))
  let : CF.IsRightDerivedFunctor (roosDerivedUnit κ) W := by exact hCF
  have hα : RF.IsRightDerivedFunctor α W := by
    rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
    exact (Functor.isLeftKanExtension_iff_of_iso₂ α η
      (Functor.isoWhiskerRight limIso.symm DerivedCategory.Q) (Iso.refl _)
      (by simp [α])).mpr
        (Functor.IsRightDerivedFunctor.isLeftKanExtension RF η W)
  let ρ := CF.rightDerivedUnique RF (roosDerivedUnit κ) α W
  have hn : DerivedCategory.Q.map (roosι B) ≫ κ.hom.app B ≫
      ρ.hom.app (DerivedCategory.Q.obj B) = α.app B := by
    have h := CF.rightDerivedNatTrans_app RF (roosDerivedUnit κ) α W (𝟙 _) B
    simpa [ρ, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      roosDerivedUnit, roosInclusion, roosLimitFunctor,
      Functor.rightDerivedNatTrans, Category.assoc] using h
  have hunit : DerivedCategory.Q.map (limIso.hom.app B ≫ roosι B) ≫
      κ.hom.app B ≫ ρ.hom.app (DerivedCategory.Q.obj B) = η.app B := by
    simp only [Functor.map_comp, Category.assoc, hn]
    dsimp only [α, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Iso.symm_hom]
    rw [← Category.assoc, ← Functor.map_comp, limIso.hom_inv_id_app,
      DerivedCategory.Q.map_id, Category.id_comp]
  have haug (n : ℕ) : a ≫ limIso.hom.app B ≫ limit.π B.asFunctor (op n) ≫
      e.hom.app (op n) = ((IntegralOnSlice.augmentation.{u, u} l E T none).app Q).app (op n) := by
    dsimp only [limIso]
    rw [← Category.assoc (CompletedCoefficientPushforward.limitModelIso.hom.app B),
      CompletedCoefficientPushforward.limitModel_hom_π]
    exact ha n
  have hchain : a ≫ limIso.hom.app B ≫ roosι B =
      IntegralOnSlice.roosUnit.{u, u} l E T none Q ≫ integralOperationsRoosMap e.inv := by
    let v := IntegralOnSlice.productAugmentation.{u, u} l E T none Q
    let z := Pi.lift (fun n : ℕ ↦ limit.π B.asFunctor (op n))
    let m := Limits.Pi.map (fun n : ℕ ↦ e.inv.app (op n))
    have hz : z ≫ roosU B = 0 := by
      apply Pi.hom_ext
      intro n
      simp [z, roosU, towerTransitionEndomorphism, towerProductShift,
        Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, limit.w]
    have hv : v ≫ towerTransitionEndomorphism
        (integralOperationsTowerStep ((IntegralOnSlice.tower l E T none).obj Q)) = 0 := by
      apply CochainComplex.HomComplex.Cochain.ofHom_injective
      simpa only [CochainComplex.HomComplex.δ_zero, zero_add,
        CochainComplex.HomComplex.Cochain.ofHom_zero] using
        IntegralOnSlice.roosUnit_condition.{u, u} l E T none Q
    have hprod : (a ≫ limIso.hom.app B) ≫ z = v ≫ m := by
      apply Pi.hom_ext
      intro n
      simp only [z, v, m, Category.assoc, Pi.map_π, Pi.lift_comp_π,
        Pi.lift_comp_π_assoc, IntegralOnSlice.productAugmentation]
      apply (cancel_mono (e.hom.app (op n))).1
      simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using haug n
    unfold integralOperationsRoosMap
    rw [arrowConeMap, ← Category.assoc a]
    exact completedCoconeLift_natural A _ _ m m (integralOperationsRoos_square e.inv)
      (a ≫ limIso.hom.app B) v z hv hz hprod
  let s := integralOperationsRoosFunctor.mapIso e
  let j := (ρ.app (DerivedCategory.Q.obj B)).symm ≪≫ (κ.app B).symm ≪≫
    DerivedCategory.Q.mapIso s
  refine ⟨j, ?_⟩
  rw [hηapp]
  change (DerivedCategory.Q.map a ≫ η.app B) ≫ j.hom = _
  rw [← hunit]
  simp only [j, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  erw [← Category.assoc, hchain]
  change (IntegralOnSlice.roosUnit.{u, u} l E T none Q ≫ s.inv) ≫ s.hom = _
  erw [Category.assoc, s.inv_hom_id, Category.comp_id]

attribute [-instance] IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective
  IntegralOnSlice.hasDerived integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsSiteSmall integralOperationsCommHasDerivedCategory
  CompletedCoefficientPushforward.modAbelian CompletedCoefficientPushforward.hasDerived in
attribute [local instance 3000] integralTowerHasDerivedCategory in
/-- The quotient completion, including its unit, is transported to integral Roos completion.
Source: Stacks Tags 093M (coefficient reduction) and 0941 (total inverse limit).
(blueprint: lem-sf-open-dvr-roos-completion-comparison).

Proof: choose a flat-term K-flat representative Q. The finite comparisons of C,
normalized on constant sections, identify each quotient tensor module with the
corresponding integral quotient module. The completed projection equations identify
their completed scalar actions. These comparisons commute with all quotient
transitions and take the quotient augmentation to the integral tensor augmentation.
Transpose this isomorphism to complexes of strict towers. The projection-normalized
limit comparison for the exact scalar equivalence C identifies their total inverse
limits. Exact countable products on the pro-etale site identify the latter total
limit with the signed integral Roos complex: the right-derived universal property
fixes its comparison with ordinary limit, so the augmentation goes to the recorded
zero-homotopy Roos unit. The definition of IntegralOnSlice.completionComparison
identifies this Roos complex with integral completion. Compose these isomorphisms.
On Q the unit equation follows from the same strict augmentation and the normalized
ordinary-limit projections. Naturality and essential surjectivity of localization
of flat-term K-flat complexes extend it to every P. No completeness hypothesis or
choice of a generator for d.ideal is used. Empty schemes and zero complexes use
the same limit and augmentation formulas. -/
theorem openDvrRoosCompletionComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (P : DerivedCategory (scalarReductionSource.{u, u} l E T)) :
    ∃ j : (completedAdicReduction T d ⋙ reconstructionRlim T d).obj
        (C.derived.functor.obj P) ≅
        C.derived.functor.obj ((IntegralOnSlice.completion l E T none).obj P),
      (reconstructionCompletionUnit T d).app (C.derived.functor.obj P) ≫ j.hom =
        C.derived.functor.map ((IntegralOnSlice.completionUnit l E T none).app P) := by
  classical
  let F := C.derived.functor
  let H := completedAdicReduction T d ⋙ reconstructionRlim T d
  let G := IntegralOnSlice.completion.{u, u} l E T none
  let ν := IntegralOnSlice.completionUnit.{u, u} l E T none
  obtain ⟨Q, f, hQ, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (DerivedCategory.Q.objPreimage P)
  let := hf
  let e : DerivedCategory.Q.obj Q ≅ P :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso P
  have hsite : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i) := by
    intro i
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i)).symm (hflat i)
  let Qgood : (IntegralOnSlice.Good.{u, u} l E T none).FullSubcategory :=
    ⟨Q, hQ, hsite⟩
  let S := openDvrSystem l E T
  obtain ⟨A⟩ := openDvrAugmentedTowerComparison l E d T C S
  obtain ⟨B, a, κ, b, τ, _, _, haug, hunit⟩ := A.representative Q hQ hsite
  let L : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _ := lim
  let β := ((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
    lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
      (L.mapHomologicalComplex (.up ℤ)).map a
  have hβ (i : ℤ) (n : ℕ) : β.f i ≫ limit.π (B.X i) (op n) =
      (a.f i).app (op n) := by
    dsimp only [β, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    rw [Adjunction.mapHomologicalComplex_unit_app_f]
    change (constLimAdj.unit.app (Q.X i) ≫ L.map (a.f i)) ≫ _ = _
    dsimp only [L]
    erw [Category.assoc, limMap_π, ← Category.assoc]
    simp [constLimAdj]
  have htower : (IntegralOnSlice.tower.{u, u} l E T none).obj Q =
      unrestrictedIntegralComplexTower.{u, u} l E T Q := by
    rw [integralGlobalTower]
    rfl
  let κ' := κ ≪≫ (eqToIso htower).symm
  have hlegs (n : ℕ) :
      β ≫ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app B ≫
        κ'.hom.app (op n) =
      ((IntegralOnSlice.augmentation.{u, u} l E T none).app Q).app (op n) := by
    have hn := eq_of_heq (haug n)
    rw [integralGlobalUnit]
    simp only [κ', Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.inv,
      eqToHom_app, eqToHom_refl, Category.comp_id]
    apply HomologicalComplex.hom_ext
    intro i
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      ← Category.assoc]
    erw [hβ]
    exact congrArg (fun z ↦ z.f i) hn
  obtain ⟨jB, hjB⟩ := dvrRoosRepresentativeComparison l E T Q B κ' β hlegs
  let c := (IntegralOnSlice.completionComparison.{u, u} l E T none).app Qgood
  have hc : ν.app (DerivedCategory.Q.obj Q) ≫ c.hom =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit.{u, u} l E T none Q) :=
    (IntegralOnSlice.completionUnit_existsUnique.{u, u} l E T none).exists.choose_spec Qgood
  let jQ : H.obj (F.obj (DerivedCategory.Q.obj Q)) ≅
      F.obj (G.obj (DerivedCategory.Q.obj Q)) :=
    (reconstructionRlim T d).mapIso (A.tower.app (DerivedCategory.Q.obj Q)) ≪≫
      A.rlim.app ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
        (S.reduction.obj (DerivedCategory.Q.obj Q))) ≪≫
      F.mapIso ((coefficientConstantTowerLimit.{u, u} l E T).mapIso b ≪≫ jB ≪≫ c.symm)
  have hjQ : (reconstructionCompletionUnit T d).app (F.obj (DerivedCategory.Q.obj Q)) ≫
      jQ.hom = F.map (ν.app (DerivedCategory.Q.obj Q)) := by
    simp only [jQ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
      Functor.map_comp]
    erw [reassoc_of% (A.unit (DerivedCategory.Q.obj Q)), reassoc_of% hunit]
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    erw [← Category.assoc, hjB, ← hc, Category.assoc, c.hom_inv_id, Category.comp_id]
  let j := H.mapIso (F.mapIso e.symm) ≪≫ jQ ≪≫ F.mapIso (G.mapIso e)
  refine ⟨j, ?_⟩
  change (reconstructionCompletionUnit T d).app (F.obj P) ≫
    (H.map (F.map e.inv) ≫ jQ.hom ≫ F.map (G.map e.hom)) = F.map (ν.app P)
  rw [← Category.assoc, ← Category.assoc,
    ← (reconstructionCompletionUnit T d).naturality (F.map e.inv)]
  simp only [Functor.id_map, Category.assoc]
  erw [reassoc_of% hjQ]
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  have hn := ν.naturality e.inv
  dsimp only [Functor.id_map] at hn
  erw [reassoc_of% hn]
  simp

end WeilConjectures

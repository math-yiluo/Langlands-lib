/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
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
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
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

/-! # The augmented quotient tower under the canonical DVR coefficient comparison

Source: Stacks Tags 0941, 099B and 0A0E; canonical coefficient transport.
(blueprint: lem-sf-open-dvr-limit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Canonical projection-normalized ordinary and derived limit transport.
Source: Stacks Tags 05RR and 0941
(blueprint: lem-sf-open-dvr-limit-comparison). -/
structure OpenDvrLimitComparison
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) where
  /-- The total-limit comparison is the canonical one under the coefficient equivalence. -/
  rlim : C.towers ⋙ reconstructionRlim T d ≅
    coefficientConstantTowerLimit.{u, u} l E T ⋙ C.derived.functor
  /-- The total-limit comparison extends the ordinary projection-normalized comparison. -/
  limit_model : ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
    ∃ σ : ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).obj
          (C.towerComplexes.obj I) ≅
        C.complexes.obj
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I),
      (∀ (i : ℤ) (n : ℕ),
        σ.hom.f i ≫ C.modules.functor.map (limit.π (I.X i) (op n)) =
          limit.π ((C.towerComplexes.obj I).X i) (op n)) ∧
      C.derived.functor.map
          (derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit I) =
        C.modules.functor.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map σ.inv ≫
          reconstructionRlimComparison T d (C.towerComplexes.obj I) ≫
          (reconstructionRlim T d).map
            (C.ordinaryTowers.mapDerivedCategoryFactors.inv.app I) ≫
          rlim.hom.app (DerivedCategory.Q.obj I)

private theorem dvrRlimComparison_exists
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T) :
    ∃ e : C.towers ⋙ reconstructionRlim T d ≅
        coefficientConstantTowerLimit.{u, u} l E T ⋙ C.derived.functor,
      ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
        C.derived.functor.map
          (derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit I) ≫
          e.inv.app (DerivedCategory.Q.obj I) ≫
          (reconstructionRlim T d).map
            (C.ordinaryTowers.mapDerivedCategoryFactors.hom.app I) =
        C.modules.functor.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
              (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (preservesLimitNatIso C.modules.functor) (.up ℤ)).hom.app I) ≫
          reconstructionRlimComparison T d (C.towerComplexes.obj I) := by
  let E' := C.modules.congrRight (E := ℕᵒᵖ)
  have : E'.functor.Additive := by
    change C.ordinaryTowers.Additive
    infer_instance
  let L : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _ := lim
  let L' : CompletedAdicTowers T d ⥤ _ := reconstructionLimit T d
  let η : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  let η' : L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L'.rightDerivedFunctor :=
    { app := L'.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ L'.rightDerivedFunctorUnitQ_naturality f }
  have hL := CategoryTheory.derives L
  have : L.rightDerivedFunctor.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply hL.isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (L.rightDerivedFunctorUnitQ I.obj)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hL' := CategoryTheory.derives L'
  have : L'.rightDerivedFunctor.IsRightDerivedFunctor η'
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply hL'.isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (L'.rightDerivedFunctorUnitQ I.obj)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension L.rightDerivedFunctor η
    (HomologicalComplex.quasiIso _ (.up ℤ))
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension L'.rightDerivedFunctor η'
    (HomologicalComplex.quasiIso _ (.up ℤ))
  obtain ⟨φ, hφ⟩ := CategoryTheory.rightDerivedSquare E' C.modules L L'
    L.rightDerivedFunctor L'.rightDerivedFunctor η η'
    (preservesLimitNatIso C.modules.functor)
  refine ⟨φ.symm, ?_⟩
  intro I
  simpa [η, η', E', L, L', coefficientConstantTowerLimit, reconstructionRlim,
    CategoryTheory.Equivalence.congrRight,
    OpenDvrCoefficientModel.towers, OpenDvrCoefficientModel.ordinaryTowers,
    OpenDvrCoefficientModel.towerComplexes, OpenDvrCoefficientModel.derived,
    Functor.rightDerivedFunctorUnitQ,
    derivedLimitComplexComparison, reconstructionRlimComparison,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
    using hφ I

private theorem dvrRlimModel_exists
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T) :
    ∃ rlim : C.towers ⋙ reconstructionRlim T d ≅
        coefficientConstantTowerLimit.{u, u} l E T ⋙ C.derived.functor,
      ∀ I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
    ∃ σ : ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).obj
          (C.towerComplexes.obj I) ≅
        C.complexes.obj
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I),
      (∀ (i : ℤ) (n : ℕ),
        σ.hom.f i ≫ C.modules.functor.map (limit.π (I.X i) (op n)) =
          limit.π ((C.towerComplexes.obj I).X i) (op n)) ∧
      C.derived.functor.map
          (derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit I) =
        C.modules.functor.mapDerivedCategoryFactors.hom.app
            (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map σ.inv ≫
          reconstructionRlimComparison T d (C.towerComplexes.obj I) ≫
          (reconstructionRlim T d).map
            (C.ordinaryTowers.mapDerivedCategoryFactors.inv.app I) ≫
          rlim.hom.app (DerivedCategory.Q.obj I) := by
  obtain ⟨e, he⟩ := dvrRlimComparison_exists l E d T C
  refine ⟨e, ?_⟩
  intro I
  let s := preservesLimitNatIso C.modules.functor (J := ℕᵒᵖ)
  let σ : ((reconstructionLimit T d).mapHomologicalComplex (.up ℤ)).obj
      (C.towerComplexes.obj I) ≅ C.complexes.obj
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
          (.up ℤ)).obj I) :=
    (NatIso.mapHomologicalComplex s (.up ℤ)).symm.app I
  refine ⟨σ, ?_, ?_⟩
  · intro i n
    change (preservesLimitIso C.modules.functor (I.X i)).inv ≫
      C.modules.functor.map (limit.π (I.X i) (op n)) = _
    exact preservesLimitIso_inv_π C.modules.functor (I.X i) (op n)
  · have hσ : σ.inv = (NatIso.mapHomologicalComplex s (.up ℤ)).hom.app I := rfl
    rw [hσ]
    let z := (reconstructionRlim T d).mapIso (C.ordinaryTowers.mapDerivedCategoryFactors.app I)
    let w := e.symm.app (DerivedCategory.Q.obj I) ≪≫ z
    have h := (he I)
    have h' : _ = _ := (Iso.eq_comp_inv w).2 (by
      change (_ ≫ e.inv.app _ ≫ z.hom) = _
      exact h)
    simpa only [w, z, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Iso.app_inv, Iso.app_hom, Category.assoc] using h'

/-- Scalar restriction along the canonical coefficient isomorphism transports limits.
Source: Stacks Tags 05RR and 0941
(blueprint: lem-sf-open-dvr-limit-comparison).

Proof: scalar restriction is an exact equivalence. Its ordinary limit comparison is
preservesLimitNatIso, hence is fixed by all projections. Apply rightDerivedSquare to
the coefficient equivalence and its pointwise tower equivalence, with the universal
right-derived pairs. Its factorization equation is the required equation on complexes.
The localization comparison through the homotopy category is the recorded
reconstructionRlimComparison. Compose the factorization equation with the inverse
tower-localization isomorphism and the derived comparison to obtain limit_model. -/
theorem openDvrLimitComparison
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T) :
    Nonempty (OpenDvrLimitComparison l E C) := by
  obtain ⟨e, he⟩ := dvrRlimModel_exists l E d T C
  exact ⟨⟨e, he⟩⟩

end WeilConjectures

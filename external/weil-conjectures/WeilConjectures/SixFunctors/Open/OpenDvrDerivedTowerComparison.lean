/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import all WeilConjectures.CategoryTheory.Constant.ConstantTowerNormalization

/-! # The natural derived DVR tower comparison on resolutions

Source: Stacks Tag 06XN, comparison using a resolving class.
(blueprint: lem-sf-open-dvr-derived-tower-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] HasDerivedCategory.standard Functor.rightDerivedFunctor

local instance (priority := 10000) towerComparisonSequenceSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × T.ProEt) :=
  coefficientSequenceEssentiallySmall.{u, 0} T

private def reductionComplexCounitNat
    {B D : Type*} [Category B] [Abelian B] [Category D] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    {F : B ⥤ D} [F.Additive] {P : CochainComplex B ℤ → Prop}
    (R : DerivedReductionModelData F P) :
    DerivedCategory.Q ⋙ R.reduction ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso B).inv R.reduction ≫
    Functor.whiskerLeft (HomotopyCategory.quotient B (.up ℤ)) R.counit ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).hom

private theorem goodResolutions (T : Scheme.{u})
    (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ) :
    ∃ (P : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ) (s : P ⟶ Q),
      (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology T)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) P ∧
        ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := ProEt.topology T)
          (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (P.X i)) ∧
      QuasiIso s := by
  obtain ⟨P, s, hP, hflat, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q
  refine ⟨P, s, ⟨hP, ?_⟩, hs⟩
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (P.X i)).symm (hflat i)

private theorem coefficientKFlatTransport
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology T)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q) :
    CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d)
      (C.complexes.obj Q) := by
  obtain ⟨Riso⟩ := SheafOfModules.ringIso_tensor_transport C.completed
  have h := (Riso.kflat_iff Q).mpr hQ
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
    (R := completedAdicCommRing T d) (C.complexes.obj Q)).mp
  simpa only [OpenDvrCoefficientModel.complexes, C.modules_functor] using h

/-- Ordinary tensor transport and a flat-resolution comparison give a natural derived tower iso.
Source: Stacks Tag 06XN (comparison on resolutions)
(blueprint: lem-sf-open-dvr-derived-tower-comparison).

Proof: compare the completed-adic reduction counit with epsilon after exact scalar
restriction and coefficient transport, followed by the inverse ordinary tensor
comparison. Both target the same localized ordinary tensor tower. The first is an
isomorphism on K-flat complexes by Koszul reconstruction and preservation of
K-flatness under the coefficient ring isomorphism. The second is an isomorphism
there by the hypothesis on epsilon. Flat-term K-flat complexes resolve every
complex. Apply comparison_from_resolutions to get t. Its representative equality,
after cancellation of the localized inverse ordinary comparison, is precisely the
displayed counit square. This argument uses no adjunction-unit normalization and
constructs neither an augmentation nor a total-limit map. -/
theorem openDvrDerivedTowerComparison
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E T)
    (M : CompletionUnit.OrdinaryModel l E T)
    (ν : C.modules.functor ⋙ completedAdicOrdinaryTower T d ≅
      M.tensor ⋙ coefficientSequenceRestriction.{u, u} l E T ⋙ C.ordinaryTowers)
    (ε : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E T ⋙ DerivedCategory.Q)
    (hε : ∀ Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology T)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology T)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i)) →
      IsIso (ε.app Q)) :
    ∃ t : C.derived.functor ⋙ completedAdicReduction T d ≅
        S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T ⋙ C.towers,
      ∀ (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
        (_hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology T)
          (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q)
        (_hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := ProEt.topology T)
          (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i)),
      let I := (M.quotient l E T).obj Q
      let B := (CompletionUnit.tower l E T).obj I
      (completedAdicReduction T d).map
          (C.modules.functor.mapDerivedCategoryFactors.hom.app Q) ≫
        reconstructionReductionComplexCounit T d (C.complexes.obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app Q) =
      t.hom.app (DerivedCategory.Q.obj Q) ≫
        C.towers.map ((coefficientSequenceDerivedRestriction.{u, u} l E T).map
          (ε.app Q) ≫
            (Functor.mapDerivedCategoryFactors
              (coefficientSequenceRestriction.{u, u} l E T)).hom.app I) ≫
        C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B := by
  classical
  let := coefficientSequenceHasDerived.{u, u} l E T
  let := coefficientConstantTowerDerived.{u, u} l E T
  let U := coefficientSequenceRestriction.{u, u} l E T
  let : U.Additive := coefficientSequenceRestriction_additive.{u, u} l E T
  let : PreservesFiniteLimits U := coefficientSequenceRestriction_limits.{u, u} l E T
  let : PreservesFiniteColimits U := coefficientSequenceRestriction_colimits.{u, u} l E T
  let χ : (DerivedCategory.Q (C := coefficientSequenceModules.{u, u} l E T)) ⋙
      coefficientSequenceDerivedRestriction.{u, u} l E T ≅
        CompletionUnit.tower.{u, u} l E T ⋙ DerivedCategory.Q :=
    U.mapDerivedCategoryFactors
  let β : (DerivedCategory.Q (C := ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T)) ⋙
      C.towers ≅ C.towerComplexes ⋙ DerivedCategory.Q :=
    C.ordinaryTowers.mapDerivedCategoryFactors
  let νc := NatIso.mapHomologicalComplex ν (.up ℤ)
  let H := C.complexes ⋙ (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q
  let η : DerivedCategory.Q ⋙ (C.derived.functor ⋙ completedAdicReduction T d) ⟶ H :=
    Functor.whiskerRight C.modules.functor.mapDerivedCategoryFactors.hom
        (completedAdicReduction T d) ≫
      Functor.whiskerLeft C.complexes
        (reductionComplexCounitNat (completedAdicReductionData T d))
  let θ : DerivedCategory.Q ⋙
      (S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T ⋙ C.towers) ⟶ H :=
    Functor.whiskerRight ε (coefficientSequenceDerivedRestriction.{u, u} l E T ⋙ C.towers) ≫
      Functor.whiskerLeft (M.quotient l E T)
        (Functor.whiskerRight χ.hom C.towers) ≫
      Functor.whiskerLeft ((M.quotient l E T) ⋙ U.mapHomologicalComplex (.up ℤ))
        β.hom ≫
      Functor.whiskerRight νc.inv DerivedCategory.Q
  obtain ⟨t, ht, _⟩ := comparison_from_resolutions
    (fun Q ↦ CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology T)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology T)
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) (Q.X i))
    (goodResolutions l E T) _ _ H η θ
    (fun Q hQ ↦ by
      have := reconstructionTowerCounit_isIso T d (C.complexes.obj Q)
        (coefficientKFlatTransport l E d T C Q hQ.1)
      change IsIso ((completedAdicReduction T d).map
        (C.modules.functor.mapDerivedCategoryFactors.hom.app Q) ≫
          reconstructionReductionComplexCounit T d (C.complexes.obj Q))
      infer_instance)
    (fun Q hQ ↦ by
      have := hε Q hQ.1 hQ.2
      dsimp only [θ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      infer_instance)
  refine ⟨t, ?_⟩
  intro Q hQ hflat
  let I := (M.quotient l E T).obj Q
  let B := (CompletionUnit.tower l E T).obj I
  let e := U.mapDerivedCategory.map (ε.app Q) ≫ U.mapDerivedCategoryFactors.hom.app I
  let τ := νc.app Q
  have h := ht Q ⟨hQ, hflat⟩
  rw [← Category.assoc]
  change η.app Q ≫ DerivedCategory.Q.map τ.hom =
    t.hom.app (DerivedCategory.Q.obj Q) ≫ C.towers.map e ≫
      C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B
  apply (cancel_mono (DerivedCategory.Q.map τ.inv)).mp
  have hcancel : DerivedCategory.Q.map τ.hom ≫ DerivedCategory.Q.map τ.inv = 𝟙 _ :=
    (DerivedCategory.Q.mapIso τ).hom_inv_id
  simp only [Category.assoc]
  rw [hcancel]
  change η.app Q ≫ 𝟙 (H.obj Q) = _
  calc
    _ = η.app Q := Category.comp_id (η.app Q)
    _ = t.hom.app (DerivedCategory.Q.obj Q) ≫ θ.app Q := h.symm
    _ = _ := by
      have hθ : θ.app Q = C.towers.map e ≫
          C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B ≫
            DerivedCategory.Q.map τ.inv := by
        change C.towers.map (U.mapDerivedCategory.map (ε.app Q)) ≫
            C.towers.map (U.mapDerivedCategoryFactors.hom.app I) ≫
            C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B ≫
            DerivedCategory.Q.map τ.inv =
          C.towers.map (U.mapDerivedCategory.map (ε.app Q) ≫
            U.mapDerivedCategoryFactors.hom.app I) ≫
            C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B ≫
            DerivedCategory.Q.map τ.inv
        rw [Functor.map_comp, Category.assoc]
      rw [hθ]

end WeilConjectures

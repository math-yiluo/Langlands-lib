/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralCoherenceData
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
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
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
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
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
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Acyclic
/-! # Flat-term K-flat presentations of coefficient quotient systems

Evaluation detects exactness on the sequence site. This lifts K-flatness and flatness
from the scalar extensions at every finite level to the prescribed strict presentation.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (V : AlgebraicGeometry.Scheme.{t})

attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local instance 2000] SheafOfModules.cochainModulesSymmetric
attribute [local irreducible] SheafOfModules.monoidalCategory

private instance sequencePreadditive :
    MonoidalPreadditive (coefficientSequenceModules l E V) :=
  SheafOfModules.cochainModulesPreadditive (coefficientSequenceCommRingSheaf l E V)

private instance sequenceTensorLeftColim (M : coefficientSequenceModules l E V) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits (coefficientSequenceCommRingSheaf l E V) M

private instance sequenceTensor
    (X Y : GradedObject ℤ (coefficientSequenceModules l E V)) : X.HasTensor Y := inferInstance

private def levelsAb : coefficientSequenceModules l E V ⥤
    Discrete ℕ ⥤ Sheaf (AlgebraicGeometry.Scheme.ProEt.topology V)
      AddCommGrpCat.{max u (t + 1)} where
  obj M := Discrete.functor (fun n ↦ (SheafOfModules.toSheaf _).obj
    ((coefficientSequenceEvaluation l E V n).obj M))
  map f := Discrete.natTrans (fun n ↦ (SheafOfModules.toSheaf _).map
    ((coefficientSequenceEvaluation l E V n.as).map f))
  map_id M := by ext n U x; rfl
  map_comp f g := by ext n U x; rfl

private instance : (levelsAb l E V).Faithful where
  map_injective := by
    intro M N f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    have hh := congrArg (fun a ↦ (a.app ⟨U.unop.1⟩).hom.app (op U.unop.2)) h
    ext x
    exact congrArg (fun a ↦ a.hom x) hh

private instance : (levelsAb l E V).Additive where
  map_add := by intro M N f g; ext n U x; rfl

private instance : PreservesFiniteLimits (levelsAb l E V) := by
  apply preservesFiniteLimits_of_evaluation
  intro n
  change PreservesFiniteLimits (coefficientSequenceEvaluation l E V n.as ⋙
    SheafOfModules.toSheaf _)
  infer_instance

private instance : PreservesFiniteColimits (levelsAb l E V) := by
  apply preservesFiniteColimits_of_evaluation
  intro n
  change PreservesFiniteColimits (coefficientSequenceEvaluation l E V n.as ⋙
    SheafOfModules.toSheaf _)
  infer_instance

private theorem acyclic_of_levels
    (P : CochainComplex (coefficientSequenceModules l E V) ℤ)
    (hP : ∀ n, (((coefficientSequenceEvaluation l E V n).mapHomologicalComplex
      (.up ℤ)).obj P).Acyclic) : P.Acyclic := by
  intro k
  apply (P.sc k).exact_map_iff_of_faithful (levelsAb l E V) |>.mp
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).2
  apply NatTrans.ext
  funext n
  let F := (evaluation (Discrete ℕ)
    (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology V) AddCommGrpCat.{max u (t + 1)})).obj n
  have hh : ((P.sc k).map (levelsAb l E V) |>.map F).Exact := by
    exact (hP n.as k).map (SheafOfModules.toSheaf _)
  have hz : IsZero (F.obj ((P.sc k).map (levelsAb l E V)).homology) :=
    IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp hh)
      (((P.sc k).map (levelsAb l E V)).mapHomologyIso F).symm
  exact hz.eq_of_src _ _

private theorem kflat_of_levels
    (P : CochainComplex (coefficientSequenceModules l E V) ℤ)
    (hP : ∀ n, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E V n)
      (((coefficientSequenceEvaluation l E V n).mapHomologicalComplex (.up ℤ)).obj P)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E V) P := by
  intro Z hZ
  apply acyclic_of_levels l E V
  intro n
  have hZn : (((coefficientSequenceEvaluation l E V n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := by
    intro k
    exact (hZ k).map (coefficientSequenceEvaluation l E V n)
  have hh := hP n _ hZn
  intro k
  exact (hh k).of_iso (coefficientEvaluationTensorIso l E V n Z P).symm

private theorem flat_extension (n : ℕ)
    (M : scalarReductionSource l E V)
    (hM : SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology V)
      (R := completedIntegralCommRingSheafUnrestricted.{t, u} l E V) M) :
    SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology V)
      (R := integralCoefficientCommRingSheaf.{t, u} l E V n)
      ((scalarReductionExtension l E V n).obj M) := by
  have hobj := (scalarReductionExistence l E V n).choose_spec.choose M
  apply SheafOfModules.flatOnSite_of_iso
    (integralCoefficientCommRingSheaf.{t, u} l E V n)
    (eqToIso hobj).symm
  exact SheafOfModules.isFlat_changeOfRingsOfUniverses.{t + 1, t, max u (t + 1), max u (t + 1)}
    (completedIntegralCommRingProjectionUnrestricted l E V n) M hM

private theorem native_kflat
    (P : CochainComplex (coefficientSequenceModules l E V) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E V) P) :
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E V) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor Z P (MonoidalCategory.curriedTensor _))).2 (hP Z hZ)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
    ((HomotopyCategory.quotient (coefficientSequenceModules l E V) (.up ℤ)).mapIso
      (CochainComplex.Monoidal.braiding Z P)) hr, hr⟩

private theorem flat_of_single
    (M : coefficientSequenceModules l E V)
    (hM : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E V)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) :
    SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (AlgebraicGeometry.Scheme.ProEt.topology V))
      (R := coefficientSequenceCommRingSheaf l E V) M := by
  have hf := (CochainComplex.kFlat_single_obj_iff_flat M 0).mp
    (native_kflat l E V _ hM)
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (coefficientSequenceCommRingSheaf l E V) M).symm
    hf.2

private noncomputable instance finiteMonoidal (n : ℕ) :
    MonoidalCategory (normalizedDVRModules l E V n) :=
  SheafOfModules.cochainModulesMonoidal (integralCoefficientCommRingSheaf l E V n)

private noncomputable instance finiteSymmetric (n : ℕ) :
    SymmetricCategory (normalizedDVRModules l E V n) :=
  SheafOfModules.cochainModulesSymmetric (integralCoefficientCommRingSheaf l E V n)

private instance finitePreadditive (n : ℕ) :
    MonoidalPreadditive (normalizedDVRModules l E V n) :=
  SheafOfModules.cochainModulesPreadditive (integralCoefficientCommRingSheaf l E V n)

private instance finiteTensorLeftColim (n : ℕ) (M : normalizedDVRModules l E V n) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits
    (integralCoefficientCommRingSheaf l E V n) M

private noncomputable instance finiteColimits (n : ℕ) :
    HasColimitsOfSize.{0, 0} (normalizedDVRModules l E V n) := by
  with_unfolding_all infer_instance

private instance finiteTensorR (n : ℕ) (X Y : GradedObject ℤ (normalizedDVRModules l E V n)) :
    X.HasTensor Y := inferInstance
private instance finiteTensorFour (n : ℕ)
    (X Y Z U : GradedObject ℤ (normalizedDVRModules l E V n)) :
    GradedObject.HasTensor₄ObjExt X Y Z U := inferInstance
private instance finiteTensorLeft (n : ℕ)
    (X Y Z : GradedObject ℤ (normalizedDVRModules l E V n)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private instance finiteTensorRight (n : ℕ)
    (X Y Z : GradedObject ℤ (normalizedDVRModules l E V n)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance

private theorem finite_independent_of_native (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E V n) ℤ)
    (hP : (HomologicalComplex.quasiIso (normalizedDVRModules l E V n) (.up ℤ)).kFlat P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E V n) P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hP
  intro Z hZ
  have hz := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).2 hZ
  have h := (hP _ hz).2
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 h

private theorem flat_of_levels
    (M : coefficientSequenceModules l E V)
    (hM : ∀ n, SheafOfModules.IsFlatOnSite
      (J := AlgebraicGeometry.Scheme.ProEt.topology V)
      (R := integralCoefficientCommRingSheaf l E V n)
      ((coefficientSequenceEvaluation l E V n).obj M)) :
    SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (AlgebraicGeometry.Scheme.ProEt.topology V))
      (R := coefficientSequenceCommRingSheaf l E V) M := by
  apply flat_of_single l E V
  apply kflat_of_levels l E V
  intro n
  let F := coefficientSequenceEvaluation l E V n
  let P := (HomologicalComplex.single _ (.up ℤ) 0).obj (F.obj M)
  have hf : ObjectProperty.flat (F.obj M) := by
    have h := hM n
    have hr := (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (integralCoefficientCommRingSheaf l E V n) _) h
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (F.obj M)).symm hr, hr⟩
  have hp := finite_independent_of_native l E V n P
    ((CochainComplex.kFlat_single_obj_iff_flat (F.obj M) 0).2 hf)
  have e := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M
  intro Z hZ
  have h := hp Z hZ
  intro k
  exact (h k).of_iso
    ((coefficientTotalTensor.{u, t + 1, t} (AlgebraicGeometry.Scheme.ProEt.topology V)
      (integralCoefficientCommRingSheaf l E V n)).mapIso
        (Iso.prod (Iso.refl Z) e)).symm

end WeilConjectures
namespace WeilConjectures.IntegralCoherence
universe s
variable {S : Type s} {W : S → AlgebraicGeometry.Scheme.{t}}
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
end WeilConjectures.IntegralCoherence

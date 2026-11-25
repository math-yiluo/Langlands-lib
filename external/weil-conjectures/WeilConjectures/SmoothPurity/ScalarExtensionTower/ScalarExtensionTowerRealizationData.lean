/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Data for scalar-extension realization equations

The existing tensor realization, reduction maps and normalized derived comparison
are separated from the coherence theorem so its two word comparisons can be proved
independently. Their definitions and statements are unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.coefficientTotalTensor
  SheafOfModules.monoidalCategory
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.integralComparisonSequenceScalarModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] scalar_adj comparisons
  integralComparisonSequenceTensorSection integralComparisonSequenceScalarUnit

/-- A generator read in the legacy restricted finite-tensor tower's exact section type.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def integralTensorGenerator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules.{u, u} l E W) ℤ)
    (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q).X r).val.obj U) :
    ((((integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P, Q)).obj
      (op n)).X (p + r)).val.obj U :=
  integralOperationsTotalTensorSection.{u, u} l E W n P Q p r U x y

/-- Representative normalization of the completed tensor realization, including its
local tensor formula and its specified Roos comparison. Both input presentations
must fix the derived comparison in the whole tower through its adjunction transpose;
finite derived evaluations alone do not determine that comparison.
Source: Stacks 06YS, 07A4, 0941 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def IsTensorModelNormalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W)
    (realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (C D : Complex l E W)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P.obj)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q.obj)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) D),
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C eC κC →
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      Q.obj Q.property.1 D eD κD →
    IsIntegralComparisonPresentationCoherent l E W S P.obj C eC κC →
    IsIntegralComparisonPresentationCoherent l E W S Q.obj D eD κD →
    ∃ q : (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P.obj, Q.obj),
      (∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
        (x : (C.X p).val.obj (op (n, U.unop)))
        (y : (D.X r).val.obj (op (n, U.unop))),
        ((q.hom.app (op n)).f (p + r)).val.app U
          (integralComparisonRestrictedSection.{u, u} l E W
            (((tensor l E W).obj (C, D)).X (p + r)) n U
            (generator l E W C D p r (op (n, U.unop)) x y)) =
          integralTensorGenerator l E W P.obj Q.obj n p r U
            (((κC n).hom.f p).val.app U (coefficientEvaluationSection.{u, u} l E W (C.X p) n U x))
            (((κD n).hom.f r).val.app U
              (coefficientEvaluationSection.{u, u} l E W (D.X r) n U y))) ∧
      FiveStepEquation
        (realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
        ((coefficientSequenceLimit.{u, u} l E W).map
          (S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom)))
        ((coefficientSequenceLimit.{u, u} l E W).map
          ((S.systemTensorModel.iso _ _ _ C D hC hD).inv))
        ((integralComparisonRoosBridge.{u, u} l E W ρ
          ((tensor l E W).obj (C, D))).hom)
        (DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom))
        ((integralCompletedTensorComparison.{u, u} l E W).hom.app (P, Q))

attribute [local irreducible] IsTensorModelNormalized

/-- A normalized presentation of the named completed tensor by whole quotient systems.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4 and 0941
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
structure TensorModel (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) where
  /-- The named completed tensor, realized by the specified system closed tensor. -/
  realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
    S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W
  /-- Normalization at every whole-system coherent good quotient presentation. -/
  normalization : IsTensorModelNormalized l E W S ρ realization

/-- The actual reduction of a completed pullback, followed by the coherent counit.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def pullbackReduction (W : Bool → Scheme.{u}) (M : CompletedOperations.Models.{u, u} l E W)
    (f : W true ⟶ W false) (K : DerivedCategory (scalarReductionSource.{u, u} l E (W false))) :
    (M.calculus true).reduction.obj ((integralDerivedPullback.{u, u} l E f).obj K) ⟶
      (integralComparisonDerivedSequencePullback.{u, u} l E f).obj
        ((M.calculus false).reduction.obj K) :=
  (M.calculus true).reduction.map ((M.pullback f).realization.hom.app K) ≫
    (M.calculus true).adjunction.counit.app _

/-- The actual coherent scalar-reduction comparison, obtained from its normalized
realization and the coherent counit, with no arbitrary quotient identification.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def scalarReduction (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L W)
    (M : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    SL.reduction.obj ((integralScalarExtension.{u} l E L ι W).obj K) ⟶
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).obj (SE.reduction.obj K) :=
  SL.reduction.map (M.realization.hom.app K) ≫ SL.adjunction.counit.app _

/-- The completed tensor's actual quotient comparison, followed by the coherent counit.
Source: node proof step 8 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def tensorReduction (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) (M : TensorModel l E W S ρ)
    (K N : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    S.reduction.obj ((integralCompletedTensor.{u, u} l E W).obj (K, N)) ⟶
      S.systemClosed.tensor.obj (S.reduction.obj K, S.reduction.obj N) :=
  S.reduction.map (M.realization.hom.app (K, N)) ≫ S.adjunction.counit.app _

/-- The flat-term K-flat class used for scalar/tensor descent on the sequence site.
Source: Stacks 06YS, 0G7E (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def Good (W : Scheme.{u}) (P : Complex l E W) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (R := coefficientSequenceCommRingSheaf.{u, u} l E W) P ∧
  ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := coefficientSequenceCommRingSheaf.{u, u} l E W) (P.X n)

/-- Cochain normalization of the system derived scalar/tensor comparison.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence). -/
def DerivedSigmaModel (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor) :
    Prop :=
  ∀ (P Q : Complex l E W) (hP : Good l E W P) (hQ : Good l E W Q),
    ∃ (hsP : Good l L W ((scalar l E L ι W).obj P))
      (hsQ : Good l L W ((scalar l E L ι W).obj Q)),
    (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
        ((SE.systemTensorModel.iso _ _ _ P Q hP.1 hQ.1).hom) ≫
      α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      SL.systemClosed.tensor.map (Prod.mkHom
        ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app P)
        ((integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app Q)) =
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε.app
        ((tensor l E W).obj (P, Q)) ≫
      DerivedCategory.Q.map (((comparisons l).sigma E L ι W).hom.app (P, Q)) ≫
      (SL.systemTensorModel.iso _ _ _ _ _ hsP.1 hsQ.1).hom

attribute [local irreducible] DerivedSigmaModel

private theorem scalar_good (W : Scheme.{u}) (P : Complex l E W) (hP : Good l E W P) :
    Good l L W ((scalar l E L ι W).obj P) := by
  unfold Good at hP ⊢
  have h := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (integralComparisonSequenceScalarMap.{u, u} l E L ι W) P
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).E
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).obj_eq
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).map_eq hP.1
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSheaf.{u, u} l E W) (P.X n)) (hP.2 n))
  refine ⟨h.1, fun n ↦ ?_⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
      (coefficientSequenceCommRingSheaf.{u, u} l L W)
      (((scalar l E L ι W).obj P).X n)).symm (h.2 n)

-- Compare the restricted tensor models and counits simultaneously.

/-- The derived comparison is determined by the same strict sigma on good representatives.
Source: node proof steps 1, 4, 8; Stacks 06YS, 07A4
(blueprint: lem-pur-scalar-extension-tower-coherence).
Proof: flat-term K-flat change of rings works without flatness of the ring map.
It preserves Good and computes scalar derived extension by its universal counit.
Localize sigma on the two resolving subcategories, inserting the normalized tensor
models and scalar counits. Simultaneous K-flat resolutions give naturality on roofs
and independence of resolutions. The localization universal property gives uniqueness
with this cochain model equation. -/
theorem derivedSigma_existsUnique (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W) :
    ∃! α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor,
      DerivedSigmaModel l E L ι W SE SL α := by
  unfold DerivedSigmaModel
  let A := coefficientSequenceModules.{u, u} l E W
  let B := coefficientSequenceModules.{u, u} l L W
  let P : ObjectProperty (CochainComplex A ℤ) := Good l E W
  let S : ObjectProperty (CochainComplex B ℤ) := Good l L W
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ P X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨K, f, hK, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf.{u, u} l E W) X.as
    have hs : ∀ n, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (R := coefficientSequenceCommRingSheaf.{u, u} l E W) (K.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSheaf.{u, u} l E W) (K.X n)).symm (hflat n)
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj K, hK, hs⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh P H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A))
      (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A))))
  let PE : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W)
  let PL : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l L W)
  let iE : P.FullSubcategory ⥤ PE.FullSubcategory :=
    ObjectProperty.lift _ P.ι (fun X ↦ X.property.1)
  let iL : S.FullSubcategory ⥤ PL.FullSubcategory :=
    ObjectProperty.lift _ S.ι (fun X ↦ X.property.1)
  let r := Functor.isoWhiskerLeft (iE.prod iE) SE.systemTensorModel.comparison
  let r' := Functor.isoWhiskerLeft (iL.prod iL) SL.systemTensorModel.comparison
  obtain ⟨α, hα, huniq⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q (scalar l E L ι W)
    (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W)
    (integralComparisonSequenceScalarModel.{u, u} l E L ι W).ε P S
    (fun X hX ↦ scalar_good l E L ι W X hX) ff' (tensor l E W) (tensor l L W)
    SE.systemClosed.tensor SL.systemClosed.tensor r r'
    ((comparisons l).sigma E L ι W)
    (fun X hX ↦ (integralComparisonSequenceScalarModel.{u, u} l E L ι W).computes X hX.1)
    (fun X Y hX hY ↦ (integralComparisonSequenceScalarModel.{u, u} l E L ι W).computes _
      (coefficientTotalTensor_isKFlat.{u, u + 1, u} _ _ X Y hX.1 hY.1))
  refine ⟨α, ?_, ?_⟩
  · intro X Y hX hY
    exact ⟨scalar_good l E L ι W X hX, scalar_good l E L ι W Y hY, hα X Y hX hY⟩
  · intro β hβ
    apply huniq β
    intro X Y hX hY
    obtain ⟨hX', hY', h⟩ := hβ X Y hX hY
    exact h

/-- The representative-normalized derived tensor scalar comparison on coherent systems.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-extension-tower-coherence). -/
def derivedSigma (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W) :=
  (derivedSigma_existsUnique l E L ι W SE SL).exists.choose

attribute [local irreducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralCompletedTensor integralDerivedPullback
  integralComparisonDerivedSequenceScalar integralComparisonDerivedSequencePullback
  pullbackReduction scalarReduction tensorReduction derivedSigma

end WeilConjectures.ScalarExtensionTower

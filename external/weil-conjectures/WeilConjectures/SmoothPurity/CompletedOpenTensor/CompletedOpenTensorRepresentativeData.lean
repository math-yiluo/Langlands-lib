/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # Data for compatible representatives of strict open tensors

All 21 definitions below retain their original signatures and bodies.
(blueprint: def-pur-completed-open-tensor-representative-data).

Source: Stacks Project, sites-cohomology.tex Tag 0GL1 and sites-modules.tex Tag 0E8I;
strict-system and completion-unit refinement, original realization proof steps 1--3
(blueprint: lem-pur-completed-open-tensor-system-realization).

The index n means positive exponent n+1. Site and coefficient universes are independent.
All tensors below are the published total-complex derived tensors. In particular the
system tensor is formed on the ringed sequence site, before finite evaluation or total limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOpenTensor
open IntegralOpenReduction

attribute [local irreducible] IntegralOnSlice.duality SheafOfModules.monoidalCategory
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U V : Scheme.{t}} (j : U ⟶ V) [IsOpenImmersion j]

/-- Compatible presentations of the already specified open operations, reduction and
completion. The all-input comparison is essential: ordinary tensor need not be complete.
The two completion comparisons are fixed by their actual units, and restriction/completion
by its unit square. No arbitrary comparison of completed objects is supplied.
Source: Tags 0GL1, 0E8I, 0941, 099B; node proof steps 1--5
(blueprint: lem-pur-completed-open-tensor-system-realization). -/
structure Context where
  ambient : CoefficientDerivedSystemCalculus l E V
  openSite : CoefficientDerivedSystemCalculus l E U
  ambientCoherence : CoefficientDerivedSystemCoherence l E V ambient
  openCoherence : CoefficientDerivedSystemCoherence l E U openSite
  operations : Operations l E j
  coefficients : TensorComparison l E j operations
  completeOpen : Comparison l E j operations ambient openSite coefficients
  ordinaryV : OpenSemilinearTensor.OrdinaryReduction l E V
  ordinaryU : OpenSemilinearTensor.OrdinaryReduction l E U
  strictOpen : OpenSemilinearTensor.Comparison l E j operations ambient openSite
    ordinaryV ordinaryU coefficients
  sameOpen : ∀ K : (complete l E U).FullSubcategory,
    strictOpen.r.hom.app K.obj = completeOpen.r.hom.app K
  tensorV : (IntegralOnSlice.duality l E V none).closed = ambient.integralClosed
  tensorU : (IntegralOnSlice.duality l E U none).closed = openSite.integralClosed
  completionV : IntegralOnSlice.completion l E V none ≅
    ambient.reduction ⋙ coefficientSequenceLimit l E V
  completionU : IntegralOnSlice.completion l E U none ≅
    openSite.reduction ⋙ coefficientSequenceLimit l E U
  unitV : ∀ H : DerivedCategory (scalarReductionSource l E V),
    (IntegralOnSlice.completionUnit l E V none).app H ≫ completionV.hom.app H =
      ambient.adjunction.unit.app H
  unitU : ∀ H : DerivedCategory (scalarReductionSource l E U),
    (IntegralOnSlice.completionUnit l E U none).app H ≫ completionU.hom.app H =
      openSite.adjunction.unit.app H
  openUnit : 𝟭 _ ≅ shriek l E j operations ⋙ star l E j operations
  openUnitHom : openUnit.hom = (openAdjunction l E j operations).unit
  restrictionCompletion : IntegralOnSlice.completion l E V none ⋙ star l E j operations ≅
    star l E j operations ⋙ IntegralOnSlice.completion l E U none
  restrictionUnit : ∀ H : DerivedCategory (scalarReductionSource l E V),
    (star l E j operations).map ((IntegralOnSlice.completionUnit l E V none).app H) ≫
        restrictionCompletion.hom.app H =
      (IntegralOnSlice.completionUnit l E U none).app ((star l E j operations).obj H)

variable (C : Context l E j)

/-- Ordinary tensor on the ambient site, exactly the tensor used in completedTensor.
Source: Tag 0GL1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
abbrev tensorV := (IntegralOnSlice.duality l E V none).closed.tensor

/-- The same ordinary tensor on the open site.
Source: Tag 0GL1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
abbrev tensorU := (IntegralOnSlice.duality l E U none).closed.tensor

/-- The source ordinary tensor functor H(K,N).
Source: Tag 0GL1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
abbrev ordinarySource := (shriek l E j C.operations).prod (𝟭 _) ⋙ tensorV l E (V := V)

/-- The ordinary tensor H_U(K,N), before extension by zero.
Source: Tag 0GL1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
abbrev ordinaryOpen := (𝟭 _).prod (star l E j C.operations) ⋙ tensorU l E (U := U)

/-- The type of ordinary open tensor comparisons, not a choice of such a map.
Source: Tag 0GL1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
abbrev OrdinaryMap := ordinarySource l E j C ≅ ordinaryOpen l E j C ⋙ shriek l E j C.operations

/-- Balanced scalar tensor q_V, including the recorded strict quotient transitions.
Source: node proof step 1, Tag 07A4
(blueprint: lem-pur-completed-open-tensor-system-realization). -/
def reductionTensorV : tensorV l E (V := V) ⋙ C.ambient.reduction ≅
    C.ambient.reduction.prod C.ambient.reduction ⋙ C.ambient.systemClosed.tensor :=
  isoWhiskerRight (eqToIso (congrArg CoefficientClosedStructure.tensor C.tensorV))
    C.ambient.reduction ≪≫ C.ambient.reductionTensor

/-- The corresponding balanced scalar tensor q_U.
Source: node proof step 1, Tag 07A4
(blueprint: lem-pur-completed-open-tensor-system-realization). -/
def reductionTensorU : tensorU l E (U := U) ⋙ C.openSite.reduction ≅
    C.openSite.reduction.prod C.openSite.reduction ⋙ C.openSite.systemClosed.tensor :=
  isoWhiskerRight (eqToIso (congrArg CoefficientClosedStructure.tensor C.tensorU))
    C.openSite.reduction ≪≫ C.openSite.reductionTensor

variable (K : DerivedCategory (scalarReductionSource l E U))
  (N : DerivedCategory (scalarReductionSource l E V))

/-- T is the tensor of whole reductions on the ambient ringed sequence site.
Source: node statement, Tag 0941
(blueprint: lem-pur-completed-open-tensor-system-realization). -/
def sourceSystem : coefficientSequenceDerived l E V :=
  C.ambient.systemClosed.tensor.obj
    (C.ambient.reduction.obj ((shriek l E j C.operations).obj K), C.ambient.reduction.obj N)

/-- S is the open tensor of whole reductions, with its actual quotient transitions.
Source: node statement, Tag 0941
(blueprint: lem-pur-completed-open-tensor-system-realization). -/
def openSystem : coefficientSequenceDerived l E U :=
  C.openSite.systemClosed.tensor.obj
    (C.openSite.reduction.obj K,
      C.openSite.reduction.obj ((star l E j C.operations).obj N))

/-- The simultaneous open tensor map: q_V inverse, reduction of gamma ordinary,
the all-input strict open comparison, then J(q_U). This fixes the system map itself.
Source: node proof steps 1--2, Tag 0GL1
(blueprint: lem-pur-completed-open-tensor-system-realization). -/
def systemMap (γ : OrdinaryMap l E j C) :
    sourceSystem l E j C K N ≅ (J l E j C.operations).obj (openSystem l E j C K N) :=
  ((reductionTensorV l E j C).app ((shriek l E j C.operations).obj K, N)).symm ≪≫
    C.ambient.reduction.mapIso (γ.app (K, N)) ≪≫
    C.strictOpen.r.app ((ordinaryOpen l E j C).obj (K, N)) ≪≫
    (J l E j C.operations).mapIso
      ((reductionTensorU l E j C).app (K, (star l E j C.operations).obj N))

/-- The analogous open tensor substitution identification.
Source: node proof steps 3 and 5
(blueprint: lem-pur-completed-open-tensor-system-realization). -/
def openIdentification :
    (IntegralOnSlice.completedTensor l E U none).obj (K, (star l E j C.operations).obj N) ≅
      (coefficientSequenceLimit l E U).obj (openSystem l E j C K N) :=
  C.completionU.app ((ordinaryOpen l E j C).obj (K, N)) ≪≫
    (coefficientSequenceLimit l E U).mapIso
      ((reductionTensorU l E j C).app (K, (star l E j C.operations).obj N))

/-- The total-complex representative of H.
Source: Tag 0GL1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
abbrev sourceComplex (P : CochainComplex (scalarReductionSource l E U) ℤ)
    (Q : CochainComplex (scalarReductionSource l E V) ℤ) :=
  (OpenSemilinearTensor.total l E V).obj
    ((OpenSemilinearTensor.extensionComplex l E j C.operations).obj P, Q)

/-- The total-complex representative of H_U.
Source: Tag 0GL1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
abbrev openComplex (P : CochainComplex (scalarReductionSource l E U) ℤ)
    (Q : CochainComplex (scalarReductionSource l E V) ℤ) :=
  (OpenSemilinearTensor.total l E U).obj
    (P, (OpenSemilinearTensor.restrictionComplex l E j C.operations).obj Q)

/-- One strict chain map on whole quotient systems, formed before localization.
Source: node proof step 2 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
def strictChain (P : CochainComplex (scalarReductionSource l E U) ℤ)
    (Q : CochainComplex (scalarReductionSource l E V) ℤ) :
    (C.ordinaryV.functor.mapHomologicalComplex (.up ℤ)).obj (sourceComplex l E j C P Q) ≅
      ((systemExtension l E j C.operations).mapHomologicalComplex (.up ℤ)).obj
        ((C.ordinaryU.functor.mapHomologicalComplex (.up ℤ)).obj (openComplex l E j C P Q)) :=
  (C.ordinaryV.functor.mapHomologicalComplex (.up ℤ)).mapIso
      (C.strictOpen.totalComparison.chain P Q) ≪≫
    OpenSemilinearTensor.ordinaryChain l E j C.operations C.ordinaryV C.ordinaryU
      C.strictOpen.ordinary (openComplex l E j C P Q)

variable (P : CochainComplex (scalarReductionSource l E U) ℤ)
  (Q : CochainComplex (scalarReductionSource l E V) ℤ)
  (hP : CochainComplex.IsKFlatIndependentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l E U) P)
  (hQ : CochainComplex.IsKFlatIndependentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l E V) Q)
  (hfP : SemilinearSections.flatTerms.{t + 1, t, max u (t + 1)} (Scheme.ProEt.topology U)
    (completedIntegralCommRingSheafUnrestricted l E U) P)
  (hR : CochainComplex.IsKFlatIndependentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l E U)
    ((OpenSemilinearTensor.restrictionComplex l E j C.operations).obj Q))

/-- The ambient ordinary-tensor representative, using the actual derived-functor counit.
Source: node proof step 1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
def sourceRepresentative :
    (ordinarySource l E j C).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj (sourceComplex l E j C P Q) :=
  (tensorV l E (V := V)).mapIso
      (Iso.prod ((extension l E j C.operations).mapDerivedCategoryFactors.app P)
        (Iso.refl (DerivedCategory.Q.obj Q))) ≪≫
    ((IntegralOnSlice.duality l E V none).models.iso _ _ _ _ _
      (C.strictOpen.kflat P hP hfP) hQ).symm

/-- The open ordinary-tensor representative, retaining the restriction counit.
Source: node proof step 1 (blueprint: lem-pur-completed-open-tensor-system-realization). -/
def openRepresentative :
    (ordinaryOpen l E j C).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj (openComplex l E j C P Q) :=
  (tensorU l E (U := U)).mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj P))
        ((restriction l E j C.operations).mapDerivedCategoryFactors.app Q)) ≪≫
    ((IntegralOnSlice.duality l E U none).models.iso _ _ _ P _ hP hR).symm

/-- Normalization on flat-term K-flat quotient representatives. The displayed strict-chain
augmentation equation is imposed on every local section in every degree and finite level,
before localization. Together these components are equality of augmented strict maps;
they are not a test for equality of arbitrary derived arrows. The two Computations include
the actual scalar-unit augmentations and all quotient transitions. The last square
identifies localization of that single chain map with systemMap itself.
Source: node proof steps 1--3, Tags 0GL1, 0E8I, 0941
(blueprint: lem-pur-completed-open-tensor-system-realization). -/
def RepresentativeLaws (γ : OrdinaryMap l E j C) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ)
    (Q : CochainComplex (scalarReductionSource l E V) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E V) Q)
    (hfP : SemilinearSections.flatTerms.{t + 1, t, max u (t + 1)} (Scheme.ProEt.topology U)
      (completedIntegralCommRingSheafUnrestricted l E U) P)
    (_hfQ : SemilinearSections.flatTerms.{t + 1, t, max u (t + 1)} (Scheme.ProEt.topology V)
      (completedIntegralCommRingSheafUnrestricted l E V) Q),
    ∃ (hR : CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E U)
        ((OpenSemilinearTensor.restrictionComplex l E j C.operations).obj Q))
      (hH : CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E V) (sourceComplex l E j C P Q))
      (hHU : CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E U) (openComplex l E j C P Q))
      (aV : OpenSemilinearTensor.Computation l E C.ambient C.ordinaryV
        (sourceComplex l E j C P Q) hH)
      (aU : OpenSemilinearTensor.Computation l E C.openSite C.ordinaryU
        (openComplex l E j C P Q) hHU),
      (γ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (shriek l E j C.operations).map (openRepresentative l E j C P Q hP hR).hom ≫
          (extension l E j C.operations).mapDerivedCategoryFactors.hom.app
            (openComplex l E j C P Q) =
        (sourceRepresentative l E j C P Q hP hQ hfP).hom ≫
          DerivedCategory.Q.map (C.strictOpen.totalComparison.chain P Q).hom) ∧
      (∀ (n : ℕ) (d : ℤ) (W : V.ProEtᵒᵖ)
        (x : ((sourceComplex l E j C P Q).X d).val.obj W),
        ((finiteExtension l E j C.operations n).map
          ((C.ordinaryU.complexEvaluation l E (openComplex l E j C P Q) n).hom.f d)).val.app W
          (((extensionEvaluation l E j C.operations n).hom.app
            (((C.ordinaryU.functor.mapHomologicalComplex (.up ℤ)).obj
              (openComplex l E j C P Q)).X d)).val.app W
            (((coefficientSequenceEvaluation l E V n).map
              ((strictChain l E j C P Q).hom.f d)).val.app W
              (((C.ordinaryV.complexEvaluation l E (sourceComplex l E j C P Q) n).inv.f d).val.app
                W (coefficientIntegralScalarUnitSection l E V n
                  ((sourceComplex l E j C P Q).X d) W x)))) =
        ((C.coefficients.ordinary n).hom.app ((openComplex l E j C P Q).X d)).val.app W
          (coefficientIntegralScalarUnitSection l E V n
            ((extension l E j C.operations).obj ((openComplex l E j C P Q).X d)) W
            (((C.strictOpen.totalComparison.chain P Q).hom.f d).val.app W x))) ∧
      ((systemMap l E j C (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) γ).hom ≫
          (J l E j C.operations).map
            ((reductionTensorU l E j C).inv.app
                (DerivedCategory.Q.obj P, (star l E j C.operations).obj (DerivedCategory.Q.obj Q)) ≫
              C.openSite.reduction.map (openRepresentative l E j C P Q hP hR).hom ≫ aU.iso.hom) ≫
          (systemExtension l E j C.operations).mapDerivedCategoryFactors.hom.app
            ((C.ordinaryU.functor.mapHomologicalComplex (.up ℤ)).obj (openComplex l E j C P Q)) =
        (reductionTensorV l E j C).inv.app
            ((shriek l E j C.operations).obj (DerivedCategory.Q.obj P), DerivedCategory.Q.obj Q) ≫
          C.ambient.reduction.map (sourceRepresentative l E j C P Q hP hQ hfP).hom ≫ aV.iso.hom ≫
          DerivedCategory.Q.map (strictChain l E j C P Q).hom)

end WeilConjectures.CompletedOpenTensor

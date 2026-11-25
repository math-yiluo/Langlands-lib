/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus

/-! # Finite-quotient scalar-extension models

Source: Stacks 06YY and 0941. The canonical finite quotient, its universal derived
scalar extension and its K-flat comparison are re-exported by the evaluation data.
(blueprint: def-coef-finite-quotient-models).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 128
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v a b r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive

section StandardCoefficientInstances

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] preadditiveCoyoneda SheafOfModules.unit
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
attribute [local irreducible] coefficientOrdinaryScalarAdjunction
attribute [local irreducible] coefficientOrdinaryQuotientNaturalTransformation
attribute [local irreducible] scalarReductionExtension
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] coefficientLocalizedCounitModel
attribute [local irreducible] coefficientFiniteReductionModel
attribute [local irreducible] CoefficientComparisonEquation CoefficientTransitionEquation
attribute [local irreducible] coefficientComplexCompositeTransformation
attribute [local irreducible] coefficientComplexCompositeSourceTransformation
attribute [local irreducible] coefficientUniqueComparisonChoice

set_option backward.defeqAttrib.useBackward false

attribute [local irreducible] coefficientKFlatInclusion
  CoefficientTensorModels.iso coefficientBaseChangeHom coefficientEnrichedAdjunctionMap
  CoefficientClosedStructure.tensor CoefficientClosedStructure.transpose
  CoefficientClosedStructure.evaluation CoefficientClosedStructure.composition
  CoefficientReductionModels CoefficientScalarTensorGenerators

attribute [local irreducible] coefficientOrdinaryQuotient
  coefficientOrdinaryQuotientComponent

attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.instCategory HomologicalComplex.instCategory
  CochainComplex.IsKFlatIndependentCoefficients SheafOfModules.IsFlatOnSite
  SheafOfModules.siteSheafTensorRight
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex.mapBifunctorMap
  HomologicalComplex₂.total HomologicalComplex.single

set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local semireducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier in
/-- The commutative quotient underlying the recorded scalar restriction.
Source: Stacks 06YY, node proof step 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotient {m n : ℕ} (h : n ≤ m) :
    integralCoefficientCommRingSheaf l E W m ⟶ integralCoefficientCommRingSheaf l E W n where
  hom :=
    { app := fun V ↦ CommRingCat.ofHom ((normalizedDVRQuotient l E W h).hom.app V).hom
      naturality := fun {_ _} f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((normalizedDVRQuotient l E W h).hom.naturality f) }

set_option linter.defProp false in
/-- The recorded universal change-of-rings witness, now for B_m → B_n.
Source: Stacks 06YY, node proof steps 5, 7 and 10
(blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientExistence {m n : ℕ} (h : n ≤ m) :
    ∃ (F : normalizedDVRModules l E W m ⥤ normalizedDVRModules l E W n)
      (hobj : ∀ M : normalizedDVRModules l E W m,
        F.obj M = SheafOfModules.changeOfRings (coefficientFiniteQuotient l E W h) M)
      (_ : ∀ {M N : normalizedDVRModules l E W m} (f : M ⟶ N),
        F.map f = eqToHom (hobj M) ≫
          SheafOfModules.changeOfRingsHom (coefficientFiniteQuotient l E W h) M f ≫
            eqToHom (hobj N).symm)
      (_ : F.Additive),
      (∀ {P Q : CochainComplex (normalizedDVRModules l E W m) ℤ} (f : P ⟶ Q),
        CochainComplex.IsKFlatIndependentCoefficients
          (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
        CochainComplex.IsKFlatIndependentCoefficients
          (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) Q →
        QuasiIso f → QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f)) ∧
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (HomotopyCategory.quasiIso (normalizedDVRModules l E W m) (.up ℤ)) ∧
      ∃ (LF : normalizedDVRDerived l E W m ⥤ normalizedDVRDerived l E W n)
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (normalizedDVRModules l E W m) (.up ℤ)) ∧
          (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
          ∀ P : CochainComplex (normalizedDVRModules l E W m) ℤ,
            CochainComplex.IsKFlatIndependentCoefficients
              (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
              IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := Scheme.ProEt.topology W) (coefficientFiniteQuotient l E W h)

attribute [local irreducible] coefficientFiniteQuotientExistence

/-- Ordinary extension along the actual finite quotient, with tensor objects and maps fixed.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientExtension {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModules l E W m ⥤ normalizedDVRModules l E W n :=
  (coefficientFiniteQuotientExistence l E W h).choose

/-- The ordinary quotient extension has exactly the recorded sheafified tensor object.
Source: Stacks 06YY, node proof steps 5 and 10
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: specialize the object equality of the recorded derived-change-of-rings
witness used to define coefficientFiniteQuotientExtension. Its first component
is this very extension functor and its second component is the displayed equality. -/
theorem coefficientFiniteQuotientExtension_obj {m n : ℕ} (h : n ≤ m)
    (M : normalizedDVRModules l E W m) :
    (coefficientFiniteQuotientExtension l E W h).obj M =
      SheafOfModules.changeOfRings (coefficientFiniteQuotient l E W h) M := by
  exact (coefficientFiniteQuotientExistence l E W h).choose_spec.choose M

/-- Additivity supplied by the recorded change-of-rings witness.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable instance coefficientFiniteQuotientExtensionAdditive {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientExtension l E W h).Additive :=
  (coefficientFiniteQuotientExistence l E W h).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The universal derived pair for the actual finite quotient.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientDerivedExistence {m n : ℕ} (h : n ≤ m) :
    ∃ (LF : normalizedDVRDerived l E W m ⥤ normalizedDVRDerived l E W n)
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (coefficientFiniteQuotientExtension l E W h).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (normalizedDVRModules l E W m) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (normalizedDVRModules l E W m) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients
            (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (coefficientFiniteQuotientExistence l E W h).choose_spec.choose_spec.choose_spec.choose_spec.2.2

attribute [local irreducible] coefficientFiniteQuotientDerivedExistence

/-- Derived scalar extension B_m → B_n from the recorded change-of-rings construction.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientDerived {m n : ℕ} (h : n ≤ m) :
    normalizedDVRDerived l E W m ⥤ normalizedDVRDerived l E W n :=
  (coefficientFiniteQuotientDerivedExistence l E W h).choose

/-- Its universal comparison on homotopy complexes, invertible on K-flat representatives.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientCounit {m n : ℕ} (h : n ≤ m) :
    DerivedCategory.Qh ⋙ coefficientFiniteQuotientDerived l E W h ⟶
      (coefficientFiniteQuotientExtension l E W h).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  (coefficientFiniteQuotientDerivedExistence l E W h).choose_spec.choose

/-- The recorded finite-quotient universal counit is invertible on K-flat complexes.
Source: Stacks 06YY, node proof steps 5, 7 and 10
(blueprint: lem-coef-derived-system-evaluation-calculus).
Proof: specialize the K-flat counit clause of the recorded derived-change-of-rings
witness to the actual quotient B_m → B_n and the given representative. This is
exactly the universal counit used here, so no additional comparison is needed. -/
theorem coefficientFiniteQuotientCounit_isIso {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P) :
    IsIso ((coefficientFiniteQuotientCounit l E W h).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  exact (coefficientFiniteQuotientDerivedExistence l E W h).choose_spec.choose_spec.2.2 P hP

/-- The canonical K-flat computation, using precisely the universal change-of-rings counit.
Source: Stacks 06YY (blueprint: lem-coef-derived-system-evaluation-calculus). -/
noncomputable def coefficientFiniteQuotientModel {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E W m) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m) P) :
    (coefficientFiniteQuotientDerived l E W h).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  coefficientLocalizedCounitModel (coefficientFiniteQuotientDerived l E W h) P
    (((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex (.up ℤ)).obj P)
    ((coefficientFiniteQuotientCounit l E W h).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
    (coefficientFiniteQuotientCounit_isIso l E W h P hP)

attribute [local irreducible] coefficientFiniteQuotientModel

end StandardCoefficientInstances

end WeilConjectures

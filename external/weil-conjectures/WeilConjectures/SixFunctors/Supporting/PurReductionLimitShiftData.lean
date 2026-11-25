/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # Normalized coefficient reduction and limit shift data

The canonical helpers and the data record formerly declared in
`WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction`. The limit model is written with
its standard composite comparison to avoid expanding large coefficient instances.
Source: Stacks 07A6, 0941, 08TC and derived.tex 0A8D
(blueprint: def-coef-reduction-limit-shift-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genInjectivity false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceRestriction coefficientSequenceEvaluation
  coefficientFiniteDerivedExtension scalarReductionExtension coefficientFiniteReductionModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The canonical comparison from the actual sequence limit to the termwise
limit of a specified K-injective replacement of the restricted sequence.
It is the exact restriction/localization comparison, followed by `Rlim(j)` and
`rightDerivedFunctorObjQIso`; no new choice of a derived functor is made.
Source: Stacks 0941 and 0D6E
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientLimitModel
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j] :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  SequenceKInjectiveComparison.comparisonIso (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) N I j

/-- The shifted replacement map is exactly `j[r]`, with the canonical termwise
identification `U(N[r]) ≅ (UN)[r]` in its source.
Source: Stacks 0941, derived.tex 070H
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientShiftedResolution
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) (r : ℤ) :
    ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (N⟦r⟧) ⟶ I⟦r⟧ :=
  (((coefficientSequenceRestriction l E W).mapHomologicalComplex
    (ComplexShape.up ℤ)).commShiftIso r).hom.app N ≫ j⟦r⟧'

/-- The canonical product comparison for the evaluated shifted tower, using
localization's cochain shift and preservation of products by the shift equivalence.
Source: Stacks 0941 and derived.tex 0BK6
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientRoosProductShift
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E W))]
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (r : ℤ) :
    (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj ((I⟦r⟧).asFunctor.obj (op n))) ≅
      (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))⟦r⟧ :=
  Limits.Pi.mapIso (fun n : ℕ ↦ (DerivedCategory.Q.commShiftIso r).app
    (I.asFunctor.obj (op n))) ≪≫
      (PreservesProduct.iso (shiftFunctor _ r)
        (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))).symm

/-- A Roos triangle whose first vertex is the actual sequence-limit functor,
computed on a specified simultaneous K-injective tower. Its first arrow is
normalized by the actual limit-cone projections through `purCoefficientLimitModel`.
Source: Stacks 0941 and 08TC
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
structure PurCoefficientRoosTriangle
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E W))]
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j] where
  p : (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ⟶
    ∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))
  δ : (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))) ⟶
    ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N))⟦(1 : ℤ)⟧
  triangle : IsDerivedLimitTriangle
    (fun n : ℕ ↦ DerivedCategory.Q.map
      (I.asFunctor.map (homOfLE (Nat.le_succ n)).op))
    ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N)) p δ
  projection : ∀ n : ℕ,
    p ≫ Limits.Pi.π _ n = (purCoefficientLimitModel l E W N I j).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lim.π (op n)) (ComplexShape.up ℤ)).app I)

attribute [local irreducible] coefficientSequenceLimit coefficientConstantTowerLimit

/-- Normalized shifts for the given reduction/limit adjunction. Finite shifts
are fixed by the existing K-flat model, not chosen to match reduction afterwards.
The limit equation uses the fixed resolution comparison for `j` and `j[r]`.
The Roos connecting-map equation uses that same `limit_shift` and the actual
limit triangles, with the cochain sign `r.negOnePow`.
Source: Stacks 07A6, 0941 and derived.tex 0A8D
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
structure PurReductionLimitShiftData
    (S : CoefficientDerivedSystemCalculus l E W) where
  reduction_shift : S.reduction.CommShift ℤ
  finite_reduction_shift :
    ∀ n : ℕ, (coefficientFiniteDerivedExtension l E W n).CommShift ℤ
  finite_shift_model :
    ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
      (hQr : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          (Q⟦r⟧)),
      letI := finite_reduction_shift n
      (coefficientFiniteDerivedExtension l E W n).map
          ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
        ((coefficientFiniteDerivedExtension l E W n).commShiftIso r).hom.app
          (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E W Q hQ n).hom⟦r⟧' =
      (coefficientFiniteReductionModel l E W (Q⟦r⟧) hQr n).hom ≫
        DerivedCategory.Q.map
          ((((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso r).hom.app Q) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)
  reduction_shift_evaluation :
    ∀ n : ℕ,
      letI := reduction_shift
      letI := finite_reduction_shift n
      NatTrans.CommShift (S.reductionEvaluation n).hom ℤ
  limit_shift : (coefficientSequenceLimit l E W).CommShift ℤ
  limit_shift_resolution :
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
      (r : ℤ) [(I⟦r⟧).IsKInjective]
      [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
      letI := limit_shift
      (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N) ≫
        (purCoefficientLimitModel l E W N I j).hom⟦r⟧' =
      (purCoefficientLimitModel l E W (N⟦r⟧) (I⟦r⟧)
        (purCoefficientShiftedResolution l E W N I j r)).hom ≫
        DerivedCategory.Q.map
          ((((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso r).hom.app I) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)
  products : HasCountableProducts (DerivedCategory (scalarReductionSource l E W))
  roos :
    letI := products
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j],
      PurCoefficientRoosTriangle l E W N I j
  roos_triangle_shift :
    letI := products
    letI := limit_shift
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
      (r : ℤ) [(I⟦r⟧).IsKInjective]
      [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).p ≫
        (purCoefficientRoosProductShift l E W I r).hom =
      (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N) ≫ (roos N I j).p⟦r⟧') ∧
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).δ ≫
        ((coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
          ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
            (DerivedCategory.Q.obj N))⟦(1 : ℤ)⟧' =
      r.negOnePow • ((purCoefficientRoosProductShift l E W I r).hom ≫
        (roos N I j).δ⟦r⟧' ≫ (shiftFunctorComm _ 1 r).hom.app
          ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N))))
  unit_shift :
    letI := reduction_shift
    letI := limit_shift
    ∀ r : ℤ,
      Adjunction.CommShift.CompatibilityUnit S.adjunction
        (S.reduction.commShiftIso r)
        ((coefficientSequenceLimit l E W).commShiftIso r)
  counit_shift :
    letI := reduction_shift
    letI := limit_shift
    ∀ r : ℤ,
      Adjunction.CommShift.CompatibilityCounit S.adjunction
        (S.reduction.commShiftIso r)
        ((coefficientSequenceLimit l E W).commShiftIso r)

end WeilConjectures

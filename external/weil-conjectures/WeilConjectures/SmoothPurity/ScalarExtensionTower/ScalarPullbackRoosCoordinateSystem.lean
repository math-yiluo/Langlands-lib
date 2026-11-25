/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRoosCoordinates
import all WeilConjectures.SmoothPurity.IntegralCoherence.IntegralGoodQuotientPresentation

/-! # Moving the system comparison into scalar/pullback Roos coordinates

Source: Stacks 06YY, 07A4 and 0941. This is the formal system-comparison
part of the scalar/pullback realization calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard integralOrdinaryScalar
  integralComparisonSystemScalarPullback integralComparisonSequenceScalarPullback
  integralComparisonSequenceScalarModel coefficientSequenceLimit

-- The coefficient-functor comparisons exceed the default elaboration budget.
/-- Move the inverse scalar/pullback system comparison through the explicit coordinate.
Source: Stacks 06YY, 07A4 and 0941; step 2 of stage3-pur-scalar-pullback-left-roos.
(blueprint: lem-pur-scalar-pullback-roos-coordinate-system).

Proof: finite evaluations identify C with the quotient complexes of the good P.
Detect K-flatness on those levels. The system comparison therefore computes on C
by its defining normalized counit equation. Precompose that equation with its
inverse and cancel. Naturality of the inverse comparison moves the presentation
map SE.reduction(eP inverse) followed by eC across the comparison. Apply the limit
functor to the resulting equality and retain the same Roos bridge and strict q.
This proves the stated entire-system equation before any completed-operation
normalization. -/
theorem scalarPullbackRoosCoordinate_system
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (ρ : IntegralComparisonRoosModel.{u, u} l L X)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (eP : DerivedCategory.Q.obj P.obj ≅ K)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj) :
    let T := coefficientSequenceLimit.{u, u} l L X
    let B := integralComparisonDerivedSequencePullback.{u, u} l L f
    let A := integralComparisonDerivedSequenceScalar.{u, u} l E L ι Y
    let β := integralComparisonSystemScalarPullback.{u, u} l E L ι f
    let a := SE.reduction.map eP.inv ≫ eC.hom
    let CS := ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
      (.up ℤ)).obj C
    let b :=
      (integralComparisonSequencePullback.{u, u} l L f).mapDerivedCategoryFactors.hom.app CS
    let r := (integralComparisonRoosBridge.{u, u} l L X ρ
      (((integralComparisonSequencePullback l L f).mapHomologicalComplex (.up ℤ)).obj CS)).hom
    let z := DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)
    T.map (β.inv.app (SE.reduction.obj K)) ≫
        scalarPullbackRoosCoordinate l E L ι f P C SE ρ K eP eC q =
      T.map (B.map (A.map a ≫
        (integralComparisonSequenceScalarModel.{u, u} l E L ι Y).ε.app C) ≫ b) ≫ r ≫ z := by
  classical
  dsimp only
  let T := coefficientSequenceLimit.{u, u} l L X
  let B := integralComparisonDerivedSequencePullback.{u, u} l L f
  let CS := ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
    (.up ℤ)).obj C
  let t := (integralComparisonSequenceScalarModel.{u, u} l E L ι Y).ε.app C
  let b := (integralComparisonSequencePullback.{u, u} l L f).mapDerivedCategoryFactors.hom.app CS
  let r := (integralComparisonRoosBridge.{u, u} l L X ρ
    (((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj CS)).hom
  let z := DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)
  have hk : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E Y) C := by
    apply WeilConjectures.kflat_of_levels l E Y
    intro n
    exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E Y n)
      (κ n).symm ((coefficientTensorModelPreservation l E Y).1 P.obj P.property.1 n)
  let β := integralComparisonSystemScalarPullback.{u, u} l E L ι f
  let a := SE.reduction.map eP.inv ≫ eC.hom
  have hβ := (integralComparisonSystemScalarPullback_existsUnique l E L ι f).exists.choose_spec
    C hk
  have hβ' : β.inv.app (DerivedCategory.Q.obj C) ≫
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι X).map
        ((integralComparisonSequencePullback.{u, u} l E f).mapDerivedCategoryFactors.hom.app C) ≫
      (integralComparisonSequenceScalarModel.{u, u} l E L ι X).ε.app
        (((integralComparisonSequencePullback.{u, u} l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (integralComparisonSequenceScalarPullback.{u, u} l E L ι f) (.up ℤ)).hom.app C) =
      B.map t ≫ b := by
    have h := congrArg
      ((integralComparisonSystemScalarPullback_existsUnique l E L ι f).exists.choose.inv.app
        (DerivedCategory.Q.obj C) ≫ ·) hβ
    simpa only [β, integralComparisonSystemScalarPullback, Category.assoc,
      Iso.inv_hom_id_app_assoc, B, t, b, CS] using h
  unfold scalarPullbackRoosCoordinate
  change T.map (β.inv.app (SE.reduction.obj K)) ≫ T.map _ ≫ r ≫ z = _
  erw [← T.map_comp_assoc]
  apply congrArg (fun g ↦ T.map g ≫ r ≫ z)
  have hn := β.inv.naturality a
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  erw [hβ']
  dsimp only [a, B, t, b, CS]
  simp only [Functor.map_comp, Category.assoc]

end WeilConjectures.ScalarExtensionTower

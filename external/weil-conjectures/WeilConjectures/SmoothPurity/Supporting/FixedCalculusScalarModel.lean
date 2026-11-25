/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison
import WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientScalarTowerComparison
import all WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence

/-! # Scalar realization over a fixed quotient calculus -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard

/-- A quotient-normalized scalar realization for any fixed reduction calculus.
Source: Stacks 03EK, 03D7, 06YY and 0941.
(blueprint: lem-pur-fixed-calculus-scalar-model).

Proof: choose the normalized ordinary and derived quotient models for the fixed
calculus. Evaluated quotients of a good complex are K-flat; the componentwise
criterion gives K-flatness of the whole sequence. Its scalar cochain counit,
Roos bridge and balanced ordinary scalar tower comparison form a natural iso.
Descend it along the good-complex localization. For any coherent presentation,
its comparison with the fixed quotient model is a strict iso fixing every finite
comparison and the entire derived comparison. Naturality of the scalar counit
and cancellation of this strict iso give the asserted normalization. -/
theorem fixedCalculusScalarModel
    (W : Scheme.{u})
    (SW : CoefficientDerivedSystemCalculus l E W)
    (ρW : IntegralComparisonRoosModel l L W) :
    Nonempty (IntegralComparisonScalarModel l E L ι W SW ρW) := by
  obtain ⟨M, ⟨D⟩⟩ := CompletionUnit.fixedCalculusModels l E W SW
  have hD (P : (integralOperationsGoodComplex l E W).FullSubcategory)
      (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (e : SW.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
          (unrestrictedIntegralFiniteComplex l E W n).obj P.obj)
      (_hp : CoefficientReductionPresentation l E W SW.toCoefficientDerivedSystemReduction
        P.obj P.property.1 C e κ)
      (hc : IsIntegralComparisonPresentationCoherent l E W SW P.obj C e κ) :=
    coherentQuotientModelComparison l E W SW M D P.obj C e κ hc
  obtain ⟨θ, hθ⟩ := ordinaryQuotientScalarTowerComparison l E L ι W M
  let A := (integralOperationsGoodComplex l E W).ι
  let R := M.quotient l E W
  let F := (integralComparisonSequenceScalarModel l E L ι W).E
  let U := coefficientSequenceRestriction l L W
  let H : (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l L W) ℤ) ⥤
      DerivedCategory (scalarReductionSource l L W) :=
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let T := F.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let LL := coefficientSequenceLimit l L W
  let V := integralComparisonDerivedSequenceScalar l E L ι W ⋙ LL
  let η : DerivedCategory.Q ⋙ V ⟶ T ⋙ H :=
    Functor.whiskerRight (integralComparisonSequenceScalarModel l E L ι W).ε LL ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (Functor.isoWhiskerRight U.mapDerivedCategoryFactors
            (coefficientConstantTowerLimit l L W) ≪≫
          Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ)) ρW.comparison).hom
  have hη (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      IsIso (η.app (R.obj P.obj)) := by
    have hk : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) (R.obj P.obj) := by
      apply sequenceKFlat_of_evaluations l E W
      intro n
      exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E W n)
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P.obj).symm
        ((coefficientTensorModelPreservation l E W).1 P.obj P.property.1 n)
    have := (integralComparisonSequenceScalarModel l E L ι W).computes _ hk
    dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let d : integralOperationsGoodLocalization l E W ⋙ SW.reduction ≅
      A ⋙ R ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      haveI := D.reduction_isIso P.obj P.property.1 P.property.2
      exact asIso (D.reductionComparison.app P.obj)) (by
        intro P Q a
        exact D.reductionComparison.naturality a.hom)
  have : IsIso (Functor.whiskerLeft (A ⋙ R) η) :=
    (NatTrans.isIso_iff_isIso_app _).2 hη
  let δ : integralOperationsGoodLocalization l E W ⋙ (SW.reduction ⋙ V) ≅
      integralScalarOnGood l E L ι W :=
    Functor.isoWhiskerRight d V ≪≫ asIso (Functor.whiskerLeft (A ⋙ R) η) ≪≫
      Functor.isoWhiskerLeft A (Functor.isoWhiskerRight θ H)
  obtain ⟨r, hr, _⟩ :=
    (integralScalarExtensionWellDefined l E L ι W).2.choose_spec.choose_spec.2.2.1
      (SW.reduction ⋙ V) δ
  change Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E W) r ≪≫ δ =
    integralScalarExtensionComparisonOfUniverses l E L ι W at hr
  refine ⟨⟨r, ?_⟩⟩
  intro P C e κ hp hc
  obtain ⟨a, ha, hκ⟩ := hD P C e κ hp hc
  let q := T.mapIso a.symm ≪≫ θ.app P.obj
  refine ⟨q, hθ P.obj C a κ hκ, ?_⟩
  have he := congrArg (fun z ↦ z.hom.app P) hr
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (V.map (D.reductionComparison.app P.obj) ≫ η.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj)) =
    (integralScalarExtensionComparisonOfUniverses l E L ι W).hom.app P at he
  have hn := η.naturality a.hom
  change V.map (DerivedCategory.Q.map a.hom) ≫ η.app C =
    η.app (R.obj P.obj) ≫ H.map (T.map a.hom) at hn
  have hq : T.map a.hom ≫ q.hom = θ.hom.app P.obj := by
    dsimp only [q]
    change T.map a.hom ≫ (T.map a.inv ≫ θ.hom.app P.obj) = _
    rw [← Category.assoc, ← T.map_comp, a.hom_inv_id, T.map_id, Category.id_comp]
  have hcancel : H.map (T.map a.hom) ≫ H.map q.hom = H.map (θ.hom.app P.obj) := by
    rw [← H.map_comp, hq]
  have hcomp : V.map e.hom ≫ η.app C ≫ H.map q.hom =
      V.map (D.reductionComparison.app P.obj) ≫ η.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj) := by
    rw [← ha, V.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (V.map (DerivedCategory.Q.map a.hom)), hn]
    simp only [Category.assoc]
    rw [hcancel]
  have hηC : LL.map ((integralComparisonSequenceScalarModel l E L ι W).ε.app C) ≫
      (integralComparisonRoosBridge l L W ρW _).hom = η.app C := by
    rfl
  have hfirst :
      LL.map ((integralComparisonDerivedSequenceScalar l E L ι W).map e.hom) ≫
        LL.map ((integralComparisonSequenceScalarModel l E L ι W).ε.app C) ≫
          (integralComparisonRoosBridge l L W ρW _).hom ≫ H.map q.hom =
      V.map e.hom ≫ η.app C ≫ H.map q.hom := by
    simpa only [V, Functor.comp_map, Category.assoc] using
      congrArg (fun g ↦ V.map e.hom ≫ g ≫ H.map q.hom) hηC
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (LL.map ((integralComparisonDerivedSequenceScalar l E L ι W).map e.hom) ≫
        LL.map ((integralComparisonSequenceScalarModel l E L ι W).ε.app C) ≫
          (integralComparisonRoosBridge l L W ρW _).hom ≫ H.map q.hom) = _
  rw [hfirst, hcomp]
  exact he

end WeilConjectures

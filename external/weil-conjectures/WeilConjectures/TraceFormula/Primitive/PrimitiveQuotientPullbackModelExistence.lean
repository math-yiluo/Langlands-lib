/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientReductionComparison
import WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison

/-! # Primitive quotient pullback model existence

This is the pullback conjunct split from
`primitiveQuotientRealizationComparisons`.
The comparison tests whole-system adjunction-coherent quotient presentations.
Source: Stacks 099N(5), 06YY and 0941.
(blueprint: lem-trf-primitive-quotient-pullback-model-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict K-flat construction and the normalized Roos comparison produce the
required realization. Source: Stacks 099N(2),(5), 06YS, 0G7E and 0941.
Proof: choose the flat-term K-flat representative supplied by the reduction
calculus. Apply independent-coefficient change of rings at every quotient level,
identify the resulting strict pullback tower with the defining Roos tower, and
apply the fixed normalized Roos comparison. The resulting isomorphism is natural
on the whole derived category by descent from the K-flat class. The remaining
normalization equation is checked on every whole-system coherent reduction
presentation by naturality of the fixed comparisons and cancellation of the
strict quotient isomorphism. Finite evaluations are not used to detect derived maps.
This theorem is the pullback
conjunct split from `primitiveQuotientRealizationComparisons`.
(blueprint: lem-trf-primitive-quotient-pullback-model-existence) -/
theorem primitiveQuotientPullbackModelExistence
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρX : IntegralComparisonRoosModel l E X) :
    Nonempty (IntegralComparisonPullbackModel l E f SY ρX) := by
  obtain ⟨M, D, hD⟩ := coherentQuotientReductionComparison l E Y _hlY SY
  obtain ⟨θ, hθ⟩ := ordinaryQuotientPullbackTowerComparison l E f M
  let A := (integralOperationsGoodComplex l E Y).ι
  let R := M.quotient l E Y
  let F := integralComparisonSequencePullback l E f
  let U := coefficientSequenceRestriction l E X
  let H : (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ) ⥤
      DerivedCategory (scalarReductionSource l E X) :=
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let T := F.mapHomologicalComplex (.up ℤ) ⋙ U.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let L := coefficientSequenceLimit l E X
  let V := integralComparisonDerivedSequencePullback l E f ⋙ L
  let η : DerivedCategory.Q ⋙ V ≅ T ⋙ H :=
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors L ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (Functor.isoWhiskerRight U.mapDerivedCategoryFactors
            (coefficientConstantTowerLimit l E X) ≪≫
          Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ)) ρX.comparison)
  let d : integralOperationsGoodLocalization l E Y ⋙ SY.reduction ≅
      A ⋙ R ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      haveI := D.reduction_isIso P.obj P.property.1 P.property.2
      exact asIso (D.reductionComparison.app P.obj)) (by
        intro P Q a
        exact D.reductionComparison.naturality a.hom)
  let δ : integralOperationsGoodLocalization l E Y ⋙ (SY.reduction ⋙ V) ≅
      integralOperationsPullbackOnGood l E f :=
    Functor.isoWhiskerRight d V ≪≫ Functor.isoWhiskerLeft (A ⋙ R) η ≪≫
      Functor.isoWhiskerLeft A (Functor.isoWhiskerRight θ H)
  have descended := (integralOperationsWellDefined l E f X).2.2.choose_spec.choose_spec
  have huniq := descended.choose_spec.choose_spec.1
  obtain ⟨r, hr, _⟩ := huniq (SY.reduction ⋙ V) δ
  change Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) r ≪≫ δ =
    integralDerivedPullbackComparison l E f at hr
  refine ⟨⟨r, ?_⟩⟩
  intro P C e κ hp hc
  obtain ⟨a, ha, hκ⟩ := hD P C e κ hp hc
  let q := T.mapIso a.symm ≪≫ θ.app P.obj
  refine ⟨q, hθ P.obj C a κ hκ, ?_⟩
  have he := congrArg (fun z ↦ z.hom.app P) hr
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (V.map (D.reductionComparison.app P.obj) ≫ η.hom.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj)) =
    (integralDerivedPullbackComparison l E f).hom.app P at he
  have hn := η.hom.naturality a.hom
  change V.map (DerivedCategory.Q.map a.hom) ≫ η.hom.app C =
    η.hom.app (R.obj P.obj) ≫ H.map (T.map a.hom) at hn
  have hη : (L.map ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
      L.map (F.mapDerivedCategoryFactors.hom.app C) ≫
        (integralComparisonRoosBridge l E X ρX _).hom) =
      V.map e.hom ≫ η.hom.app C := by
    rfl
  have hq : T.map a.hom ≫ q.hom = θ.hom.app P.obj := by
    dsimp only [q]
    change T.map a.hom ≫ (T.map a.inv ≫ θ.hom.app P.obj) = _
    rw [← Category.assoc, ← T.map_comp, a.hom_inv_id, T.map_id, Category.id_comp]
  have hcancel : H.map (T.map a.hom) ≫ H.map q.hom = H.map (θ.hom.app P.obj) := by
    rw [← H.map_comp, hq]
  have hcomp : V.map e.hom ≫ η.hom.app C ≫ H.map q.hom =
      V.map (D.reductionComparison.app P.obj) ≫ η.hom.app (R.obj P.obj) ≫
        H.map (θ.hom.app P.obj) := by
    rw [← ha, V.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (V.map (DerivedCategory.Q.map a.hom)), hn]
    simp only [Category.assoc]
    rw [hcancel]
  have hfirst :
      L.map ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
        L.map (F.mapDerivedCategoryFactors.hom.app C) ≫
          (integralComparisonRoosBridge l E X ρX _).hom ≫ H.map q.hom =
      V.map e.hom ≫ η.hom.app C ≫ H.map q.hom := by
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ H.map q.hom) hη
  change r.hom.app (DerivedCategory.Q.obj P.obj) ≫
      (L.map ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
        L.map (F.mapDerivedCategoryFactors.hom.app C) ≫
          (integralComparisonRoosBridge l E X ρX _).hom ≫ H.map q.hom) = _
  rw [hfirst, hcomp]
  exact he

end WeilConjectures

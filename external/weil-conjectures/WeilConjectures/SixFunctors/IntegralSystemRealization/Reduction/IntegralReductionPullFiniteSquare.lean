/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteScalarPullCochainModel
import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullOrdinarySquare
import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullEvaluationQuotient
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientReductionPresentation
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Finite scalar pullback in the canonical quotient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
attribute [local instance] WeilConjectures.coefficientFiniteExtensionAdditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finite_square_pasting
    {C : Type*} [Category C]
    {A B C₁ D Z B₁ C₂ E₁ F₁ G₁ H₁ T₁ I₁ J₁ K₁ L₁ M₁ N₁ : C}
    (v : A ⟶ B) (ev : B ⟶ C₁) (ty : C₁ ⟶ D) (ν : N₁ ⟶ D) (tx : A ⟶ N₁)
    (ry : B ⟶ B₁) (vy : C₁ ⟶ C₂) (ev' : B₁ ⟶ C₂) (wy : C₂ ⟶ E₁)
    (εy : D ⟶ E₁) (i : E₁ ⟶ Z) (sf : B₁ ⟶ F₁) (fac : F₁ ⟶ G₁)
    (q₁ : G₁ ⟶ H₁) (q₂ : H₁ ⟶ T₁) (τ : T₁ ⟶ Z)
    (redc : A ⟶ I₁) (rx : I₁ ⟶ J₁) (qq : J₁ ⟶ F₁)
    (fx : J₁ ⟶ K₁) (qe : K₁ ⟶ G₁) (κx : K₁ ⟶ L₁) (νo : L₁ ⟶ T₁)
    (tpx : I₁ ⟶ M₁) (εx : M₁ ⟶ L₁) (scalarc : N₁ ⟶ M₁) [Mono (εy ≫ i)]
    (hY : vy ≫ wy = ty ≫ εy) (hn : ry ≫ ev' = ev ≫ vy)
    (he : ev' ≫ wy ≫ i = sf ≫ fac ≫ q₁ ≫ q₂ ≫ τ)
    (hm : v ≫ ry ≫ sf = redc ≫ rx ≫ qq) (hf : qq ≫ fac = fx ≫ qe)
    (ho : qe ≫ q₁ ≫ q₂ = κx ≫ νo) (hX : rx ≫ fx ≫ κx = tpx ≫ εx)
    (ht : redc ≫ tpx = tx ≫ scalarc)
    (hs : ν ≫ εy ≫ i = scalarc ≫ εx ≫ νo ≫ τ) :
    v ≫ ev ≫ ty = tx ≫ ν := by
  apply (cancel_mono (εy ≫ i)).1
  simp only [Category.assoc]
  rw [← reassoc_of% hY, ← reassoc_of% hn, he]
  rw [reassoc_of% hm, reassoc_of% hf, reassoc_of% ho, reassoc_of% hX,
    reassoc_of% ht, hs]

private theorem pull_good {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    integralOperationsGoodComplex l E X
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj) := by
  exact AlgebraicGeometry.ProEtale.VaryingRing.ringPull_preserves_flat f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f) P.obj P.property.1 P.property.2

private theorem reduction_eval_model (W : Scheme.{u}) (n : ℕ)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (coefficientSequenceDerivedEvaluation l E W n).map
        ((pullbackTensorReductionModel l E W).hom.app P) ≫
      (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P.obj) =
    ((calculus l E W).reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj) ≫
      (coefficientFiniteReductionModel l E W P.obj P.property.1 n).hom := by
  exact (CompletedQuotient.completedQuotientReductionPresentation l E W P).1 n

private theorem on_good (o : Operations l E) (model : RealizationModel l E o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((model.reductionPull f).hom.app (DerivedCategory.Q.obj P.obj)) ≫
      (pullbackTensorDerivedEvaluation l E f n).hom.app
        ((calculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj)) ≫
      (finiteDerivedPullback l E n f).map
        (((calculus l E Y).reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj)) =
    ((calculus l E X).reductionEvaluation n).hom.app
        ((ringedPull l E f).obj (DerivedCategory.Q.obj P.obj)) ≫
      (integralFiniteScalarPull l E f n).hom.app (DerivedCategory.Q.obj P.obj) := by
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let F := integralOrdinaryPull l E f
  let S := pullbackTensorSequenceInverse l E f
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let EY := coefficientSequenceDerivedEvaluation l E Y n
  let V := finiteDerivedPullback l E n f
  let I := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let PX : (integralOperationsGoodComplex l E X).FullSubcategory :=
    ⟨(F.mapHomologicalComplex (.up ℤ)).obj P.obj, pull_good l E f P⟩
  let CY := ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj
  let CX := ((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj PX.obj
  let v := (model.reductionPull f).hom.app (DerivedCategory.Q.obj P.obj)
  let c := F.mapDerivedCategoryFactors.hom.app P.obj
  let rx := (pullbackTensorReductionModel l E X).hom.app PX
  let ry := (pullbackTensorReductionModel l E Y).hom.app P
  let ty := ((calculus l E Y).reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj)
  let κx := (pullbackTensorReductionEvaluationComplex l E X n).inv.app PX.obj
  let κy := (pullbackTensorReductionEvaluationComplex l E Y n).inv.app P.obj
  let εx := (coefficientFiniteReductionModel l E X PX.obj PX.property.1 n).hom
  let εy := (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom
  let fx := (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app CX
  let fy := (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app CY
  let q := model.ordinary.reductionPullComplex l E f P.obj
  let en := pullbackTensorDerivedEvaluation l E f n
  let ν := ordinaryFiniteScalarPullComplex l E f n P.obj
  let τ := (NatIso.mapHomologicalComplex
    (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
      (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj)
  have hY : EY.map ry ≫ fy ≫ DerivedCategory.Q.map κy = ty ≫ εy :=
    reduction_eval_model l E Y n P
  have hX : EX.map rx ≫ fx ≫ DerivedCategory.Q.map κx =
      ((calculus l E X).reductionEvaluation n).hom.app (DerivedCategory.Q.obj PX.obj) ≫ εx :=
    reduction_eval_model l E X n PX
  have hm := congrArg (fun k ↦ EX.map k) (model.model f P PX.property)
  simp only [Functor.map_comp] at hm
  have hn := en.hom.naturality ry
  dsimp only [Functor.comp_map] at hn
  have hf := (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.naturality q
  dsimp only [Functor.comp_map] at hf
  have ho := congrArg (fun k ↦ DerivedCategory.Q.map k)
    (integralReductionPullOrdinaryComplex l E model.ordinary f n P.obj)
  simp only [DerivedCategory.Q.map_comp] at ho
  have hY' : V.map (EY.map ry) ≫ V.map (fy ≫ DerivedCategory.Q.map κy) =
      V.map ty ≫ V.map εy := by
    simpa only [Functor.map_comp, Category.assoc] using congrArg (fun h ↦ V.map h) hY
  have he := integralReductionPullEvaluationQuotient l E f n P.obj
  dsimp only at he
  simp only [DerivedCategory.Q.map_comp, Category.assoc] at he
  have ht := ((calculus l E X).reductionEvaluation n).hom.naturality c
  dsimp only [Functor.comp_map] at ht
  exact finite_square_pasting
    (v := EX.map v)
    (ev := en.hom.app ((calculus l E Y).reduction.obj (DerivedCategory.Q.obj P.obj)))
    (ty := V.map ty) (ν := (integralFiniteScalarPull l E f n).hom.app
      (DerivedCategory.Q.obj P.obj))
    (tx := ((calculus l E X).reductionEvaluation n).hom.app
      ((ringedPull l E f).obj (DerivedCategory.Q.obj P.obj)))
    (ry := EX.map ((pullbackTensorSequenceDerived l E f).map ry))
    (vy := V.map (EY.map ry)) (ev' := en.hom.app (DerivedCategory.Q.obj CY))
    (wy := V.map (fy ≫ DerivedCategory.Q.map κy)) (εy := V.map εy)
    (i := I.mapDerivedCategoryFactors.hom.app
      (((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (sf := EX.map (S.mapDerivedCategoryFactors.hom.app CY))
    (fac := (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
      ((S.mapHomologicalComplex (.up ℤ)).obj CY))
    (q₁ := DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app CY))
    (q₂ := DerivedCategory.Q.map
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map κy))
    (τ := DerivedCategory.Q.map τ)
    (redc := EX.map ((calculus l E X).reduction.map c)) (rx := EX.map rx)
    (qq := EX.map (DerivedCategory.Q.map q)) (fx := fx)
    (qe := DerivedCategory.Q.map
      (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).map q))
    (κx := DerivedCategory.Q.map κx) (νo := DerivedCategory.Q.map ν)
    (tpx := ((calculus l E X).reductionEvaluation n).hom.app (DerivedCategory.Q.obj PX.obj))
    (εx := εx) (scalarc := (scalarReductionDerivedExtension l E X n).map c)
    hY' hn he hm hf ho hX ht
    (integralFiniteScalarPullCochainModel l E f n P PX.property)

/-- Finite evaluation of the whole-system pullback model is the canonical scalar square.
Source: Stacks 07A4, 07A6, 0941 and 0D6D; fix-prop-coherence, coefficient
comparisons before taking open mates
(blueprint: lem-sf-integral-reduction-pull-finite-square).

Proof: choose a flat-term K-flat representative P of H. Geometric inverse image
preserves flat terms and K-flatness, so model.model applies to P and its inverse
image. Evaluate that equation at n. The ordinary limit projection equation in
model.ordinary identifies the evaluated ordinary conjugate with quotient/pullback
interchange: after inserting the scalar units, both section maps send a section
and its quotient coefficient to the same pulled-back tensor. The unit-normalized
restriction/direct-image comparison defining integralFiniteScalarPull has that
same transpose. The reductionModel equations of the calculus and the cochain
normalization of pullbackTensorDerivedEvaluation cancel the computation
isomorphisms on both sides. This proves the displayed equation on Q(P).
Naturality and the K-flat resolution isomorphism transport it to H. No open
extension, open mate, constructibility, completeness or nonempty-scheme
hypothesis is used; zero complexes and n=0 obey the same tensor equation. -/
theorem integralReductionPullFiniteSquare (o : Operations l E)
    (model : RealizationModel l E o) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : Integral l E Y) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E X n).map ((model.reductionPull f).hom.app H) ≫
      (pullbackTensorDerivedEvaluation l E f n).hom.app ((calculus l E Y).reduction.obj H) ≫
      (finiteDerivedPullback l E n f).map (((calculus l E Y).reductionEvaluation n).hom.app H) =
    ((calculus l E X).reductionEvaluation n).hom.app ((ringedPull l E f).obj H) ≫
      (integralFiniteScalarPull l E f n).hom.app H := by
  let L := integralOperationsGoodLocalization l E Y
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E Y
  let lhs := Functor.whiskerRight (model.reductionPull f).hom
      (coefficientSequenceDerivedEvaluation l E X n) ≫
    Functor.whiskerLeft (calculus l E Y).reduction
      (pullbackTensorDerivedEvaluation l E f n).hom ≫
    Functor.whiskerRight ((calculus l E Y).reductionEvaluation n).hom
      (finiteDerivedPullback l E n f)
  let rhs := Functor.whiskerLeft (ringedPull l E f)
      ((calculus l E X).reductionEvaluation n).hom ≫ (integralFiniteScalarPull l E f n).hom
  have he : lhs = rhs := by
    apply Localization.natTrans_ext L W
    intro P
    exact on_good l E o model f n P
  exact congr_app he H

end WeilConjectures.IntegralSystemRealization

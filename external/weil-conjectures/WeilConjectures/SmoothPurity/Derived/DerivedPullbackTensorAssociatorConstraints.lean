/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import all WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints

import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorCoherentReduction
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorUnit
import WeilConjectures.SmoothPurity.Common.CommonStageUnitorTransport
import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! # Common-stage normalized tensor associator

The common-stage associator and braiding constraints, using the finite
normalized constraints and the directed-stage representative calculation.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Preserve the cached additive-group data while comparing stage Hom types.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

-- Match the category-wrapper proof context used by DerivedPullbackTensorHom.
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  integralCoefficientLinear integralScalarConstant sfIntegralCoefficientLinear
  sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  commonStageTensorComparison commonStagePullbackComparison
  operationStageTransitionIso commonStageDerivedTensor commonStageDerivedPullback

section ScalarAssociator
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
open scoped TensorProduct

private theorem scalarAssoc_chosen_spec {A : Sort*} {p : A → Prop}
    (h : ∃! a, p a) (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private theorem scalarAssoc_tensor_map_heq {C : Type*} [Category* C] (T : C × C ⥤ C)
    {A B D E A' B' D' E' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : D ⟶ E} {g' : D' ⟶ E'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (T.map (Prod.mkHom f g)) (T.map (Prod.mkHom f' g')) := by
  subst A' B' D' E'
  cases hf
  cases hg
  rfl

private theorem scalarAssoc_nested_left
    {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (e : T ⋙ R ≅ R.prod R ⋙ U)
    {A A' B B' C₀ C₀' : C} (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀') :
    R.map (T.map (Prod.mkHom (T.map (Prod.mkHom f g)) h)) ≫
        e.hom.app (T.obj (A', B'), C₀') ≫
        U.map (Prod.mkHom (e.hom.app (A', B')) (𝟙 _)) =
      e.hom.app (T.obj (A, B), C₀) ≫
        U.map (Prod.mkHom (e.hom.app (A, B)) (𝟙 _)) ≫
        U.map (Prod.mkHom (U.map (Prod.mkHom (R.map f) (R.map g))) (R.map h)) := by
  have he (X Y : C × C) (k : X ⟶ Y) :
      R.map (T.map k) ≫ e.hom.app Y =
        e.hom.app X ≫ U.map (Prod.mkHom (R.map k.1) (R.map k.2)) :=
    e.hom.naturality k
  rw [← Category.assoc, he]
  simp only [Category.assoc]
  congr 1
  rw [← U.map_comp, ← U.map_comp]
  congr 1
  ext
  · exact he (A, B) (A', B') (Prod.mkHom f g)
  · simp

private theorem scalarAssoc_nested_right
    {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (e : T ⋙ R ≅ R.prod R ⋙ U)
    {A A' B B' C₀ C₀' : C} (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀') :
    R.map (T.map (Prod.mkHom f (T.map (Prod.mkHom g h)))) ≫
        e.hom.app (A', T.obj (B', C₀')) ≫
        U.map (Prod.mkHom (𝟙 _) (e.hom.app (B', C₀'))) =
      e.hom.app (A, T.obj (B, C₀)) ≫
        U.map (Prod.mkHom (𝟙 _) (e.hom.app (B, C₀))) ≫
        U.map (Prod.mkHom (R.map f) (U.map (Prod.mkHom (R.map g) (R.map h)))) := by
  have he (X Y : C × C) (k : X ⟶ Y) :
      R.map (T.map k) ≫ e.hom.app Y =
        e.hom.app X ≫ U.map (Prod.mkHom (R.map k.1) (R.map k.2)) :=
    e.hom.naturality k
  rw [← Category.assoc, he]
  simp only [Category.assoc]
  congr 1
  rw [← U.map_comp, ← U.map_comp]
  congr 1
  ext
  · simp
  · exact he (B, C₀) (B', C₀') (Prod.mkHom g h)

private theorem scalarAssoc_faithful_naturality
    {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) [R.Faithful] (T : C × C ⥤ C) (U : D × D ⥤ D)
    (e : T ⋙ R ≅ R.prod R ⋙ U)
    (a : ∀ A B C₀, T.obj (T.obj (A, B), C₀) ≅ T.obj (A, T.obj (B, C₀)))
    (b : ∀ A B C₀, U.obj (U.obj (A, B), C₀) ≅ U.obj (A, U.obj (B, C₀)))
    (hb : ∀ {A A' B B' C₀ C₀' : D} (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀'),
      U.map (Prod.mkHom (U.map (Prod.mkHom f g)) h) ≫ (b A' B' C₀').hom =
        (b A B C₀).hom ≫ U.map (Prod.mkHom f (U.map (Prod.mkHom g h))))
    (ha : ∀ A B C₀, R.map (a A B C₀).hom ≫ e.hom.app (A, T.obj (B, C₀)) ≫
      U.map (Prod.mkHom (𝟙 _) (e.hom.app (B, C₀))) =
        e.hom.app (T.obj (A, B), C₀) ≫
          U.map (Prod.mkHom (e.hom.app (A, B)) (𝟙 _)) ≫
            (b (R.obj A) (R.obj B) (R.obj C₀)).hom)
    {A A' B B' C₀ C₀' : C} (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀') :
    T.map (Prod.mkHom (T.map (Prod.mkHom f g)) h) ≫ (a A' B' C₀').hom =
      (a A B C₀).hom ≫ T.map (Prod.mkHom f (T.map (Prod.mkHom g h))) := by
  apply R.map_injective
  let d := e.app (A', T.obj (B', C₀')) ≪≫
    U.mapIso (Iso.prod (Iso.refl _) (e.app (B', C₀')))
  apply (cancel_mono d.hom).1
  change _ ≫ (e.hom.app (A', T.obj (B', C₀')) ≫
    U.map (Prod.mkHom (𝟙 _) (e.hom.app (B', C₀')))) =
    _ ≫ (e.hom.app (A', T.obj (B', C₀')) ≫
    U.map (Prod.mkHom (𝟙 _) (e.hom.app (B', C₀'))))
  simp only [Functor.map_comp, Category.assoc]
  rw [ha]
  have hl := congrArg (fun z ↦ z ≫ (b (R.obj A') (R.obj B') (R.obj C₀')).hom)
    (scalarAssoc_nested_left R T U e f g h)
  simp only [Category.assoc] at hl
  rw [hl, hb, scalarAssoc_nested_right R T U e f g h]
  simpa only [Category.assoc] using (congrArg
    (fun z ↦ z ≫ U.map (Prod.mkHom (R.map f)
      (U.map (Prod.mkHom (R.map g) (R.map h))))) (ha A B C₀)).symm

private theorem scalarAssoc_integral_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    {M N P M' N' P' : sfIntegralConstructibleCategory l E W}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom ((constructibleIntegralTensor l E W).map (Prod.mkHom f g)) h) ≫
        (pullbackTensorIntegralAssociator l E W M' N' P').hom =
      (pullbackTensorIntegralAssociator l E W M N P).hom ≫
        (constructibleIntegralTensor l E W).map
          (Prod.mkHom f ((constructibleIntegralTensor l E W).map (Prod.mkHom g h))) := by
  have := (coherentReduction_fullyFaithful l E W).2
  apply scalarAssoc_faithful_naturality (coherentReduction l E W)
    (constructibleIntegralTensor l E W) (pullbackTensorCalculus l E W).systemClosed.tensor
    (reduction_tensor l E W) (pullbackTensorIntegralAssociator l E W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.associator
  · intro M N P M' N' P' f g h
    exact @MonoidalCategory.associator_naturality _ _
      (pullbackTensorCalculus l E W).systemClosed.monoidal _ _ _ _ _ _ f g h
  · intro M N P
    unfold coherentReduction reduction_tensor pullbackTensorIntegralAssociator
    unfold NatIso.ofComponents
    dsimp only [Functor.comp_map, ObjectProperty.ι_map, Functor.comp_obj,
      Functor.prod_obj, ObjectProperty.ι_obj]
    exact (pullbackTensorIntegralAssociator_existsUnique l E W M N P).exists.choose_spec

/-- The prescribed rational tensor associator is natural in all three arrows.
Source: Stacks 06YS, 07A4, 0941; the proved private calculations of
`CommonStageTensorLineCoherenceNaturality`.
(blueprint: lem-pur-rational-pullback-tensor-associator-natural).
Proof: coherent reduction reflects the integral associator square, because its
tensor comparison is natural and the system associator is natural. For rational
arrows, use the prescribed bilinear tensor formulas. On three pure scalar tensors
both sides are the localized integral square with the same product of scalars.
Tensor-product induction extends the equality to arbitrary arrows. -/
private theorem scalarAssoc_rationalAssociator_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    {K K' L L' M M' : sfRationalConstructibleCategory l E X}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') :
    (rationalDerivedTensor l E X).map
        (Prod.mkHom ((rationalDerivedTensor l E X).map (Prod.mkHom f g)) h) ≫
        (pullbackTensorRationalAssociator l E X K' L' M').hom =
      (pullbackTensorRationalAssociator l E X K L M).hom ≫
        (rationalDerivedTensor l E X).map
          (Prod.mkHom f ((rationalDerivedTensor l E X).map (Prod.mkHom g h))) := by
  let F := rationalDerivedTensor l E X
  have spec := scalarAssoc_chosen_spec (rationalDerivedTensor_existsUnique l E X) F rfl
  let I := constructibleIntegralTensor l E X
  let R := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  have ho (MN : sfRationalConstructibleCategory l E X ×
      sfRationalConstructibleCategory l E X) :
      F.obj MN = ScalarLocalization.mk (I.obj (MN.1.obj, MN.2.obj)) :=
    spec.1 MN
  let b (A A' B B' : sfRationalConstructibleCategory l E X) :
      (A ⟶ A') →ₗ[Localization.Away p] (B ⟶ B') →ₗ[Localization.Away p]
        (F.obj (A, B) ⟶ F.obj (A', B')) :=
    (spec.2 A A' B B').choose
  have hb (A A' B B' : sfRationalConstructibleCategory l E X)
      (f : A ⟶ A') (g : B ⟶ B') : F.map (Prod.mkHom f g) = b A A' B B' f g :=
    (spec.2 A A' B B').choose_spec.1 f g
  have hp (A A' B B' : sfRationalConstructibleCategory l E X)
      (f : A.obj ⟶ A'.obj) (g : B.obj ⟶ B'.obj) (a c : Localization.Away p) :
      HEq (F.map (Prod.mkHom (a ⊗ₜ[R] f) (c ⊗ₜ[R] g)))
        ((a * c) ⊗ₜ[R] I.map (Prod.mkHom f g)) := by
    rw [hb]
    exact (spec.2
      A A' B B').choose_spec.2 f g a c
  have hlobj (A B C : sfRationalConstructibleCategory l E X) :
      F.obj (F.obj (A, B), C) =
        ScalarLocalization.mk (I.obj (I.obj (A.obj, B.obj), C.obj)) := by
    rw [ho, ho]
  have hrobj (A B C : sfRationalConstructibleCategory l E X) :
      F.obj (A, F.obj (B, C)) =
        ScalarLocalization.mk (I.obj (A.obj, I.obj (B.obj, C.obj))) := by
    rw [ho, ho]
  change F.map (Prod.mkHom (F.map (Prod.mkHom f g)) h) ≫
      (pullbackTensorRationalAssociator l E X K' L' M').hom =
    (pullbackTensorRationalAssociator l E X K L M).hom ≫
      F.map (Prod.mkHom f (F.map (Prod.mkHom g h)))
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' =>
    simpa only [hb, map_add, LinearMap.add_apply, Preadditive.add_comp,
      Preadditive.comp_add] using congrArg₂ (· + ·) hf hf'
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' =>
      simpa only [hb, map_add, LinearMap.add_apply, Preadditive.add_comp,
        Preadditive.comp_add] using congrArg₂ (· + ·) hg hg'
    | tmul c g =>
      induction h using TensorProduct.inductionOn with
      | add h h' hh hh' =>
        simpa only [hb, map_add, LinearMap.add_apply, Preadditive.add_comp,
          Preadditive.comp_add] using congrArg₂ (· + ·) hh hh'
      | tmul d h =>
        have hfg := hp K K' L L' f g a c
        have hgh := hp L L' M M' g h c d
        have hleft := (scalarAssoc_tensor_map_heq F (ho (K, L)) (ho (K', L')) rfl rfl
          hfg HEq.rfl).trans
            (hp (ScalarLocalization.mk (I.obj (K.obj, L.obj)))
              (ScalarLocalization.mk (I.obj (K'.obj, L'.obj))) M M'
              (I.map (Prod.mkHom f g)) h (a * c) d)
        have hright := (scalarAssoc_tensor_map_heq F rfl rfl (ho (L, M)) (ho (L', M'))
          HEq.rfl hgh).trans
            (hp K K' (ScalarLocalization.mk (I.obj (L.obj, M.obj)))
              (ScalarLocalization.mk (I.obj (L'.obj, M'.obj)))
              f (I.map (Prod.mkHom g h)) a (c * d))
        have ha := (pullbackTensorRationalAssociator_existsUnique l E X K L M).exists.choose_spec
        have ha' :=
          (pullbackTensorRationalAssociator_existsUnique l E X K' L' M').exists.choose_spec
        have hl := heq_comp (hlobj K L M) (hlobj K' L' M') (hrobj K' L' M') hleft ha'
        have hr := heq_comp (hlobj K L M) (hrobj K L M) (hrobj K' L' M') ha hright
        apply eq_of_heq
        refine hl.trans ((heq_of_eq ?_).trans hr.symm)
        change ScalarLocalization.composition R _ p _ _ _
            (1 ⊗ₜ[R] (pullbackTensorIntegralAssociator l E X K'.obj L'.obj M'.obj).hom)
            (((a * c) * d) ⊗ₜ[R] I.map (Prod.mkHom (I.map (Prod.mkHom f g)) h)) =
          ScalarLocalization.composition R _ p _ _ _
            ((a * (c * d)) ⊗ₜ[R] I.map (Prod.mkHom f (I.map (Prod.mkHom g h))))
            (1 ⊗ₜ[R] (pullbackTensorIntegralAssociator l E X K.obj L.obj M.obj).hom)
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, mul_assoc]
        rw [scalarAssoc_integral_naturality l E X f g h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integral scalar extension carries the integral associator to the integral associator,
conjugated by the prescribed integral scalar tensor comparisons.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: apply coherent reduction. The
coherent scalar tensor normalization identifies the reduced tensor comparison with the
whole-system scalar tensorator, which is associative (`systemScalarTensorAssociativity`);
conclude with the reduced associativity calculation and faithfulness of coherent reduction. -/
theorem integralScalarAssociatorSquare
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι W).map (pullbackTensorIntegralAssociator l E W M N P).hom ≫
      (integralTensorScalarComparison l E L ι W M
        ((constructibleIntegralTensor l E W).obj (N, P))).hom ≫
      (constructibleIntegralTensor l L W).map
        (Prod.mkHom (𝟙 _) (integralTensorScalarComparison l E L ι W N P).hom) =
    (integralTensorScalarComparison l E L ι W
        ((constructibleIntegralTensor l E W).obj (M, N)) P).hom ≫
      (constructibleIntegralTensor l L W).map
        (Prod.mkHom (integralTensorScalarComparison l E L ι W M N).hom (𝟙 _)) ≫
      (pullbackTensorIntegralAssociator l L W
        ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι W).obj M)
        ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι W).obj N)
        ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
          E L ι W).obj P)).hom := by
  have := (coherentReduction_fullyFaithful l L W).2
  let F := sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
    E L ι W
  obtain ⟨p₀, hp₀⟩ := integralScalarTensorCoherentReduction l E L ι W
  let p : F ⋙ coherentReduction l L W ≅
      coherentReduction l E W ⋙ integralComparisonDerivedSequenceScalar l E L ι W := p₀
  have hspec (D : Type u) [Field D] [Algebra (Padic l) D] [FiniteDimensional (Padic l) D]
      (A B C : sfIntegralConstructibleCategory l D W) :
      (coherentReduction l D W).map (pullbackTensorIntegralAssociator l D W A B C).hom ≫
        (reduction_tensor l D W).hom.app (A, (constructibleIntegralTensor l D W).obj (B, C)) ≫
        (pullbackTensorCalculus l D W).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((reduction_tensor l D W).hom.app (B, C))) =
      (reduction_tensor l D W).hom.app ((constructibleIntegralTensor l D W).obj (A, B), C) ≫
        (pullbackTensorCalculus l D W).systemClosed.tensor.map
          (Prod.mkHom ((reduction_tensor l D W).hom.app (A, B)) (𝟙 _)) ≫
        ((pullbackTensorCalculus l D W).systemClosed.monoidal.associator
          ((coherentReduction l D W).obj A) ((coherentReduction l D W).obj B)
          ((coherentReduction l D W).obj C)).hom := by
    unfold coherentReduction reduction_tensor pullbackTensorIntegralAssociator
    unfold NatIso.ofComponents
    dsimp only [Functor.comp_map, ObjectProperty.ι_map, Functor.comp_obj,
      Functor.prod_obj, ObjectProperty.ι_obj]
    exact (pullbackTensorIntegralAssociator_existsUnique l D W A B C).exists.choose_spec
  exact reduced_associativity (coherentReduction l E W) (coherentReduction l L W) F
    (integralComparisonDerivedSequenceScalar l E L ι W)
    (constructibleIntegralTensor l E W) (constructibleIntegralTensor l L W)
    (pullbackTensorCalculus l E W).systemClosed.tensor
    (pullbackTensorCalculus l L W).systemClosed.tensor
    (reduction_tensor l E W) (reduction_tensor l L W) p
    (ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W))
    (integralTensorScalarComparison l E L ι W)
    (pullbackTensorIntegralAssociator l E W) (pullbackTensorIntegralAssociator l L W)
    (pullbackTensorCalculus l E W).systemClosed.monoidal.associator
    (pullbackTensorCalculus l L W).systemClosed.monoidal.associator
    (fun f g h ↦ @MonoidalCategory.associator_naturality _ _
      (pullbackTensorCalculus l L W).systemClosed.monoidal _ _ _ _ _ _ f g h)
    (hspec E) (hspec L) (fun A B ↦ hp₀ A B)
    (fun A B C ↦ systemScalarTensorAssociativity l E L ι W A B C) M N P

/-- Rational scalar extension carries the rational associator to the rational associator,
conjugated by the prescribed rational scalar tensor comparisons.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: every arrow is the
localization of the corresponding integral arrow; apply `integralScalarAssociatorSquare`. -/
theorem rationalScalarAssociatorSquare
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :
    (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        (pullbackTensorRationalAssociator l E W M N P).hom ≫
      (rationalTensorScalarComparison l E L ι W).hom.app
        (M, (rationalDerivedTensor l E W).obj (N, P)) ≫
      (rationalDerivedTensor l L W).map
        (Prod.mkHom (𝟙 _) ((rationalTensorScalarComparison l E L ι W).hom.app (N, P))) =
    (rationalTensorScalarComparison l E L ι W).hom.app
        ((rationalDerivedTensor l E W).obj (M, N), P) ≫
      (rationalDerivedTensor l L W).map
        (Prod.mkHom ((rationalTensorScalarComparison l E L ι W).hom.app (M, N)) (𝟙 _)) ≫
      (pullbackTensorRationalAssociator l L W
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)
        ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          P)).hom := by
  let S := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let Q := sfRationalConstructibleLocalization l L W
  let QE := sfRationalConstructibleLocalization l E W
  let U := constructibleIntegralTensor l E W
  let V := constructibleIntegralTensor l L W
  let μ := integralTensorScalarComparison l E L ι W
  have hG (K : sfRationalConstructibleCategory l E W) :
      (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K =
        Q.obj (S.obj K.obj) :=
    sfRationalScalarExtension_obj l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K
  have hTE (MN) :
      (rationalDerivedTensor l E W).obj MN = QE.obj (U.obj (MN.1.obj, MN.2.obj)) :=
    (scalarAssoc_chosen_spec (rationalDerivedTensor_existsUnique l E W)
      (rationalDerivedTensor l E W) rfl).1 MN
  have hTL (MN) :
      (rationalDerivedTensor l L W).obj MN = Q.obj (V.obj (MN.1.obj, MN.2.obj)) :=
    (scalarAssoc_chosen_spec (rationalDerivedTensor_existsUnique l L W)
      (rationalDerivedTensor l L W) rfl).1 MN
  have hc (A B : sfRationalConstructibleCategory l E W) :
      HEq ((rationalTensorScalarComparison l E L ι W).hom.app (A, B))
        (Q.map (μ A.obj B.obj).hom) :=
    scalarAssoc_chosen_spec (rationalTensorScalarComparison_existsUnique l E L ι W)
      (rationalTensorScalarComparison l E L ι W) rfl A B
  have hbase (K : sfRationalConstructibleCategory l E W) :
      ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
        K).obj = S.obj K.obj := by
    rw [hG]; rfl
  have hid (K : sfRationalConstructibleCategory l E W) :
      HEq (𝟙 ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
        L ι).obj K)) (Q.map (𝟙 (S.obj K.obj))) := by
    have hh {A : sfRationalConstructibleCategory l L W}
        {B : sfIntegralConstructibleCategory l L W} (h : A = Q.obj B) :
        HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
    exact hh (hG K)
  have htmap {A B C D : sfRationalConstructibleCategory l L W}
      {A' B' C' D' : sfIntegralConstructibleCategory l L W}
      (hA : A = Q.obj A') (hB : B = Q.obj B')
      (hC : C = Q.obj C') (hD : D = Q.obj D')
      (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
      (ha : HEq a (Q.map a')) (hb : HEq b (Q.map b')) :
      HEq ((rationalDerivedTensor l L W).map (Prod.mkHom a b))
        (Q.map (V.map (Prod.mkHom a' b'))) := by
    subst A B C D
    have ha' := eq_of_heq ha
    have hb' := eq_of_heq hb
    subst a b
    obtain ⟨bil, hbil, hbil'⟩ :=
      (scalarAssoc_chosen_spec (rationalDerivedTensor_existsUnique l L W)
        (rationalDerivedTensor l L W) rfl).2
        (Q.obj A') (Q.obj B') (Q.obj C') (Q.obj D')
    rw [hbil]
    convert hbil' a' b' 1 1 using 1
    simp only [one_mul]
    rfl
  have hmap {A B : sfRationalConstructibleCategory l E W}
      {A' B' : sfIntegralConstructibleCategory l E W}
      (hA : A = QE.obj A') (hB : B = QE.obj B')
      (a : A ⟶ B) (b : A' ⟶ B') (hab : HEq a (QE.map b)) :
      HEq ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        a) (Q.map (S.map b)) := by
    subst A B
    have hab' := eq_of_heq hab
    subst a
    have h := sfRationalScalarExtension_map_tmul l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι A' B' b 1
    have h1 :
        (sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E 1)) = 1 := by
      simp only [map_one]
    rw [h1] at h
    exact h
  have hμ {A A' B B' : sfIntegralConstructibleCategory l E W} (hA : A = A') (hB : B = B') :
      HEq (Q.map (μ A B).hom) (Q.map (μ A' B').hom) := by
    subst hA hB; rfl
  have hαL {A A' B B' C C' : sfIntegralConstructibleCategory l L W}
      (hA : A = A') (hB : B = B') (hC : C = C') :
      HEq (Q.map (pullbackTensorIntegralAssociator l L W A B C).hom)
        (Q.map (pullbackTensorIntegralAssociator l L W A' B' C').hom) := by
    subst hA hB hC; rfl
  have hTEobj (A B : sfRationalConstructibleCategory l E W) :
      ((rationalDerivedTensor l E W).obj (A, B)).obj = U.obj (A.obj, B.obj) := by rw [hTE]; rfl
  have h1 := hmap
    (A := (rationalDerivedTensor l E W).obj ((rationalDerivedTensor l E W).obj (M, N), P))
    (B := (rationalDerivedTensor l E W).obj (M, (rationalDerivedTensor l E W).obj (N, P)))
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl) _ _
    (pullbackTensorRationalAssociator_existsUnique l E W M N P).exists.choose_spec
  have h2 := (hc M ((rationalDerivedTensor l E W).obj (N, P))).trans (hμ rfl (hTEobj N P))
  have h3 := htmap (hG M) (hG M)
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl) (𝟙 _)
    ((rationalTensorScalarComparison l E L ι W).hom.app (N, P))
    (𝟙 _) (μ N.obj P.obj).hom (hid M) (hc N P)
  have h4 := (hc ((rationalDerivedTensor l E W).obj (M, N)) P).trans (hμ (hTEobj M N) rfl)
  have h5 := htmap
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
    (hG P) (hG P) ((rationalTensorScalarComparison l E L ι W).hom.app (M, N)) (𝟙 _)
    (μ M.obj N.obj).hom (𝟙 _) (hc M N) (hid P)
  have h6 := (pullbackTensorRationalAssociator_existsUnique l L W
    ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
    ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)
    ((sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
      P)).exists.choose_spec.trans (hαL (hbase M) (hbase N) (hbase P))
  have hl := heq_comp
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl) h1
    (heq_comp
      (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
      (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
      (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl) h2 h3)
  have hr := heq_comp
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
    (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl) h4
    (heq_comp
      (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
      (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl)
      (by simp only [Functor.comp_obj, Functor.prod_obj, hG, hTE, hTL]; rfl) h5 h6)
  apply eq_of_heq
  refine hl.trans ((heq_of_eq ?_).trans hr.symm)
  have h := congrArg Q.map (integralScalarAssociatorSquare l E L ι W M.obj N.obj P.obj)
  simp only [Functor.map_comp] at h
  exact h

end ScalarAssociator

section HigherCoherence
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- The left nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonLeft (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W
      (commonStageTensorObject l Ω W M N) P).stage ≤ L) :=
  commonStageTensorComparison l Ω W (commonStageTensorObject l Ω W M N) P L h ≪≫
    ((@rationalDerivedTensor l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
      hW)).mapIso
      (Iso.prod (commonStageTensorComparison l Ω W M N L (((Padic.finiteCoefficientFields_properties
        l Ω).1 (commonStageTensorObject l Ω W M N).stage P.stage).1.trans h)) (Iso.refl _))

/-- The right nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonRight (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W M
      (commonStageTensorObject l Ω W N P)).stage ≤ L) :=
  commonStageTensorComparison l Ω W M (commonStageTensorObject l Ω W N P) L h ≪≫
    ((@rationalDerivedTensor l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
      hW)).mapIso
      (Iso.prod (Iso.refl _) (commonStageTensorComparison l Ω W N P L
        (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage (commonStageTensorObject l Ω W N
        P).stage).2.trans h)))

section CommonAssociatorTransport

-- Transport an associator square along an equality of the scalar functor.
private theorem scalarAssoc_square_of_eq {A B : Type*} [Category* A] [Category* B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) {G G' : A ⥤ B} (hG : G' = G)
    (cG : TA ⋙ G ≅ G.prod G ⋙ TB) (c : TA ⋙ G' ≅ G'.prod G' ⋙ TB)
    (hc : c = Functor.isoWhiskerLeft TA (eqToIso hG) ≪≫ cG ≪≫
      Functor.isoWhiskerRight (NatIso.prod (eqToIso hG).symm (eqToIso hG).symm) TB)
    (αA : ∀ X Y Z, TA.obj (TA.obj (X, Y), Z) ≅ TA.obj (X, TA.obj (Y, Z)))
    (αB : ∀ X Y Z, TB.obj (TB.obj (X, Y), Z) ≅ TB.obj (X, TB.obj (Y, Z)))
    (h : ∀ X Y Z, G.map (αA X Y Z).hom ≫ cG.hom.app (X, TA.obj (Y, Z)) ≫
      TB.map (Prod.mkHom (𝟙 _) (cG.hom.app (Y, Z))) =
      cG.hom.app (TA.obj (X, Y), Z) ≫ TB.map (Prod.mkHom (cG.hom.app (X, Y)) (𝟙 _)) ≫
        (αB (G.obj X) (G.obj Y) (G.obj Z)).hom) (X Y Z : A) :
    G'.map (αA X Y Z).hom ≫ c.hom.app (X, TA.obj (Y, Z)) ≫
      TB.map (Prod.mkHom (𝟙 _) (c.hom.app (Y, Z))) =
    c.hom.app (TA.obj (X, Y), Z) ≫ TB.map (Prod.mkHom (c.hom.app (X, Y)) (𝟙 _)) ≫
      (αB (G'.obj X) (G'.obj Y) (G'.obj Z)).hom := by
  subst hG hc
  simpa [Functor.isoWhiskerLeft, Functor.isoWhiskerRight, NatTrans.prod] using h X Y Z

attribute [local semireducible] operationStageTransitionIso in
private theorem commonScalarAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
    (X Y Z : Stage l Ω W i) :
    ((stageSystem l Ω W).T h).map (pullbackTensorRationalAssociator l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W X Y Z).hom ≫
      (rationalTensorStageComparison l Ω W h).hom.app (X,
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W).obj
          (Y, Z)) ≫
      (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W).map
        (Prod.mkHom (𝟙 _) ((rationalTensorStageComparison l Ω W h).hom.app (Y, Z))) =
    (rationalTensorStageComparison l Ω W h).hom.app
        ((rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W).obj
          (X, Y), Z) ≫
      (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W).map
        (Prod.mkHom ((rationalTensorStageComparison l Ω W h).hom.app (X, Y)) (𝟙 _)) ≫
      (pullbackTensorRationalAssociator l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W
        (((stageSystem l Ω W).T h).obj X) (((stageSystem l Ω W).T h).obj Y)
        (((stageSystem l Ω W).T h).obj Z)).hom :=
  scalarAssoc_square_of_eq
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W)
    ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 i j h)
    (rationalTensorScalarComparison l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W)
    (rationalTensorStageComparison l Ω W h) rfl
    (pullbackTensorRationalAssociator l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
    (pullbackTensorRationalAssociator l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W)
    (fun X Y Z ↦ rationalScalarAssociatorSquare l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) W X Y Z) X Y Z

/-- Reassociate the two input corrections through the bifunctor. -/
private theorem scalarAssoc_tensorStageComparison_endpoint
    {C D : Type*} [Category* C] [Category* D]
    (F : C × C ⥤ C) (G : D × D ⥤ D) {T R : C ⥤ D} (e : T ≅ R)
    (c : F ⋙ R ≅ R.prod R ⋙ G) (X Y : C) {X' Y' : D}
    (a : T.obj X ≅ X') (b : T.obj Y ≅ Y') :
    ((Functor.isoWhiskerLeft F e ≪≫ c ≪≫
        Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) G).app (X, Y) ≪≫
      G.mapIso (Iso.prod a b)) =
    e.app (F.obj (X, Y)) ≪≫ c.app (X, Y) ≪≫
      G.mapIso (Iso.prod ((e.app X).symm ≪≫ a) ((e.app Y).symm ≪≫ b)) := by
  apply Iso.ext
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    NatIso.prod_hom, NatTrans.prod, Iso.prod_hom, Functor.mapIso_hom]
  simp only [Category.assoc, ← Functor.map_comp, prod_comp, Iso.prod_hom, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv]

attribute [local semireducible] operationStageTransitionIso commonStageTensorComparison in
/-- The common-stage tensor comparison is the descent endpoint of the stage comparisons. -/
private theorem scalarAssoc_commonStageTensorComparison_endpoint (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : (commonStageTensorObject l Ω W P Q).stage ≤ L) :
    (commonStageTensorComparison l Ω W P Q L h).hom =
      (stageEndpoint (stageSystem l Ω W)
        (fun i ↦ rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
        (fun h ↦ rationalTensorStageComparison l Ω W h)
        ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1
        ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2
        P.obj Q.obj h).hom := by
  have hh := scalarAssoc_tensorStageComparison_endpoint
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage)) W)
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W)
    (operationStageTransitionIso l Ω W _ L h)
    (rationalTensorScalarComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientCompositum l Ω P.stage Q.stage))
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω _ L h) W)
    (P.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1)
    (Q.toStage ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2)
    (((stageSystem l Ω W).assoc
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1 h).app P.obj)
    (((stageSystem l Ω W).assoc
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2 h).app Q.obj)
  have hh' := congrArg Iso.hom hh
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom] at hh'
  rw [show commonStageTensorComparison l Ω W P Q L h =
      (operationStageTransitionIso l Ω W _ L h).app (commonStageTensorObject l Ω W P Q).obj ≪≫
        _ ≪≫ _ from rfl]
  exact hh'.symm

/-- Cached stagewise tensor functors. -/
private abbrev caT (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    Stage l Ω W i × Stage l Ω W i ⥤ Stage l Ω W i :=
  rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W

/-- Cached stagewise tensor comparisons. -/
private abbrev cac (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    caT l Ω W i ⋙ (stageSystem l Ω W).T h ≅
      ((stageSystem l Ω W).T h).prod ((stageSystem l Ω W).T h) ⋙ caT l Ω W j :=
  rationalTensorStageComparison l Ω W h

/-- Cached stagewise associators. -/
private abbrev caα (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (i : AlgebraicallyClosedCoefficients.Index l Ω) (X Y Z : Stage l Ω W i) :
    (caT l Ω W i).obj ((caT l Ω W i).obj (X, Y), Z) ≅
      (caT l Ω W i).obj (X, (caT l Ω W i).obj (Y, Z)) :=
  pullbackTensorRationalAssociator l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
    W X Y Z

private theorem ca_tower (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    StageTensorTower (stageSystem l Ω W) (caT l Ω W) (fun h ↦ cac l Ω W h) :=
  fun h h' X Y ↦ rationalTensorStageComparison_coherent l Ω W h h' X Y

private theorem ca_hα (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ i {X X' Y Y' Z Z' : Stage l Ω W i} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
      (caT l Ω W i).map (Prod.mkHom ((caT l Ω W i).map (Prod.mkHom f g)) h) ≫
          (caα l Ω W i X' Y' Z').hom =
        (caα l Ω W i X Y Z).hom ≫ (caT l Ω W i).map (Prod.mkHom f
          ((caT l Ω W i).map (Prod.mkHom g h))) :=
  fun i _ _ _ _ _ _ f g h ↦ scalarAssoc_rationalAssociator_natural l _ W f g h

private theorem ca_hAS (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j)
      (X Y Z : Stage l Ω W i),
      ((stageSystem l Ω W).T h).map (caα l Ω W i X Y Z).hom ≫
        (cac l Ω W h).hom.app (X, (caT l Ω W i).obj (Y, Z)) ≫
        (caT l Ω W j).map (Prod.mkHom (𝟙 _) ((cac l Ω W h).hom.app (Y, Z))) =
      (cac l Ω W h).hom.app ((caT l Ω W i).obj (X, Y), Z) ≫
        (caT l Ω W j).map (Prod.mkHom ((cac l Ω W h).hom.app (X, Y)) (𝟙 _)) ≫
        (caα l Ω W j (((stageSystem l Ω W).T h).obj X) (((stageSystem l Ω W).T h).obj Y)
          (((stageSystem l Ω W).T h).obj Z)).hom :=
  fun h X Y Z ↦ commonScalarAssociator l Ω W h X Y Z

-- assembling the common-stage associator unfolds long composites of stage comparisons
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackTensorCommonAssociator_exists_aux (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃ e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv)) := by
  classical
  let S := stageSystem l Ω W
  let MN := commonStageTensorObject l Ω W M N
  let NP := commonStageTensorObject l Ω W N P
  let A := commonStageTensorObject l Ω W MN P
  let B := commonStageTensorObject l Ω W M NP
  have h₁ := ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1
  have h₂ := ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2
  have g₁ := ((Padic.finiteCoefficientFields_properties l Ω).1 MN.stage P.stage).1
  have g₃ := ((Padic.finiteCoefficientFields_properties l Ω).1 MN.stage P.stage).2
  have f₂ := ((Padic.finiteCoefficientFields_properties l Ω).1 N.stage P.stage).1
  have f₃ := ((Padic.finiteCoefficientFields_properties l Ω).1 N.stage P.stage).2
  have f₁ := ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage NP.stage).1
  have e₁ := ((Padic.finiteCoefficientFields_properties l Ω).1 M.stage NP.stage).2
  obtain ⟨d, hd⟩ := pairCategory_exists_iso_of_tr₂ S (A := A) (B := B)
    (fun hS hT ↦ stageAssociatorRep S (caT l Ω W) (fun h ↦ cac l Ω W h) (caα l Ω W)
      h₁ h₂ g₁ g₃ f₂ f₃ f₁ e₁ M.obj N.obj P.obj hS hT)
    (fun hS hT k ↦ stageAssociatorRep_tr S (caT l Ω W) (fun h ↦ cac l Ω W h)
      (ca_tower l Ω W) (caα l Ω W) (ca_hα l Ω W) (ca_hAS l Ω W) h₁ h₂ g₁ g₃ f₂ f₃ f₁ e₁
      M.obj N.obj P.obj hS hT k)
  have hTc := scalarAssoc_chosen_spec (commonStageDerivedTensor_existsUnique l Ω W)
    (commonStageDerivedTensor l Ω W) (by unfold commonStageDerivedTensor; rfl)
  have hT1 : (commonStageDerivedTensor l Ω W).obj
      ((commonStageDerivedTensor l Ω W).obj (M, N), P) = A := by
    rw [hTc.1 M N, hTc.1]
  have hT2 : (commonStageDerivedTensor l Ω W).obj
      (M, (commonStageDerivedTensor l Ω W).obj (N, P)) = B := by
    rw [hTc.1 N P, hTc.1]
  have hL (L : AlgebraicallyClosedCoefficients.Index l Ω) (hS : A.stage ≤ L) :
      (pullbackTensorCommonLeft l Ω W M N P L hS).hom =
        (stageLeftNested S (caT l Ω W) (fun h ↦ cac l Ω W h) h₁ h₂ g₁ g₃
          M.obj N.obj P.obj hS).hom := by
    have e₂ := scalarAssoc_commonStageTensorComparison_endpoint l Ω W MN P L hS
    have e₁ := scalarAssoc_commonStageTensorComparison_endpoint l Ω W M N L (g₁.trans hS)
    unfold pullbackTensorCommonLeft
    exact congrArg₂ (fun a b ↦ a ≫ (rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W).map (Prod.mkHom b (𝟙 _))) e₂ e₁
  have hR (L : AlgebraicallyClosedCoefficients.Index l Ω) (hT : B.stage ≤ L) :
      (pullbackTensorCommonRight l Ω W M N P L hT).hom =
        (stageRightNested S (caT l Ω W) (fun h ↦ cac l Ω W h) f₂ f₃ f₁ e₁
          M.obj N.obj P.obj hT).hom := by
    have e₂ := scalarAssoc_commonStageTensorComparison_endpoint l Ω W M NP L hT
    have e₁ := scalarAssoc_commonStageTensorComparison_endpoint l Ω W N P L (e₁.trans hT)
    unfold pullbackTensorCommonRight
    exact congrArg₂ (fun a b ↦ a ≫ (rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W).map (Prod.mkHom (𝟙 _) b)) e₂ e₁
  refine ⟨eqToIso hT1 ≪≫ d ≪≫ eqToIso hT2.symm, fun L hS hT ↦ ?_⟩
  rw [Iso.trans_hom, Iso.trans_hom, eqToIso.hom, eqToIso.hom, hd L hS hT]
  refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans (heq_of_eq ?_))
  dsimp only [GeneralAlgebraicallyClosedCoefficients.ofHom]
  apply congrArg (StageSystem.PairCategory.mkHom (X := A) (Y := B) L hS hT)
  have hR' := congrArg Iso.inv (Iso.ext (hR L hT))
  exact (congrArg₂ (fun a b ↦ a ≫ (caα l Ω W L _ _ _).hom ≫ b) (hL L hS) hR').symm

end CommonAssociatorTransport

attribute [local irreducible] pullbackTensorCommonLeft pullbackTensorCommonRight

/-- Existence half of the normalized constraint; uniqueness is proved by the parent theorem.
Source: Stacks 06YS, 07A4, 0941.
(blueprint: lem-pur-derived-pullback-tensor-constraints-common-associator-existence). -/
theorem pullbackTensorCommonAssociator_exists (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃ e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv)) := by
  exact pullbackTensorCommonAssociator_exists_aux l Ω W M N P

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The common-stage associator has its prescribed representative at every larger field.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Conjugate the rational associator
by the
  displayed transition/tensor comparisons. Their scalar-extension cocycles show independence of
  enlargement. The inverse formula gives an inverse class. Directedness supplies common stages, and
  a representative determines its colimit hom class uniquely. -/
theorem pullbackTensorCommonAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv)) := by
  obtain ⟨e, he⟩ := pullbackTensorCommonAssociator_exists l Ω W M N P
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  let S := commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P
  let T := commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)
  let L := Padic.finiteCoefficientCompositum l Ω S.stage T.stage
  let hS := ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage T.stage).1
  let hT := ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage T.stage).2
  exact eq_of_heq ((hd L hS hT).trans (he L hS hT).symm)

/-- The stage-independent rational associator class.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonAssociator_existsUnique l _ Ω _ _ _ W hW) M N P).exists.choose

attribute [local irreducible] pullbackTensorCommonAssociator

end HigherCoherence

end WeilConjectures

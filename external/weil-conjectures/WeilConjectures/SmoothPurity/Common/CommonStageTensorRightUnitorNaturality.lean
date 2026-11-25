/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful

/-! # Naturality of the prescribed common-stage right unitor

Source: Stacks Project, Tags 07A4 and 0941; coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-right-unitor-natural).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  commonStageTensorObject

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence commonStageTensorComparison
  operationStageTransitionIso

private theorem chosen_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private theorem counit_model_naturality
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (R : D ⥤ T) (L : T ⥤ D) (adj : R ⊣ L) (F : C ⥤ D) (H : C ⥤ T)
    (a : F ≅ H ⋙ L) {M N : C} (f : M ⟶ N) :
    R.map (F.map f) ≫ R.map (a.hom.app N) ≫ adj.counit.app (H.obj N) =
      R.map (a.hom.app M) ≫ adj.counit.app (H.obj M) ≫ H.map f := by
  rw [← R.map_comp_assoc, a.hom.naturality, R.map_comp]
  simp only [Functor.comp_map, Category.assoc]
  exact congrArg (fun k ↦ R.map (a.hom.app M) ≫ k)
    (adj.counit.naturality (H.map f))

private theorem tensor_unit_square {C : Type*} [Category* C]
    (T : C × C ⥤ C) {U V : C} (e : V ⟶ U)
    (r : ∀ M, T.obj (M, U) ⟶ M)
    (hr : ∀ {M N} (f : M ⟶ N), T.map (Prod.mkHom f (𝟙 U)) ≫ r N = r M ≫ f)
    {M N : C} (f : M ⟶ N) :
    T.map (Prod.mkHom f (𝟙 V)) ≫ T.map (Prod.mkHom (𝟙 N) e) ≫ r N =
      T.map (Prod.mkHom (𝟙 M) e) ≫ r M ≫ f := by
  have h : Prod.mkHom f (𝟙 V) ≫ Prod.mkHom (𝟙 N) e =
      Prod.mkHom (𝟙 M) e ≫ Prod.mkHom f (𝟙 U) := by
    ext <;> simp
  rw [← T.map_comp_assoc, h, T.map_comp, Category.assoc, hr]

private theorem naturality_of_reduction
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (T : C × C ⥤ C) (R : C ⥤ D) [R.Faithful]
    (a : T ⋙ R ≅ R.prod R ⋙ MonoidalCategory.tensor D)
    (U : C) (e : R.obj U ≅ MonoidalCategoryStruct.tensorUnit D)
    (r : ∀ M, T.obj (M, U) ≅ M)
    (h : ∀ M, R.map (r M).hom = a.hom.app (M, U) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom (𝟙 _) e.hom) ≫
      (MonoidalCategoryStruct.rightUnitor (R.obj M)).hom)
    {M N : C} (f : M ⟶ N) :
    T.map (Prod.mkHom f (𝟙 U)) ≫ (r N).hom = (r M).hom ≫ f := by
  apply R.map_injective
  rw [Functor.map_comp, Functor.map_comp, h, h]
  have hn := a.hom.naturality (Prod.mkHom f (𝟙 U))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  apply congrArg (fun z ↦ a.hom.app (M, U) ≫ z)
  rw [R.map_id]
  apply tensor_unit_square (MonoidalCategory.tensor D) e.hom
    (fun M ↦ (MonoidalCategoryStruct.rightUnitor M).hom)
  intro M N g
  simpa only [MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id] using
    MonoidalCategory.rightUnitor_naturality g

section Integral
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]

private abbrev coherentReduction :
    sfIntegralConstructibleCategory l E X ⥤ coefficientSequenceDerived l E X :=
  (sfIntegralConstructible l E X).ι ⋙ (pullbackTensorCalculus l E X).reduction

private def reductionTensor :
    constructibleIntegralTensor l E X ⋙ coherentReduction l E X ≅
      (coherentReduction l E X).prod (coherentReduction l E X) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor :=
  NatIso.ofComponents (fun MN ↦ pullbackTensorIntegralReductionTensor l E X MN.1 MN.2) (by
    intro MN PQ k
    have hn := counit_model_naturality
      (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
      (pullbackTensorCalculus l E X).adjunction (integralCompletedTensor l E X)
      (((pullbackTensorCalculus l E X).reduction.prod
        (pullbackTensorCalculus l E X).reduction) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor)
      (pullbackTensorIntegralTensorModel l E X) (Prod.mkHom k.1.hom k.2.hom)
    exact hn.trans (Category.assoc _ _ _).symm)

private theorem integral_naturality {M N : sfIntegralConstructibleCategory l E X}
    (f : M ⟶ N) :
    (constructibleIntegralTensor l E X).map (Prod.mkHom f (𝟙 _)) ≫
        (pullbackTensorIntegralRightUnitor l E X N).hom =
      (pullbackTensorIntegralRightUnitor l E X M).hom ≫ f := by
  have : (coherentReduction l E X).Faithful := by
    have h := (integralSystemReduction_fullyFaithful l E X).2
    change (coherentReduction l E X).Faithful at h
    exact h
  let S := (pullbackTensorCalculus l E X).systemClosed
  let := S.monoidal
  exact naturality_of_reduction (constructibleIntegralTensor l E X)
    (coherentReduction l E X) (reductionTensor l E X)
    (pullbackTensorIntegralUnit l E X) (pullbackTensorIntegralUnitReduction l E X)
    (fun M ↦ pullbackTensorIntegralRightUnitor l E X M)
    (fun M ↦ (pullbackTensorIntegralRightUnitor_existsUnique l E X M).exists.choose_spec) f

private theorem rational_naturality {M N : sfRationalConstructibleCategory l E X}
    (f : M ⟶ N) :
    (rationalDerivedTensor l E X).map (Prod.mkHom f (𝟙 _)) ≫
        (pullbackTensorRationalRightUnitor l E X N).hom =
      (pullbackTensorRationalRightUnitor l E X M).hom ≫ f := by
  let U := pullbackTensorRationalUnit l E X
  let T := rationalDerivedTensor l E X
  have hT := chosen_spec (rationalDerivedTensor_existsUnique l E X) T rfl
  obtain ⟨b, hb, hpure⟩ := hT.2 M N U U
  have hM := chosen_spec (pullbackTensorRationalRightUnitor_existsUnique l E X M)
    (pullbackTensorRationalRightUnitor l E X M) rfl
  have hN := chosen_spec (pullbackTensorRationalRightUnitor_existsUnique l E X N)
    (pullbackTensorRationalRightUnitor l E X N) rfl
  change T.map (Prod.mkHom f (𝟙 U)) ≫ _ = _
  induction f using TensorProduct.inductionOn with
  | tmul c f =>
    have hm : HEq (T.map (Prod.mkHom
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) (𝟙 U)))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralTensor l E X).map (Prod.mkHom f (𝟙 U.obj))) := by
      rw [hb]
      change HEq (b (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)
        (1 ⊗ₜ[Padic.coefficientExtensionIntegers l E] 𝟙 U.obj)) _
      simpa only [mul_one] using hpure f (𝟙 U.obj) c 1
    have hleft := heq_comp (hT.1 (M, U)) (hT.1 (N, U)) rfl hm hN
    have hright := heq_comp (hT.1 (M, U)) rfl rfl hM
      (HEq.rfl : HEq (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ[_] (pullbackTensorIntegralRightUnitor l E X N.obj).hom)
        (c ⊗ₜ[_] (constructibleIntegralTensor l E X).map (Prod.mkHom f (𝟙 U.obj))) =
      ScalarLocalization.composition _ _ _ _ _ _
        (c ⊗ₜ[_] f) (1 ⊗ₜ[_] (pullbackTensorIntegralRightUnitor l E X M.obj).hom)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun z ↦ c ⊗ₜ[Padic.coefficientExtensionIntegers l E] z)
      (integral_naturality l E X f)
  | add f g hf hg =>
    simp only [hb, map_add, LinearMap.add_apply, Preadditive.add_comp] at hf hg ⊢
    rw [hf, hg]
    exact (Preadditive.comp_add (C := sfRationalConstructibleCategory l E X) _ _ _
      (pullbackTensorRationalRightUnitor l E X M).hom (f : M ⟶ N) (g : M ⟶ N)).symm

end Integral

-- Compare the cached category instances rather than unfolding their Hom data.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
  Linear.homModule Preadditive.homGroup

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local irreducible] Padic.coefficientExtensionIntegers
  ScalarLocalization.composition pullbackTensorCommonUnit pullbackTensorRationalUnit

attribute [local irreducible] commonStageDerivedTensor rationalDerivedTensor
  pullbackTensorCommonUnitStage pullbackTensorRationalRightUnitor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the canonical right unitor for the reconstructed common-stage unit.

Source: Stacks Project, Tags 07A4 and 0941; coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-right-unitor-natural).

Proof: apply faithful coherent reduction to the integral square and substitute
its normalized tensor and unit comparisons. The resulting square is precisely
right-unitor naturality in the coherent system monoidal category. Localizing
the integral equality proves the rational square on pure scalar tensors;
bilinearity extends it to all rational maps. Choose a common finite coefficient
stage for the source, target and a representative of the given arrow. The
common-stage unitor and tensor representative formulas conjugate the square
to the rational square: functoriality moves the unit comparison past the
first-variable arrow, and inverse tensor comparisons cancel. The rational square
commutes, so the two representatives agree at that stage and give equal
common-stage morphisms. The argument also applies to the zero arrow and to
identity arrows. -/
theorem commonStageTensorRightUnitor_naturality
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {K K' : generalAlgebraicallyClosedConstructibleCategory l Ω X} (f : K ⟶ K') :
    (commonStageDerivedTensor l Ω X).map (Prod.mkHom f (𝟙 _)) ≫
        (pullbackTensorCommonRightUnitor l Ω X K').hom =
      (pullbackTensorCommonRightUnitor l Ω X K).hom ≫ f := by
  classical
  let U := pullbackTensorCommonUnit l Ω X
  let A := commonStageTensorObject l Ω X K U
  let B := commonStageTensorObject l Ω X K' U
  let P := Padic.finiteCoefficientCompositum l Ω A.stage B.stage
  obtain ⟨L, hL, hK, hK', a, rfl⟩ :=
    StageSystem.PairCategory.exists_le_mkHom_eq f P
  have hA : A.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans hL
  have hB : B.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans hL
  have hU : U.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 K.stage U.stage).2.trans hA
  have hT := chosen_spec (commonStageDerivedTensor_existsUnique l Ω X)
    (commonStageDerivedTensor l Ω X) (by unfold commonStageDerivedTensor; rfl)
  have hM := chosen_spec (pullbackTensorCommonRightUnitor_existsUnique l Ω X K)
    (pullbackTensorCommonRightUnitor l Ω X K) rfl L hA
  have hN := chosen_spec (pullbackTensorCommonRightUnitor_existsUnique l Ω X K')
    (pullbackTensorCommonRightUnitor l Ω X K') rfl L hB
  have ht := hT.2 K U K' U L hA hB a (𝟙 (U.toStage hU))
  have hid : GeneralAlgebraicallyClosedCoefficients.ofHom U U L hU hU (𝟙 _) = 𝟙 U :=
    (StageSystem.PairCategory.id_eq_mkHom U hU).symm
  rw [hid] at ht
  have hleft := heq_comp (hT.1 K U) (hT.1 K' U) rfl ht hN
  have hright := heq_comp (hT.1 K U) rfl rfl hM
    (HEq.rfl : HEq (GeneralAlgebraicallyClosedCoefficients.ofHom K K' L hK hK' a)
      (GeneralAlgebraicallyClosedCoefficients.ofHom K K' L hK hK' a))
  apply eq_of_heq
  refine hleft.trans (HEq.trans ?_ hright.symm)
  apply heq_of_eq
  dsimp only [GeneralAlgebraicallyClosedCoefficients.ofHom]
  rw [StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom (X := A) (Y := K') L hA hK')
  dsimp only [U, A, B]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply congrArg (fun z ↦ (commonStageTensorComparison l Ω X K U L hA).hom ≫ z)
  exact tensor_unit_square
    (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
    (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
    (U := pullbackTensorRationalUnit l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
    (V := U.toStage hU)
    (pullbackTensorCommonUnitStage l Ω X L hU).hom
    (fun M ↦ (pullbackTensorRationalRightUnitor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X M).hom)
    (fun f ↦ rational_naturality l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X f) a

end WeilConjectures

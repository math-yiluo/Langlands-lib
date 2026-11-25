/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Rational.RationalPullbackTensorAssociatorNaturality

/-! # Triangle identity for common-stage tensor

Source: Stacks Project, Tags 07A4 and 0941; the coefficient-stage conventions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

private theorem tensor_comp {C : Type*} [Category* C] (T : C × C ⥤ C)
    {A B C₀ D E F : C} (f : A ⟶ B) (g : B ⟶ C₀) (h : D ⟶ E) (k : E ⟶ F) :
    T.map (Prod.mkHom f h) ≫ T.map (Prod.mkHom g k) =
      T.map (Prod.mkHom (f ≫ g) (h ≫ k)) := by
  rw [← T.map_comp]
  rfl

private theorem triangle_change_unit {C : Type*} [Category* C]
    (T : C × C ⥤ C)
    (a : ∀ A B D, T.obj (T.obj (A, B), D) ≅ T.obj (A, T.obj (B, D)))
    (U V : C) (e : V ⟶ U) (lu : ∀ A, T.obj (U, A) ⟶ A)
    (ru : ∀ A, T.obj (A, U) ⟶ A)
    (hn : ∀ A B,
      T.map (Prod.mkHom (T.map (Prod.mkHom (𝟙 A) e)) (𝟙 B)) ≫ (a A U B).hom =
        (a A V B).hom ≫ T.map (Prod.mkHom (𝟙 A) (T.map (Prod.mkHom e (𝟙 B)))))
    (ht : ∀ A B, (a A U B).hom ≫ T.map (Prod.mkHom (𝟙 A) (lu B)) =
      T.map (Prod.mkHom (ru A) (𝟙 B))) (A B : C) :
    (a A V B).hom ≫ T.map (Prod.mkHom (𝟙 A)
        (T.map (Prod.mkHom e (𝟙 B)) ≫ lu B)) =
      T.map (Prod.mkHom (T.map (Prod.mkHom (𝟙 A) e) ≫ ru A) (𝟙 B)) := by
  have h := congrArg (fun z ↦ z ≫ T.map (Prod.mkHom (𝟙 A) (lu B))) (hn A B)
  simp only [Category.assoc, ht, tensor_comp, Category.comp_id] at h
  exact h.symm

private theorem faithful_triangle {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory D] (R : C ⥤ D) [R.Faithful] (T : C × C ⥤ C)
    (b : T ⋙ R ≅ R.prod R ⋙ MonoidalCategory.tensor D)
    (U : C) (e : R.obj U ≅ MonoidalCategoryStruct.tensorUnit D)
    (a : ∀ A B C₀, T.obj (T.obj (A, B), C₀) ≅ T.obj (A, T.obj (B, C₀)))
    (lu : ∀ A, T.obj (U, A) ≅ A) (ru : ∀ A, T.obj (A, U) ≅ A)
    (ha : ∀ A B C₀, R.map (a A B C₀).hom ≫ b.hom.app (A, T.obj (B, C₀)) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom (𝟙 _) (b.hom.app (B, C₀))) =
        b.hom.app (T.obj (A, B), C₀) ≫
          (MonoidalCategory.tensor D).map (Prod.mkHom (b.hom.app (A, B)) (𝟙 _)) ≫
          (MonoidalCategoryStruct.associator (R.obj A) (R.obj B) (R.obj C₀)).hom)
    (hl : ∀ A, R.map (lu A).hom = b.hom.app (U, A) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom e.hom (𝟙 _)) ≫
        (MonoidalCategoryStruct.leftUnitor (R.obj A)).hom)
    (hr : ∀ A, R.map (ru A).hom = b.hom.app (A, U) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom (𝟙 _) e.hom) ≫
        (MonoidalCategoryStruct.rightUnitor (R.obj A)).hom)
    (A B : C) :
    (a A U B).hom ≫ T.map (Prod.mkHom (𝟙 A) (lu B).hom) =
      T.map (Prod.mkHom (ru A).hom (𝟙 B)) := by
  let S := MonoidalCategory.tensor D
  have hn (P Q : C × C) (f : P ⟶ Q) :
      R.map (T.map f) ≫ b.hom.app Q =
        b.hom.app P ≫ S.map (Prod.mkHom (R.map f.1) (R.map f.2)) :=
    b.hom.naturality f
  have ht := triangle_change_unit S MonoidalCategoryStruct.associator
    (MonoidalCategoryStruct.tensorUnit D) (R.obj U) e.hom
    (fun M ↦ (MonoidalCategoryStruct.leftUnitor M).hom)
    (fun M ↦ (MonoidalCategoryStruct.rightUnitor M).hom)
    (fun M N ↦ MonoidalCategory.associator_naturality (𝟙 M) e.hom (𝟙 N))
    (fun M N ↦ by
      simpa only [S, MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
        MonoidalCategory.id_tensorHom] using MonoidalCategory.triangle M N) (R.obj A) (R.obj B)
  apply R.map_injective
  apply (cancel_mono (b.hom.app (A, B))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, hn]
  simp only [R.map_id, hl, hr]
  have hh := ha A U B
  -- Factor the tensor of the reduced left unitor, then apply associator compatibility.
  have hfac : S.map (Prod.mkHom (𝟙 (R.obj A))
      (b.hom.app (U, B) ≫ S.map (Prod.mkHom e.hom (𝟙 (R.obj B))) ≫
        (MonoidalCategoryStruct.leftUnitor (R.obj B)).hom)) =
      S.map (Prod.mkHom (𝟙 (R.obj A)) (b.hom.app (U, B))) ≫
        S.map (Prod.mkHom (𝟙 (R.obj A))
          (S.map (Prod.mkHom e.hom (𝟙 (R.obj B))) ≫
            (MonoidalCategoryStruct.leftUnitor (R.obj B)).hom)) := by
    rw [tensor_comp, Category.id_comp]
  rw [hfac]
  rw [reassoc_of% hh, ht, tensor_comp]
  simp only [Category.comp_id]
  rfl

section IntegralTriangle
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]

private theorem integral_triangle (A B : sfIntegralConstructibleCategory l E X) :
    (pullbackTensorIntegralAssociator l E X A (pullbackTensorIntegralUnit l E X) B).hom ≫
        (constructibleIntegralTensor l E X).map
          (Prod.mkHom (𝟙 A) (pullbackTensorIntegralLeftUnitor l E X B).hom) =
      (constructibleIntegralTensor l E X).map
        (Prod.mkHom (pullbackTensorIntegralRightUnitor l E X A).hom (𝟙 B)) := by
  have := (coherentReduction_fullyFaithful l E X).2
  let S := (pullbackTensorCalculus l E X).systemClosed
  let := S.monoidal
  apply faithful_triangle (coherentReduction l E X) (constructibleIntegralTensor l E X)
    (reduction_tensor l E X) (pullbackTensorIntegralUnit l E X)
    (pullbackTensorIntegralUnitReduction l E X) (pullbackTensorIntegralAssociator l E X)
    (pullbackTensorIntegralLeftUnitor l E X) (pullbackTensorIntegralRightUnitor l E X)
  · intro M N P
    exact (pullbackTensorIntegralAssociator_existsUnique l E X M N P).exists.choose_spec
  · intro M
    exact (pullbackTensorIntegralLeftUnitor_existsUnique l E X M).exists.choose_spec
  · intro M
    exact (pullbackTensorIntegralRightUnitor_existsUnique l E X M).exists.choose_spec

section LocalizationElaboration
set_option allowUnsafeReducibility true in
attribute [local reducible] ScalarLocalization.category

private theorem localized_tensor_map
    {A B C D : sfRationalConstructibleCategory l E X}
    {A' B' C' D' : sfIntegralConstructibleCategory l E X}
    (hA : A = (sfRationalConstructibleLocalization l E X).obj A')
    (hB : B = (sfRationalConstructibleLocalization l E X).obj B')
    (hC : C = (sfRationalConstructibleLocalization l E X).obj C')
    (hD : D = (sfRationalConstructibleLocalization l E X).obj D')
    (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
    (ha : HEq a ((sfRationalConstructibleLocalization l E X).map a'))
    (hb : HEq b ((sfRationalConstructibleLocalization l E X).map b')) :
    HEq ((rationalDerivedTensor l E X).map (Prod.mkHom a b))
      ((sfRationalConstructibleLocalization l E X).map
        ((constructibleIntegralTensor l E X).map (Prod.mkHom a' b'))) := by
  subst A B C D
  have ha' := eq_of_heq ha
  have hb' := eq_of_heq hb
  subst a b
  obtain ⟨bil, hbil, hpure⟩ :=
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.2
      ((sfRationalConstructibleLocalization l E X).obj A')
      ((sfRationalConstructibleLocalization l E X).obj B')
      ((sfRationalConstructibleLocalization l E X).obj C')
      ((sfRationalConstructibleLocalization l E X).obj D')
  change HEq ((rationalDerivedTensor_existsUnique l E X).exists.choose.map
    (Prod.mkHom ((sfRationalConstructibleLocalization l E X).map a')
      ((sfRationalConstructibleLocalization l E X).map b'))) _
  rw [hbil]
  refine (hpure a' b' 1 1).trans ?_
  simp only [one_mul]
  rfl

end LocalizationElaboration

private theorem rational_triangle (A B : sfRationalConstructibleCategory l E X) :
    (pullbackTensorRationalAssociator l E X A (pullbackTensorRationalUnit l E X) B).hom ≫
        (rationalDerivedTensor l E X).map
          (Prod.mkHom (𝟙 A) (pullbackTensorRationalLeftUnitor l E X B).hom) =
      (rationalDerivedTensor l E X).map
        (Prod.mkHom (pullbackTensorRationalRightUnitor l E X A).hom (𝟙 B)) := by
  let Q := sfRationalConstructibleLocalization l E X
  let I := constructibleIntegralTensor l E X
  let T := rationalDerivedTensor l E X
  let U := pullbackTensorRationalUnit l E X
  let V := pullbackTensorIntegralUnit l E X
  have ho (MN) : T.obj MN = Q.obj (I.obj (MN.1.obj, MN.2.obj)) :=
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 MN
  have ha := (pullbackTensorRationalAssociator_existsUnique l E X A U B).exists.choose_spec
  have hl := (pullbackTensorRationalLeftUnitor_existsUnique l E X B).exists.choose_spec
  have hr := (pullbackTensorRationalRightUnitor_existsUnique l E X A).exists.choose_spec
  have hid (M : sfRationalConstructibleCategory l E X) :
      HEq (𝟙 M) (Q.map (𝟙 M.obj)) := by
    cases M
    simp [Q, sfRationalConstructibleLocalization, ScalarLocalization.localization]
  have hleft := localized_tensor_map l E X rfl rfl (ho (U, B)) rfl
    (𝟙 A) (pullbackTensorRationalLeftUnitor l E X B).hom
    (𝟙 A.obj) (pullbackTensorIntegralLeftUnitor l E X B.obj).hom (hid A) hl
  have hright := localized_tensor_map l E X (ho (A, U)) rfl rfl rfl
    (pullbackTensorRationalRightUnitor l E X A).hom (𝟙 B)
    (pullbackTensorIntegralRightUnitor l E X A.obj).hom (𝟙 B.obj) hr (hid B)
  have hh := heq_comp (by rw [ho, ho]; rfl) (by rw [ho, ho]; rfl) (ho (A, B)) ha hleft
  apply eq_of_heq
  refine hh.trans ((heq_of_eq ?_).trans hright.symm)
  rw [← Q.map_comp]
  change Q.map ((pullbackTensorIntegralAssociator l E X A.obj V B.obj).hom ≫
    I.map (Prod.mkHom (𝟙 A.obj) (pullbackTensorIntegralLeftUnitor l E X B.obj).hom)) = _
  exact congrArg Q.map (integral_triangle l E X A.obj B.obj)

end IntegralTriangle

private theorem tensor_map_heq {C : Type*} [Category* C] (T : C × C ⥤ C)
    {A B D E A' B' D' E' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : D ⟶ E} {g' : D' ⟶ E'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (T.map (Prod.mkHom f g)) (T.map (Prod.mkHom f' g')) := by
  subst A' B' D' E'
  cases hf
  cases hg
  rfl

private theorem conjugated_triangle {C : Type*} [Category* C] (T : C × C ⥤ C)
    {A B U V W S R O : C} (e : U ⟶ V)
    (i : W ≅ T.obj (A, U)) {Z : C} (j : Z ≅ T.obj (U, B))
    (s : S ≅ T.obj (W, B)) (t : R ≅ T.obj (A, Z)) (o : O ≅ T.obj (A, B))
    (a : T.obj (T.obj (A, U), B) ⟶ T.obj (A, T.obj (U, B)))
    (lu : T.obj (V, B) ⟶ B) (ru : T.obj (A, V) ⟶ A)
    (ht : a ≫ T.map (Prod.mkHom (𝟙 A) (T.map (Prod.mkHom e (𝟙 B)) ≫ lu)) =
      T.map (Prod.mkHom (T.map (Prod.mkHom (𝟙 A) e) ≫ ru) (𝟙 B))) :
    ((s ≪≫ T.mapIso (Iso.prod i (Iso.refl B))).hom ≫ a ≫
        (t ≪≫ T.mapIso (Iso.prod (Iso.refl A) j)).inv) ≫
        (t.hom ≫ T.map (Prod.mkHom (𝟙 A)
          (j.hom ≫ T.map (Prod.mkHom e (𝟙 B)) ≫ lu)) ≫ o.inv) =
      s.hom ≫ T.map (Prod.mkHom
        (i.hom ≫ T.map (Prod.mkHom (𝟙 A) e) ≫ ru) (𝟙 B)) ≫ o.inv := by
  dsimp only [Iso.trans, Functor.mapIso, Iso.prod, Iso.refl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hcancel : T.map (Prod.mkHom (𝟙 A) j.inv) ≫
      T.map (Prod.mkHom (𝟙 A) (j.hom ≫ T.map (Prod.mkHom e (𝟙 B)) ≫ lu)) =
        T.map (Prod.mkHom (𝟙 A) (T.map (Prod.mkHom e (𝟙 B)) ≫ lu)) := by
    rw [tensor_comp]
    simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hcancel, reassoc_of% ht]
  have hjoin : T.map (Prod.mkHom i.hom (𝟙 B)) ≫
      T.map (Prod.mkHom (T.map (Prod.mkHom (𝟙 A) e) ≫ ru) (𝟙 B)) =
        T.map (Prod.mkHom (i.hom ≫ T.map (Prod.mkHom (𝟙 A) e) ≫ ru) (𝟙 B)) := by
    rw [tensor_comp, Category.id_comp]
  rw [reassoc_of% hjoin]

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  commonStageTensorObject
attribute [local irreducible] Scheme.residueField commonStageTensorComparison
  operationStageTransitionIso
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
attribute [local irreducible] Padic.coefficientExtensionIntegers ScalarLocalization.composition
  pullbackTensorCommonUnit pullbackTensorRationalUnit commonStageDerivedTensor rationalDerivedTensor
  pullbackTensorCommonUnitStage pullbackTensorRationalRightUnitor pullbackTensorRationalLeftUnitor
  pullbackTensorCommonLeftUnitor pullbackTensorCommonRightUnitor pullbackTensorCommonAssociator

private theorem chosen_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The prescribed common-stage associator and unitors satisfy the triangle identity.

Source: Stacks Project, Tags 07A4 and 0941; the normalized coefficient tensor
constraints of `lem-pur-derived-pullback-tensor-constraints`.
(blueprint: lem-pur-common-stage-tensor-triangle).

Proof: apply faithful coherent reduction to the integral equation and insert
the prescribed tensor comparison and the reduction of the reconstructed unit.
Naturality of the tensor comparison cancels the inner comparison maps. The
remaining equation is precisely the monoidal triangle identity for the selected
coherent-system monoidal structure. No normalization of its associator on
cochain representatives or compatibility with a separate signed braiding is
needed. Localize this equality to each rational coefficient field using the
defining representatives of the rational associator and both unitors. For the
common-stage equation, choose a finite field containing the stages of both
inputs, the unit, and all intermediate tensor objects. The prescribed
common-stage representatives conjugate the rational associator and unitors by
the same tensor comparisons. Tensor naturality cancels these comparisons and
the unit-stage isomorphism; the rational triangle identity makes the resulting
representatives equal. Their classes are therefore equal. Zero objects and
an empty scheme require no additional hypothesis. -/
theorem commonStageTensor_triangle
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (pullbackTensorCommonAssociator l Ω X A (pullbackTensorCommonUnit l Ω X) B).hom ≫
        (commonStageDerivedTensor l Ω X).map
          (Prod.mkHom (𝟙 A) (pullbackTensorCommonLeftUnitor l Ω X B).hom) =
      (commonStageDerivedTensor l Ω X).map
        (Prod.mkHom (pullbackTensorCommonRightUnitor l Ω X A).hom (𝟙 B)) := by
  classical
  open GeneralAlgebraicallyClosedCoefficients in
  let U := pullbackTensorCommonUnit l Ω X
  let AU := commonStageTensorObject l Ω X A U
  let UB := commonStageTensorObject l Ω X U B
  let S := commonStageTensorObject l Ω X AU B
  let R := commonStageTensorObject l Ω X A UB
  let O := commonStageTensorObject l Ω X A B
  let P := Padic.finiteCoefficientCompositum l Ω R.stage O.stage
  let L := Padic.finiteCoefficientCompositum l Ω S.stage P
  have hS : S.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage P).1
  have hP : P ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage P).2
  have hR : R.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 R.stage O.stage).1.trans hP
  have hO : O.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 R.stage O.stage).2.trans hP
  have hAU : AU.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 AU.stage B.stage).1.trans hS
  have hUB : UB.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage UB.stage).2.trans hR
  have hA : A.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage U.stage).1.trans hAU
  have hU : U.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage U.stage).2.trans hAU
  have hB : B.stage ≤ L :=
    ((Padic.finiteCoefficientFields_properties l Ω).1 AU.stage B.stage).2.trans hS
  let T := rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X
  have hT := chosen_spec (commonStageDerivedTensor_existsUnique l Ω X)
    (commonStageDerivedTensor l Ω X) (by unfold commonStageDerivedTensor; rfl)
  have ha := chosen_spec (pullbackTensorCommonAssociator_existsUnique l Ω X A U B)
    (pullbackTensorCommonAssociator l Ω X A U B)
    (by unfold pullbackTensorCommonAssociator; rfl) L hS hR
  have hl := chosen_spec (pullbackTensorCommonLeftUnitor_existsUnique l Ω X B)
    (pullbackTensorCommonLeftUnitor l Ω X B) (by unfold pullbackTensorCommonLeftUnitor; rfl) L hUB
  have hr := chosen_spec (pullbackTensorCommonRightUnitor_existsUnique l Ω X A)
    (pullbackTensorCommonRightUnitor l Ω X A) (by unfold pullbackTensorCommonRightUnitor; rfl) L hAU
  have hid (M : generalAlgebraicallyClosedConstructibleCategory l Ω X) (hM : M.stage ≤ L) :
      HEq (𝟙 M) (GeneralAlgebraicallyClosedCoefficients.ofHom M M L hM hM (𝟙 _)) :=
    heq_of_eq (StageSystem.PairCategory.id_eq_mkHom M hM)
  have hl₀ := tensor_map_heq (commonStageDerivedTensor l Ω X) rfl rfl (hT.1 U B) rfl
    (hid A hA) hl
  have hr₀ := tensor_map_heq (commonStageDerivedTensor l Ω X) (hT.1 A U) rfl rfl rfl
    hr (hid B hB)
  have hl₁ := hT.2 A UB A B L hR hO (𝟙 (A.toStage hA))
    ((commonStageTensorComparison l Ω X U B L hUB).hom ≫
      T.map (Prod.mkHom (pullbackTensorCommonUnitStage l Ω X L hU).hom (𝟙 _)) ≫
      (pullbackTensorRationalLeftUnitor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (B.toStage hB)).hom)
  have hr₁ := hT.2 AU B A B L hS hO
    ((commonStageTensorComparison l Ω X A U L hAU).hom ≫
      T.map (Prod.mkHom (𝟙 _) (pullbackTensorCommonUnitStage l Ω X L hU).hom) ≫
      (pullbackTensorRationalRightUnitor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (A.toStage hA)).hom)
    (𝟙 (B.toStage hB))
  have hl₂ := hl₀.trans hl₁
  have hr₂ := hr₀.trans hr₁
  have hleft := heq_comp (by rw [hT.1, hT.1])
    (by rw [hT.1, hT.1]) (hT.1 A B) ha hl₂
  apply eq_of_heq
  refine hleft.trans ((heq_of_eq ?_).trans hr₂.symm)
  dsimp only [GeneralAlgebraicallyClosedCoefficients.ofHom]
  rw [StageSystem.PairCategory.mkHom_comp_mkHom]
  apply congrArg (StageSystem.PairCategory.mkHom (X := S) (Y := O) L hS hO)
  exact conjugated_triangle T (pullbackTensorCommonUnitStage l Ω X L hU).hom
    (commonStageTensorComparison l Ω X A U L hAU)
    (commonStageTensorComparison l Ω X U B L hUB)
    (commonStageTensorComparison l Ω X AU B L hS)
    (commonStageTensorComparison l Ω X A UB L hR)
    (commonStageTensorComparison l Ω X A B L hO)
    (pullbackTensorRationalAssociator l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X
      (A.toStage hA) (U.toStage hU) (B.toStage hB)).hom
    (pullbackTensorRationalLeftUnitor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (B.toStage hB)).hom
    (pullbackTensorRationalRightUnitor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X (A.toStage hA)).hom
    (triangle_change_unit T
      (pullbackTensorRationalAssociator l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
      (pullbackTensorRationalUnit l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
      (U.toStage hU) (pullbackTensorCommonUnitStage l Ω X L hU).hom
      (fun M ↦ (pullbackTensorRationalLeftUnitor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X M).hom)
      (fun M ↦ (pullbackTensorRationalRightUnitor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X M).hom)
      (fun M N ↦ rationalAssociator_natural l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X
        (𝟙 M) (pullbackTensorCommonUnitStage l Ω X L hU).hom (𝟙 N))
      (rational_triangle l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X)
      (A.toStage hA) (B.toStage hB))

end WeilConjectures

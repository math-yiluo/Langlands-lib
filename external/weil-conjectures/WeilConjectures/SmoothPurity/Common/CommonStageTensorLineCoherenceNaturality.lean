/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful

/-! # Naturality of the common-stage tensor coherence components

Source: Stacks Project, Tags 06YS, 07A4 and 0941; the common-stage paragraph
of the coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-associator-natural).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open CategoryTheory.StageSystem.PairCategory

attribute [local irreducible] Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence commonStageTensorComparison operationStageTransitionIso
  pullbackTensorCommonLeft pullbackTensorCommonRight

private theorem chosen_operation_spec {A : Sort*} {p : A → Prop}
    (h : ∃! a, p a) (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

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

private theorem conjugated_square {C : Type*} [Category* C] (T : C × C ⥤ C)
    {A A' B B' C₀ C₀' U U' V V' : C}
    (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀')
    (i : U ≅ T.obj (A, B)) (i' : U' ≅ T.obj (A', B'))
    (j : V ≅ T.obj (B, C₀)) (j' : V' ≅ T.obj (B', C₀'))
    (a : T.obj (T.obj (A, B), C₀) ⟶ T.obj (A, T.obj (B, C₀)))
    (a' : T.obj (T.obj (A', B'), C₀') ⟶ T.obj (A', T.obj (B', C₀')))
    (hn : T.map (Prod.mkHom (T.map (Prod.mkHom f g)) h) ≫ a' =
      a ≫ T.map (Prod.mkHom f (T.map (Prod.mkHom g h)))) :
    T.map (Prod.mkHom (i.hom ≫ T.map (Prod.mkHom f g) ≫ i'.inv) h) ≫
        T.map (Prod.mkHom i'.hom (𝟙 C₀')) ≫ a' ≫
          T.map (Prod.mkHom (𝟙 A') j'.inv) =
      T.map (Prod.mkHom i.hom (𝟙 C₀)) ≫ a ≫
        T.map (Prod.mkHom (𝟙 A) j.inv) ≫
          T.map (Prod.mkHom f (j.hom ≫ T.map (Prod.mkHom g h) ≫ j'.inv)) := by
  have hl : T.map (Prod.mkHom (i.hom ≫ T.map (Prod.mkHom f g) ≫ i'.inv) h) ≫
      T.map (Prod.mkHom i'.hom (𝟙 C₀')) =
      T.map (Prod.mkHom i.hom (𝟙 C₀)) ≫
        T.map (Prod.mkHom (T.map (Prod.mkHom f g)) h) := by
    simp only [← T.map_comp, CategoryTheory.prod_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have hr : T.map (Prod.mkHom (𝟙 A) j.inv) ≫
      T.map (Prod.mkHom f (j.hom ≫ T.map (Prod.mkHom g h) ≫ j'.inv)) =
      T.map (Prod.mkHom f (T.map (Prod.mkHom g h))) ≫
        T.map (Prod.mkHom (𝟙 A') j'.inv) := by
    simp only [← T.map_comp, CategoryTheory.prod_comp,
      Iso.inv_hom_id_assoc, Category.comp_id, Category.id_comp]
  rw [← Category.assoc, ← Category.assoc, hl]
  simp only [Category.assoc]
  have hn' := congrArg (fun z ↦ z ≫ T.map (Prod.mkHom (𝟙 A') j'.inv)) hn
  simp only [Category.assoc] at hn'
  rw [hn', hr]

private theorem conjugated_outer_square {C : Type*} [catC : Category* C] (T : C × C ⥤ C)
    {A A' B B' C₀ C₀' U U' V V' W W' Z Z' : C}
    (f : A ⟶ A') (g : B ⟶ B') (h : C₀ ⟶ C₀')
    (i : U ≅ T.obj (A, B)) (i' : U' ≅ T.obj (A', B'))
    (j : V ≅ T.obj (B, C₀)) (j' : V' ≅ T.obj (B', C₀'))
    (s : W ≅ T.obj (U, C₀)) (s' : W' ≅ T.obj (U', C₀'))
    (t : Z ≅ T.obj (A, V)) (t' : Z' ≅ T.obj (A', V'))
    (a : T.obj (T.obj (A, B), C₀) ⟶ T.obj (A, T.obj (B, C₀)))
    (a' : T.obj (T.obj (A', B'), C₀') ⟶ T.obj (A', T.obj (B', C₀')))
    (hn : T.map (Prod.mkHom (T.map (Prod.mkHom f g)) h) ≫ a' =
      a ≫ T.map (Prod.mkHom f (T.map (Prod.mkHom g h)))) :
    (s.hom ≫ T.map (Prod.mkHom (i.hom ≫ T.map (Prod.mkHom f g) ≫ i'.inv) h) ≫ s'.inv) ≫
        (s' ≪≫ T.mapIso (Iso.prod i' (Iso.refl C₀'))).hom ≫ a' ≫
          (t' ≪≫ T.mapIso (Iso.prod (Iso.refl A') j')).inv =
      ((s ≪≫ T.mapIso (Iso.prod i (Iso.refl C₀))).hom ≫ a ≫
          (t ≪≫ T.mapIso (Iso.prod (Iso.refl A) j)).inv) ≫
        t.hom ≫ T.map (Prod.mkHom f (j.hom ≫ T.map (Prod.mkHom g h) ≫ j'.inv)) ≫
          t'.inv := by
  dsimp only [Iso.trans, Functor.mapIso, Iso.prod, Iso.refl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg (fun z ↦ s.hom ≫ z ≫ t'.inv)
    (conjugated_square T f g h i i' j j' a a' hn)

private theorem nested_comparison_naturality
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

private theorem nested_comparison_naturality_right
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

private theorem faithful_associator_naturality
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
    (nested_comparison_naturality R T U e f g h)
  simp only [Category.assoc] at hl
  rw [hl, hb, nested_comparison_naturality_right R T U e f g h]
  simpa only [Category.assoc] using (congrArg
    (fun z ↦ z ≫ U.map (Prod.mkHom (R.map f)
      (U.map (Prod.mkHom (R.map g) (R.map h))))) (ha A B C₀)).symm

private theorem counit_model_naturality
    {C D Z : Type*} [Category* C] [Category* D] [Category* Z]
    (R : D ⥤ Z) (L : Z ⥤ D) (adj : R ⊣ L) (F : C ⥤ D) (H : C ⥤ Z)
    (a : F ≅ H ⋙ L) {M N : C} (f : M ⟶ N) :
    R.map (F.map f) ≫ R.map (a.hom.app N) ≫ adj.counit.app (H.obj N) =
      (R.map (a.hom.app M) ≫ adj.counit.app (H.obj M)) ≫ H.map f := by
  rw [← R.map_comp_assoc, a.hom.naturality, R.map_comp]
  simp only [Functor.comp_map, Category.assoc]
  exact congrArg (fun k ↦ R.map (a.hom.app M) ≫ k)
    (adj.counit.naturality (H.map f))

private theorem integral_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    {K K' L L' M M' : sfIntegralConstructibleCategory l E X}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') :
    (constructibleIntegralTensor l E X).map
        (Prod.mkHom ((constructibleIntegralTensor l E X).map (Prod.mkHom f g)) h) ≫
        (pullbackTensorIntegralAssociator l E X K' L' M').hom =
      (pullbackTensorIntegralAssociator l E X K L M).hom ≫
        (constructibleIntegralTensor l E X).map
          (Prod.mkHom f ((constructibleIntegralTensor l E X).map (Prod.mkHom g h))) := by
  let R := (sfIntegralConstructible l E X).ι ⋙ (pullbackTensorCalculus l E X).reduction
  have hfaith : R.Faithful := by
    convert (integralSystemReduction_fullyFaithful l E X).2 using 0
    rfl
  let e : constructibleIntegralTensor l E X ⋙ R ≅
      R.prod R ⋙ (pullbackTensorCalculus l E X).systemClosed.tensor :=
    NatIso.ofComponents (fun MN ↦ pullbackTensorIntegralReductionTensor l E X MN.1 MN.2) (by
      intro MN PQ k
      unfold pullbackTensorIntegralReductionTensor
      dsimp only [Iso.trans, Functor.mapIso, asIso]
      convert
        counit_model_naturality (pullbackTensorCalculus l E X).reduction
          (coefficientSequenceLimit l E X) (pullbackTensorCalculus l E X).adjunction
          (integralCompletedTensor l E X)
          (((pullbackTensorCalculus l E X).reduction.prod
            (pullbackTensorCalculus l E X).reduction) ⋙
            (pullbackTensorCalculus l E X).systemClosed.tensor)
          (pullbackTensorIntegralTensorModel l E X) (Prod.mkHom k.1.hom k.2.hom) using 0
      rfl)
  apply faithful_associator_naturality R (constructibleIntegralTensor l E X)
    (pullbackTensorCalculus l E X).systemClosed.tensor e
    (pullbackTensorIntegralAssociator l E X)
    (pullbackTensorCalculus l E X).systemClosed.monoidal.associator ?_ ?_ f g h
  · intro A A' B B' C C' a b c
    exact @MonoidalCategory.associator_naturality _ _
      (pullbackTensorCalculus l E X).systemClosed.monoidal _ _ _ _ _ _ a b c
  · intro A B C
    exact (pullbackTensorIntegralAssociator_existsUnique l E X A B C).exists.choose_spec

private theorem rational_naturality
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
  have spec := chosen_operation_spec (rationalDerivedTensor_existsUnique l E X) F rfl
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
        have hleft := (tensor_map_heq F (ho (K, L)) (ho (K', L')) rfl rfl
          hfg HEq.rfl).trans
            (hp (ScalarLocalization.mk (I.obj (K.obj, L.obj)))
              (ScalarLocalization.mk (I.obj (K'.obj, L'.obj))) M M'
              (I.map (Prod.mkHom f g)) h (a * c) d)
        have hright := (tensor_map_heq F rfl rfl (ho (L, M)) (ho (L', M'))
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
        rw [integral_naturality l E X f g h]

-- These constructions are used only through their specifications below.
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue
  integralDerivedPullback integralCompletedTensor integralDerivedInternalHom
  sfRationalScalarExtension integralScalarExtension integralOrdinaryScalar
  rationalDerivedTensor rationalTensorScalarComparison sfIntegralConstructible

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the prescribed associator on all three input arrows.

Source: Stacks Project, Tags 06YS, 07A4 and 0941; the common-stage paragraph
of the coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-associator-natural).

Proof: first apply faithful coherent reduction to the integral associator
square. Naturality of the reduction/tensor comparison changes its two sides
into the usual associator square in the coherent system monoidal category.
The normalized formula for the integral associator then proves equality.
Localize: on each pure scalar tensor the equation is the integral equation
multiplied by the product of the three scalars; additivity extends it to
arbitrary rational arrows. Represent the three common-stage input arrows
over one finite extension containing all source and target coefficient fields.
Expand the common-stage associator and tensor maps using their representative
formulas. Functoriality cancels the comparison isomorphisms around the rational
square. The two resulting arrows are equal at that finite stage by rational
associator naturality, so their common-stage classes are equal. This includes identity and zero
arrows and imposes no Tor-amplitude hypothesis. -/
theorem commonStageTensorAssociator_naturality
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {K K' L L' M M' : generalAlgebraicallyClosedConstructibleCategory l Ω X}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') :
    let T := commonStageDerivedTensor l Ω X
    T.map (Prod.mkHom (T.map (Prod.mkHom f g)) h) ≫
        (pullbackTensorCommonAssociator l Ω X K' L' M').hom =
      (pullbackTensorCommonAssociator l Ω X K L M).hom ≫
        T.map (Prod.mkHom f (T.map (Prod.mkHom g h))) := by
  let T := commonStageDerivedTensor l Ω X
  have spec := chosen_operation_spec (commonStageDerivedTensor_existsUnique l Ω X) T rfl
  let O := commonStageTensorObject l Ω X
  have ho (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
      T.obj (P, Q) = O P Q :=
    spec.1 P Q
  have hm := spec.2
  obtain ⟨S₁, hK, hK', hf⟩ := exists_mkHom_eq f
  obtain ⟨S₂, hL, hL', hg⟩ := exists_mkHom_eq g
  obtain ⟨S₃, hM, hM', hh⟩ := exists_mkHom_eq h
  obtain ⟨S₄, h₁, h₂⟩ := exists_ge_ge S₁ S₂
  obtain ⟨S₅, h₃, h₄⟩ := exists_ge_ge S₄ S₃
  obtain ⟨S₆, h₅, hs⟩ := exists_ge_ge S₅ (O (O K L) M).stage
  obtain ⟨S₇, h₆, hs'⟩ := exists_ge_ge S₆ (O (O K' L') M').stage
  obtain ⟨S₈, h₇, ht⟩ := exists_ge_ge S₇ (O K (O L M)).stage
  obtain ⟨S, h₈, ht'⟩ := exists_ge_ge S₈ (O K' (O L' M')).stage
  have hs := hs.trans (h₆.trans (h₇.trans h₈))
  have hs' := hs'.trans (h₇.trans h₈)
  have ht := ht.trans h₈
  have hp (A B : generalAlgebraicallyClosedConstructibleCategory l Ω X) :=
    (Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage
  have hKL := (hp (O K L) M).1.trans hs
  have hKL' := (hp (O K' L') M').1.trans hs'
  have hLM := (hp K (O L M)).2.trans ht
  have hLM' := (hp K' (O L' M')).2.trans ht'
  obtain ⟨a, ha⟩ := hf S (h₁.trans (h₃.trans (h₅.trans (h₆.trans (h₇.trans h₈)))))
  obtain ⟨b, hb⟩ := hg S (h₂.trans (h₃.trans (h₅.trans (h₆.trans (h₇.trans h₈)))))
  obtain ⟨c, hc⟩ := hh S (h₄.trans (h₅.trans (h₆.trans (h₇.trans h₈))))
  subst f g h
  let R := rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S) X
  let ab := (commonStageTensorComparison l Ω X K L S hKL).hom ≫
    R.map (Prod.mkHom a b) ≫ (commonStageTensorComparison l Ω X K' L' S hKL').inv
  let bc := (commonStageTensorComparison l Ω X L M S hLM).hom ≫
    R.map (Prod.mkHom b c) ≫ (commonStageTensorComparison l Ω X L' M' S hLM').inv
  have hab := hm K L K' L' S hKL hKL' a b
  have hbc := hm L M L' M' S hLM hLM' b c
  have hlm := (tensor_map_heq T (ho K L) (ho K' L') rfl rfl hab HEq.rfl).trans
    (hm (O K L) M (O K' L') M' S hs hs' ab c)
  have hrm := (tensor_map_heq T rfl rfl (ho L M) (ho L' M') HEq.rfl hbc).trans
    (hm K (O L M) K' (O L' M') S ht ht' a bc)
  have hα := (pullbackTensorCommonAssociator_existsUnique l Ω X K L M).exists.choose_spec
    S hs ht
  have hα' := (pullbackTensorCommonAssociator_existsUnique l Ω X K' L' M').exists.choose_spec
    S hs' ht'
  have hos (A B C : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
      T.obj (T.obj (A, B), C) = O (O A B) C := by rw [ho, ho]
  have hot (A B C : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
      T.obj (A, T.obj (B, C)) = O A (O B C) := by rw [ho, ho]
  have hl := heq_comp (hos K L M) (hos K' L' M') (hot K' L' M') hlm hα'
  have hr := heq_comp (hos K L M) (hot K L M) (hot K' L' M') hα hrm
  apply eq_of_heq
  refine hl.trans ((heq_of_eq ?_).trans hr.symm)
  change ofHom _ _ S _ _ _ ≫ ofHom _ _ S _ _ _ =
    ofHom _ _ S _ _ _ ≫ ofHom _ _ S _ _ _
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom]
  congr 1
  unfold pullbackTensorCommonLeft pullbackTensorCommonRight
  have hn := rational_naturality l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω S) X a b c
  have q := conjugated_outer_square
    (C := Stage l Ω X S) (catC := stageCategory l Ω X S) R a b c
      (commonStageTensorComparison l Ω X K L S hKL)
      (commonStageTensorComparison l Ω X K' L' S hKL')
      (commonStageTensorComparison l Ω X L M S hLM)
      (commonStageTensorComparison l Ω X L' M' S hLM')
      (commonStageTensorComparison l Ω X (O K L) M S hs)
      (commonStageTensorComparison l Ω X (O K' L') M' S hs')
      (commonStageTensorComparison l Ω X K (O L M) S ht)
      (commonStageTensorComparison l Ω X K' (O L' M') S ht') _ _ hn
  exact q

end WeilConjectures

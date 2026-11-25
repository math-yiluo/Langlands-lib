/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints

/-! # Naturality of the normalized rational tensor associator

Source: the proved private integral and rational calculations in
`WeilConjectures.SmoothPurity.Common.CommonStageTensorLineCoherenceNaturality`,
extracted to avoid its
import of the parent comparison theorem. Stacks 06YS, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField

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

private theorem integral_naturality
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
  apply faithful_associator_naturality (coherentReduction l E W)
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
theorem rationalAssociator_natural
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

end WeilConjectures

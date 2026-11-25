/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints

/-! # Naturality of the prescribed common-stage pullback compositor

Source: blueprint dual-Tate compatibility, Step 5, coefficient-stage descent.
The proof follows the existing formal argument in SemilinearFieldOperationLifts,
without importing that consumer of the coefficient-descent interface.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct
namespace WeilConjectures.PodCoefficientDescent

attribute [local irreducible] rationalDerivedPullback sfIntegralConstructible
  commonStageDerivedPullback commonStageDerivedInternalHom rationalDerivedInternalHom
  commonStagePullbackComparison Scheme.residueField Linear.homModule
  ObjectProperty.FullSubcategory.category HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence

set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

private theorem pod_map_heq
    {C B : Type*} [Category* C] [Category* B] (F : C ⥤ B)
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem pod_rational_composition_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (h : Z ⟶ X)
    {K L : sfRationalConstructibleCategory l E Y} (a : K ⟶ L) :
    (rationalDerivedPullback l E (h ≫ f)).map a ≫
        (pullbackTensorRationalComposition l E f h L).hom =
      (pullbackTensorRationalComposition l E f h K).hom ≫
        (rationalDerivedPullback l E h).map ((rationalDerivedPullback l E f).map a) := by
  have obj {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M : sfRationalConstructibleCategory l E W) :
      (rationalDerivedPullback l E g).obj M =
        ⟨(constructibleIntegralPullback l E g).obj M.obj⟩ :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 M
  have hom {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M N : sfIntegralConstructibleCategory l E W) (b : M ⟶ N)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
      HEq ((rationalDerivedPullback l E g).map (X := ⟨M⟩) (Y := ⟨N⟩)
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] b))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E g).map b) := by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2 M N b c
  have : (rationalDerivedPullback l E (h ≫ f)).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.1
  have : (rationalDerivedPullback l E f).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
  have : (rationalDerivedPullback l E h).Additive :=
    by
      unfold rationalDerivedPullback
      exact (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.1
  have compobj (M) : (rationalDerivedPullback l E h).obj
      ((rationalDerivedPullback l E f).obj M) =
      ⟨(constructibleIntegralPullback l E h).obj
        ((constructibleIntegralPullback l E f).obj M.obj)⟩ := by
    rw [obj, obj]
  have hc (M) := (pullbackTensorRationalComposition_existsUnique l E f h M).exists.choose_spec
  induction a using TensorProduct.inductionOn with
  | tmul c a =>
    have hm := (pod_map_heq (rationalDerivedPullback l E h) (obj f K) (obj f L)
      (hom f K.obj L.obj a c)).trans
        (hom h _ _ ((constructibleIntegralPullback l E f).map a) c)
    have hleft := heq_comp (obj (h ≫ f) K) (obj (h ≫ f) L) (compobj L)
      (hom (h ≫ f) K.obj L.obj a c) (hc L)
    have hright := heq_comp (obj (h ≫ f) K) (compobj K) (compobj L) (hc K) hm
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    change ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app L.obj)
        (c ⊗ₜ (constructibleIntegralPullback l E (h ≫ f)).map a) =
      ScalarLocalization.composition _ _ _ _ _ _
        (c ⊗ₜ (constructibleIntegralPullback l E h).map
          ((constructibleIntegralPullback l E f).map a))
        (1 ⊗ₜ (pullbackTensorIntegralComposition l E f h).hom.app K.obj)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one]
    exact congrArg (fun b ↦ c ⊗ₜ b)
      ((pullbackTensorIntegralComposition l E f h).hom.naturality a)
  | add a b ha hb =>
    change (rationalDerivedPullback l E (h ≫ f)).map (a + b : K ⟶ L) ≫ _ =
      _ ≫ (rationalDerivedPullback l E h).map
        ((rationalDerivedPullback l E f).map (a + b : K ⟶ L))
    rw [Functor.map_add, Functor.map_add, Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add, ha, hb]

attribute [local irreducible] Preadditive.homGroup
  ScalarLocalization.category ScalarLocalization.linear

private theorem pod_composition_representative_naturality
    {C D B : Type*} [Category* C] [Category* D] [Category* B]
    (G : C ⥤ D) (F : D ⥤ B) (H : C ⥤ B)
    {K N : C} (r : K ⟶ N)
    (eK : H.obj K ≅ F.obj (G.obj K)) (eN : H.obj N ≅ F.obj (G.obj N))
    (nat : H.map r ≫ eN.hom = eK.hom ≫ F.map (G.map r))
    {XK XN : D} {ZK ZN WK WN : B}
    (aK : ZK ≅ H.obj K) (aN : ZN ≅ H.obj N)
    (bK : XK ≅ G.obj K) (bN : XN ≅ G.obj N)
    (dK : WK ≅ F.obj XK) (dN : WN ≅ F.obj XN) :
    (aK.hom ≫ H.map r ≫ aN.inv) ≫
        (aN.hom ≫ eN.hom ≫ F.map bN.inv ≫ dN.inv) =
      (aK.hom ≫ eK.hom ≫ F.map bK.inv ≫ dK.inv) ≫
        (dK.hom ≫ F.map (bK.hom ≫ G.map r ≫ bN.inv) ≫ dN.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_map_assoc]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ aK.hom ≫ t ≫ F.map bN.inv ≫ dN.inv) nat

private theorem pod_ofHom_square
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    (P Q R S : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hP : P.stage ≤ L) (hQ : Q.stage ≤ L) (hR : R.stage ≤ L) (hS : S.stage ≤ L)
    (u : P.toStage hP ⟶ Q.toStage hQ) (v : Q.toStage hQ ⟶ S.toStage hS)
    (u' : P.toStage hP ⟶ R.toStage hR) (v' : R.toStage hR ⟶ S.toStage hS)
    (e : u ≫ v = u' ≫ v') :
    GeneralAlgebraicallyClosedCoefficients.ofHom P Q L hP hQ u ≫
        GeneralAlgebraicallyClosedCoefficients.ofHom Q S L hQ hS v =
      GeneralAlgebraicallyClosedCoefficients.ofHom P R L hP hR u' ≫
        GeneralAlgebraicallyClosedCoefficients.ofHom R S L hR hS v' := by
  simpa only [GeneralAlgebraicallyClosedCoefficients.ofHom,
    StageSystem.PairCategory.mkHom_comp_mkHom] using
      congrArg (StageSystem.PairCategory.mkHom L hP hS) e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The prescribed common-stage pullback compositor is natural in every arrow.
Source: blueprint dual-Tate compatibility, Step 5: rational and common-stage descent.
(blueprint: lem-pod-common-stage-compositor-naturality).
Proof: on a pure tensor the rational equation is the integral compositor's
naturality equation tensored with the scalar; tensor induction extends it to
all localized arrows. Represent a common-stage arrow over one coefficient field.
The prescribed operation and compositor formulas conjugate the rational equation
by the pullback comparison isomorphisms. Cancel adjacent inverse comparisons and
apply the common-stage class map. No faithfulness of transition functors is used. -/
theorem commonStagePullbackComposition_naturality
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (h : Z ⟶ X)
    {K N : generalAlgebraicallyClosedConstructibleCategory l Ω Y} (a : K ⟶ N) :
    (commonStageDerivedPullback l Ω (h ≫ f)).map a ≫
        (pullbackTensorCommonComposition l Ω f h N).hom =
      (pullbackTensorCommonComposition l Ω f h K).hom ≫
        (commonStageDerivedPullback l Ω h).map ((commonStageDerivedPullback l Ω f).map a) := by
  have obj {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)] (M) :
      (commonStageDerivedPullback l Ω g).obj M = commonStagePullbackObject l Ω g M := by
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.1 M
  have hom {V W : Scheme.{u}} (g : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W)
      (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L) (hN : N.stage ≤ L)
      (r : M.toStage hM ⟶ N.toStage hN) :
      HEq ((commonStageDerivedPullback l Ω g).map
        (GeneralAlgebraicallyClosedCoefficients.ofHom M N L hM hN r))
        (GeneralAlgebraicallyClosedCoefficients.ofHom
          (commonStagePullbackObject l Ω g M) (commonStagePullbackObject l Ω g N) L hM hN
          ((commonStagePullbackComparison l Ω g M L hM).hom ≫
            (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
              g).map r ≫ (commonStagePullbackComparison l Ω g N L hN).inv)) := by
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω g).exists.choose_spec.2 M N L hM hN r
  have compobj (M) : (commonStageDerivedPullback l Ω h).obj
      ((commonStageDerivedPullback l Ω f).obj M) =
      commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f M) := by
    rw [obj, obj]
  have hc (M L hM) :=
    (pullbackTensorCommonComposition_existsUnique l Ω f h M).exists.choose_spec L hM
  induction a using StageSystem.PairCategory.hom_induction with
  | h L hK hN r =>
    have hm := (pod_map_heq (commonStageDerivedPullback l Ω h) (obj f K) (obj f N)
      (hom f K N L hK hN r)).trans
        (hom h (commonStagePullbackObject l Ω f K)
          (commonStagePullbackObject l Ω f N) L hK hN _)
    have hleft := heq_comp (obj (h ≫ f) K) (obj (h ≫ f) N) (compobj N)
      (hom (h ≫ f) K N L hK hN r) (hc N L hN)
    have hright := heq_comp (obj (h ≫ f) K) (compobj K) (compobj N) (hc K L hK) hm
    apply eq_of_heq
    refine hleft.trans (HEq.trans ?_ hright.symm)
    apply heq_of_eq
    refine pod_ofHom_square l Ω Z
      (commonStagePullbackObject l Ω (h ≫ f) K)
      (commonStagePullbackObject l Ω (h ≫ f) N)
      (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f K))
      (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f N))
      L hK hN hK hN _ _ _ _ ?_
    have e := @pod_composition_representative_naturality
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L)
      (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z L)
      (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y L)
      (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X L)
      (GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Z L)
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f)
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) h)
      (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (h ≫ f))
      (K.toStage hK) (N.toStage hN)
      r (pullbackTensorRationalComposition l _ f h (K.toStage hK))
      (pullbackTensorRationalComposition l _ f h (N.toStage hN))
      (pod_rational_composition_naturality l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f h
        (K := K.toStage hK) (L := N.toStage hN) r)
      ((commonStagePullbackObject l Ω f K).toStage hK)
      ((commonStagePullbackObject l Ω f N).toStage hN)
      ((commonStagePullbackObject l Ω (h ≫ f) K).toStage hK)
      ((commonStagePullbackObject l Ω (h ≫ f) N).toStage hN)
      ((commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f K)).toStage hK)
      ((commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f N)).toStage hN)
      (commonStagePullbackComparison l Ω (h ≫ f) K L hK)
      (commonStagePullbackComparison l Ω (h ≫ f) N L hN)
      (commonStagePullbackComparison l Ω f K L hK)
      (commonStagePullbackComparison l Ω f N L hN)
      (commonStagePullbackComparison l Ω h (commonStagePullbackObject l Ω f K) L hK)
      (commonStagePullbackComparison l Ω h (commonStagePullbackObject l Ω f N) L hN)
    exact e

end WeilConjectures.PodCoefficientDescent

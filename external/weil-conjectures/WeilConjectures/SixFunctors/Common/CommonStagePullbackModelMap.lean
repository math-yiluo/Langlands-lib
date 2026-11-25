/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Pullback of a common-stage model comparison

Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-stage-pullback-model-map).

This computes the pullback of the comparison between an object and a finite-stage model.
The proof identifies the prescribed pullback functor with coherent stage-system descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option Elab.async false
set_option linter.auxLemma false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

private theorem morphism_isoToStage
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, Category (A i)]
    {B : I → Type*} [∀ i, Category (B i)]
    {S : StageSystem A} {T : StageSystem B} (F : S.Morphism T)
    {i j : I} (h : i ≤ j) (K : A i) :
    F.functor.map (S.isoToStage ⟨i, K⟩ h).hom =
      (T.isoToStage ⟨i, (F.Φ i).obj K⟩ h).hom ≫
        (T.ι j).map ((F.β h).hom.app K) := by
  dsimp only [StageSystem.isoToStage]
  erw [StageSystem.ι_map_eq (le_rfl : j ≤ j), F.functor_map_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  dsimp only [StageSystem.Morphism.mapAt]
  have hc := F.coh h (le_rfl : j ≤ j) K
  have hc' := congrArg (fun t ↦
    ((T.assoc h (le_rfl : j ≤ j)).inv.app ((F.Φ i).obj K)) ≫ t ≫
      (F.Φ j).map ((S.assoc h (le_rfl : j ≤ j)).inv.app K) ≫
        (F.β (le_rfl : j ≤ j)).inv.app ((S.T h).obj K)) hc
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at hc'
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
    Category.comp_id, Iso.inv_hom_id_app_assoc] at hc'
  exact hc'.symm

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor commonStagePullbackComparison
  commonStageTensorComparison operationStageTransitionIso
  GeneralAlgebraicallyClosedCoefficients.unitor ScalarLocalization.category Scheme.residueField
  StageSystem.PairCategory.categoryStruct Preadditive.fullSubcategory
  sfIntegralConstructible ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup Linear.fullSubcategory sfIntegralConstructibleLinear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  StageSystem.ι
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  commonStagePullbackObject commonStageTensorObject

private theorem commonPullback_eq_morphism
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (F : (stageSystem l Ω Y).Morphism (stageSystem l Ω X))
    (hPhi : ∀ E, F.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
    (hb : ∀ (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
      (L : Index l Ω) (h : P.stage ≤ L),
      HEq ((F.β h).hom.app P.obj) (commonStagePullbackComparison l Ω f P L h).hom ∧
      HEq ((F.β h).inv.app P.obj) (commonStagePullbackComparison l Ω f P L h).inv) :
    commonStageDerivedPullback l Ω f = F.functor := by
  rcases F with ⟨Phi, b, hc⟩
  have hPhi' : Phi = fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f :=
    funext hPhi
  subst Phi
  apply (commonStageDerivedPullback_existsUnique l Ω f).unique
  · unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec
  · refine ⟨fun _ ↦ rfl, ?_⟩
    intro A B E hA hB a
    have ha := eq_of_heq (hb A E hA).1
    have hb' := eq_of_heq (hb B E hB).2
    apply heq_of_eq
    rw [StageSystem.Morphism.functor_map_mkHom]
    dsimp only [StageSystem.Morphism.mapAt]
    erw [ha, hb']

private theorem commonPullback_map_inclusion
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : Index l Ω) {P Q : Stage l Ω Y E} (a : P ⟶ Q) :
    HEq ((commonStageDerivedPullback l Ω f).map ((inclusion (Y := Y) E).map a))
      ((inclusion (Y := X) E).map
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).map a)) := by
  obtain ⟨b, hb, hc⟩ := commonStagePullback_comparison_data l Ω f
  let F : (stageSystem l Ω Y).Morphism (stageSystem l Ω X) :=
    { Φ := fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f
      β := b
      coh := hc }
  have hF := commonPullback_eq_morphism l Ω f F (fun _ ↦ rfl)
    (fun P L h ↦ hb h P.obj)
  rw [hF]
  exact heq_of_eq (F.functor_map_ι a)

private theorem commonPullback_isoToStage
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (h : P.stage ≤ L) :
    HEq ((commonStageDerivedPullback l Ω f).map
        ((stageSystem l Ω Y).isoToStage P h).hom)
      (((stageSystem l Ω X).isoToStage (commonStagePullbackObject l Ω f P) h).hom ≫
        (inclusion (Y := X) L).map (commonStagePullbackComparison l Ω f P L h).hom) := by
  obtain ⟨b, hb, hc⟩ := commonStagePullback_comparison_data l Ω f
  let F : (stageSystem l Ω Y).Morphism (stageSystem l Ω X) :=
    { Φ := fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f
      β := b
      coh := hc }
  have hF := commonPullback_eq_morphism l Ω f F (fun _ ↦ rfl)
    (fun P L h ↦ hb h P.obj)
  rw [hF]
  cases P with
  | mk E K =>
    have hi := morphism_isoToStage F h K
    have he := eq_of_heq (hb h K).1
    exact heq_of_eq (hi.trans (by rw [he]))

/-- Pullback maps a model comparison to its rational representative.

Source: thm-sf-pf-field.proof.md, Compatibility, passage to a common coefficient field.
(blueprint: lem-sf-common-stage-pullback-model-map).

Proof: the uniquely prescribed common pullback equals descent of the coherent rational
pullback comparisons. Its action on `isoToStage` is the transition comparison, by
coherence, and its action on an included arrow is the included rational pullback.
Functoriality composes these two formulas. -/
theorem commonStageDerivedPullback_map_model
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (h : P.stage ≤ L)
    {K : Stage l Ω Y L} (a : P.toStage h ⟶ K) :
    HEq ((commonStageDerivedPullback l Ω f).map
        (((stageSystem l Ω Y).isoToStage P h).hom ≫
          (inclusion (Y := Y) L).map a))
      (((stageSystem l Ω X).isoToStage (commonStagePullbackObject l Ω f P) h).hom ≫
        (inclusion (Y := X) L).map
          ((commonStagePullbackComparison l Ω f P L h).hom ≫
            (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map a)) := by
  have ho : ∀ P, (commonStageDerivedPullback l Ω f).obj P =
      commonStagePullbackObject l Ω f P := by
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1
  have h₁ := commonPullback_isoToStage l Ω f P L h
  have h₂ := commonPullback_map_inclusion l Ω f L a
  have hh := heq_comp (ho P) (ho ((inclusion (Y := Y) L).obj (P.toStage h)))
    (ho ((inclusion (Y := Y) L).obj K)) h₁ h₂
  exact (heq_of_eq ((commonStageDerivedPullback l Ω f).map_comp _ _)).trans
    (hh.trans (heq_of_eq ((Category.assoc _ _ _).trans
      (congrArg (fun k ↦ _ ≫ k)
        ((inclusion (Y := X) L).map_comp _ _).symm))))

end WeilConjectures

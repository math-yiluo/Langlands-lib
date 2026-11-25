/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison

/-! # Naturality of the prescribed common-stage pullback tensor comparison

Source: recorded blueprint coefficient conventions, the common-stage paragraph of
`prose-03-02`; Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open CategoryTheory.StageSystem.PairCategory
namespace WeilConjectures

-- Cache the existing category instances while comparing finite-stage arrows.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

private theorem tensor_map_heq {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ D) {A B A' B' M N M' N' : C}
    (hA : A = M) (hB : B = N) (hA' : A' = M') (hB' : B' = N')
    {a : A ⟶ A'} {b : B ⟶ B'} {f : M ⟶ M'} {g : N ⟶ N'}
    (ha : HEq a f) (hb : HEq b g) :
    HEq (T.map (Prod.mkHom a b)) (T.map (Prod.mkHom f g)) := by
  cases hA; cases hB; cases hA'; cases hB'; cases ha; cases hb
  rfl

private theorem conjugated_naturality {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (U : C × C ⥤ C) (V : D × D ⥤ D)
    (μ : ∀ M N, F.obj (U.obj (M, N)) ≅ V.obj (F.obj M, F.obj N))
    (hn : ∀ {M M' N N' : C} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (U.map (Prod.mkHom a b)) ≫ (μ M' N').hom =
        (μ M N).hom ≫ V.map (Prod.mkHom (F.map a) (F.map b)))
    {M M' N N' A A' : C} {B B' S S' P P' Q Q' : D}
    (a : M ⟶ M') (b : N ⟶ N')
    (t : A ≅ U.obj (M, N)) (t' : A' ≅ U.obj (M', N'))
    (p : B ≅ F.obj A) (p' : B' ≅ F.obj A')
    (m : P ≅ F.obj M) (m' : P' ≅ F.obj M')
    (n : Q ≅ F.obj N) (n' : Q' ≅ F.obj N')
    (s : S ≅ V.obj (P, Q)) (s' : S' ≅ V.obj (P', Q')) :
    (p.hom ≫ F.map (t.hom ≫ U.map (Prod.mkHom a b) ≫ t'.inv) ≫ p'.inv) ≫
        (p'.hom ≫ F.map t'.hom ≫ (μ M' N').hom ≫
          V.map (Prod.mkHom m'.inv n'.inv) ≫ s'.inv) =
      (p.hom ≫ F.map t.hom ≫ (μ M N).hom ≫
          V.map (Prod.mkHom m.inv n.inv) ≫ s.inv) ≫
        (s.hom ≫ V.map (Prod.mkHom (m.hom ≫ F.map a ≫ m'.inv)
          (n.hom ≫ F.map b ≫ n'.inv)) ≫ s'.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← F.map_comp_assoc t'.inv t'.hom, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [← V.map_comp_assoc]
  simp only [prod_comp, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn a b]
  rw [← V.map_comp_assoc]
  rfl

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  commonStageTensorComparison commonStagePullbackComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational comparison naturality implies naturality of the prescribed common-stage class.

Source: recorded blueprint, derived-pullback-tensor-hom, common-stage passage;
Stacks 07A4 (blueprint: lem-pur-common-stage-pullback-tensor-naturality).

Proof: Represent the two input arrows over finite coefficient fields and enlarge
both fields so that they also contain the source and target tensor-object stages.
Use the defining representative formulas for tensor and pullback on each arrow,
and for the canonical comparison on each pair of objects. At this common stage,
composition is represented by composition. The adjacent tensor and pullback
comparison inverses cancel, and the remaining square is rational naturality,
conjugated by the endpoint comparisons. Taking the common-stage morphism class
gives the asserted equality. No faithfulness of coefficient extension is used. -/
theorem commonStagePullbackTensor_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hn : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
      {M M' N N' : sfRationalConstructibleCategory l E Y} (a : M ⟶ M') (b : N ⟶ N'),
      (rationalDerivedPullback l E f).map
          ((rationalDerivedTensor l E Y).map (Prod.mkHom a b)) ≫
          (canonicalRationalPullbackTensor l E f M' N').hom =
        (canonicalRationalPullbackTensor l E f M N).hom ≫
          (rationalDerivedTensor l E X).map
            (Prod.mkHom ((rationalDerivedPullback l E f).map a)
              ((rationalDerivedPullback l E f).map b)))
    {M M' N N' : generalAlgebraicallyClosedConstructibleCategory l Ω Y}
    (a : M ⟶ M') (b : N ⟶ N') :
    (commonStageDerivedPullback l Ω f).map
        ((commonStageDerivedTensor l Ω Y).map (Prod.mkHom a b)) ≫
        (canonicalCommonStagePullbackTensor l Ω f M' N').hom =
      (canonicalCommonStagePullbackTensor l Ω f M N).hom ≫
        (commonStageDerivedTensor l Ω X).map
          (Prod.mkHom ((commonStageDerivedPullback l Ω f).map a)
            ((commonStageDerivedPullback l Ω f).map b)) := by
  let F := commonStageDerivedPullback l Ω f
  let TY := commonStageDerivedTensor l Ω Y
  let TX := commonStageDerivedTensor l Ω X
  let OY := commonStageTensorObject l Ω Y
  let OX := commonStageTensorObject l Ω X
  let P := commonStagePullbackObject l Ω f
  have hoY (A B) : TY.obj (A, B) = OY A B := by
    unfold TY commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 A B
  have hoX (A B) : TX.obj (A, B) = OX A B := by
    unfold TX commonStageDerivedTensor
    exact (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 A B
  have hoF (A) : F.obj A = P A := by
    unfold F commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 A
  have hmY := (commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.2
  have hmX := (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.2
  have hmF := (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.2
  have hmap {L : AlgebraicallyClosedCoefficients.Index l Ω}
      {A B A' B' : generalAlgebraicallyClosedConstructibleCategory l Ω Y}
      (hA : A = A') (hB : B = B') (hA' : A'.stage ≤ L) (hB' : B'.stage ≤ L)
      (c : A ⟶ B) (d : A'.toStage hA' ⟶ B'.toStage hB')
      (hc : HEq c (ofHom A' B' L hA' hB' d)) :
      HEq (F.map c) (ofHom (P A') (P B') L hA' hB'
        ((commonStagePullbackComparison l Ω f A' L hA').hom ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map d ≫
          (commonStagePullbackComparison l Ω f B' L hB').inv)) := by
    subst A B
    cases hc
    exact hmF A' B' L hA' hB' d
  obtain ⟨L₁, _, _, ha⟩ := exists_mkHom_eq a
  obtain ⟨L₂, _, _, hb⟩ := exists_mkHom_eq b
  obtain ⟨L₃, h₁, h₂⟩ := exists_ge_ge L₁ L₂
  obtain ⟨L₄, h₃, hMN⟩ := exists_ge_ge L₃ (OY M N).stage
  obtain ⟨L, h₄, hMN'⟩ := exists_ge_ge L₄ (OY M' N').stage
  have hMN := hMN.trans h₄
  obtain ⟨a', ha'⟩ := ha L (h₁.trans (h₃.trans h₄))
  obtain ⟨b', hb'⟩ := hb L (h₂.trans (h₃.trans h₄))
  subst a b
  have ht := hmY M N M' N' L hMN hMN' a' b'
  have hFt := hmap (hoY M N) (hoY M' N') hMN hMN' _ _ ht
  have hFa := hmF M M' L _ _ a'
  have hFb := hmF N N' L _ _ b'
  have htX := hmX (P M) (P N) (P M') (P N') L hMN hMN'
    ((commonStagePullbackComparison l Ω f M L _).hom ≫
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map a' ≫
      (commonStagePullbackComparison l Ω f M' L _).inv)
    ((commonStagePullbackComparison l Ω f N L _).hom ≫
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map b' ≫
      (commonStagePullbackComparison l Ω f N' L _).inv)
  have htX' := (tensor_map_heq TX (hoF M) (hoF N) (hoF M') (hoF N') hFa hFb).trans htX
  have hμ := (canonicalCommonStagePullbackTensor_existsUnique l Ω f M N).exists.choose_spec
    L hMN
  have hμ' := (canonicalCommonStagePullbackTensor_existsUnique l Ω f M' N').exists.choose_spec
    L hMN'
  change HEq (canonicalCommonStagePullbackTensor l Ω f M N).hom _ at hμ
  change HEq (canonicalCommonStagePullbackTensor l Ω f M' N').hom _ at hμ'
  have hs (A B) : F.obj (TY.obj (A, B)) = P (OY A B) := by rw [hoY, hoF]
  have ht (A B) : TX.obj (F.obj A, F.obj B) = OX (P A) (P B) := by rw [hoF, hoF, hoX]
  have hl := heq_comp (hs M N) (hs M' N') (ht M' N') hFt hμ'
  have hr := heq_comp (hs M N) (ht M N) (ht M' N') hμ htX'
  apply eq_of_heq
  refine hl.trans ((heq_of_eq ?_).trans hr.symm)
  change ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _ =
    ofHom _ _ L _ _ _ ≫ ofHom _ _ L _ _ _
  refine (mkHom_comp_mkHom _ _).trans
    ((congrArg (ofHom _ _ L _ _) ?_).trans (mkHom_comp_mkHom _ _).symm)
  dsimp only [pullbackTensorAtCommonStage, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.prod_hom]
  exact conjugated_naturality _ _ _ _ (hn _) a' b' _ _ _ _ _ _ _ _ _ _

end WeilConjectures

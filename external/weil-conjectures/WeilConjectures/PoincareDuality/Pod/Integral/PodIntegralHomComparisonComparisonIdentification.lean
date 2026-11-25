/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
public import WeilConjectures.PoincareDuality.PodCoefficientDescent.PodReindexingHomCoefficientDescent
import all WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationBase
import all WeilConjectures.PoincareDuality.PodCoefficientDescent.PodReindexingHomCoefficientDescent
import all WeilConjectures.PoincareDuality.PodCompletedReflection.PodReindexingCompletedEvaluationReflection
import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationShiftComposition

/-! # Identification of the integral comparison with the normalized comparison

Source: Stacks Project, Tag 0GMX; blueprint main-20261015
(blueprint: stage3-derived-automorphism-continuation-a-integral-comparison-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local instance 1000001] cachedCompose

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField

private theorem transportedEvaluation
    {C D : Type*} [Category C] [Category D]
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F G : C ⥤ D) (h : F = G)
    (t : SC.tensor ⋙ F ≅ F.prod F ⋙ SD.tensor)
    (c : HC ⋙ F ≅ F.op.prod F ⋙ HD)
    (he : ∀ M N, t.hom.app (HC.obj (op M, N), M) ≫
      SD.tensor.map (Prod.mkHom (c.hom.app (op M, N)) (𝟙 _)) ≫
        SD.evaluation (F.obj M) (F.obj N) = F.map (SC.evaluation M N)) (M N : C) :
    (((eqToIso h).app (SC.tensor.obj (HC.obj (op M, N), M))).symm ≪≫
        t.app (HC.obj (op M, N), M) ≪≫ SD.tensor.mapIso
          (((eqToIso h).app (HC.obj (op M, N))).prod ((eqToIso h).app M))).hom ≫
      SD.tensor.map (Prod.mkHom
        ((((eqToIso h).app (HC.obj (op M, N))).symm ≪≫ c.app (op M, N) ≪≫
          HD.mapIso ((((eqToIso h).app M).symm.op).prod ((eqToIso h).app N))).hom)
        (𝟙 _)) ≫ SD.evaluation (G.obj M) (G.obj N) = G.map (SC.evaluation M N) := by
  subst G
  simp only [eqToIso_refl, Iso.app_hom, Iso.app_inv, NatTrans.id_app,
    Iso.trans_hom, Iso.symm_hom, Iso.refl_inv, Iso.refl_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.op_hom, ← CategoryTheory.prod_id, op_id, Category.id_comp]
  erw [SD.tensor.map_id, HD.map_id]
  erw [Category.comp_id, Category.comp_id]
  exact he M N

section
attribute [local irreducible] podReindexCalculus

private theorem ordinaryComparisonEvaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : PodCompletedReflection.Comparison l E g) (M N : PodCompletedReflection.D l E Y) :
    ((PodCompletedReflection.closed l E X).transpose
      ((podOrdinaryReindex l E g).obj ((podReindexingDerivedHom l E Y none).obj (op M, N)))
      ((podOrdinaryReindex l E g).obj M) ((podOrdinaryReindex l E g).obj N)).symm
        (PodCompletedReflection.homComparison l E g c M N).hom =
      (PodCompletedReflection.tensorComparison l E g c
        ((podReindexingDerivedHom l E Y none).obj (op M, N)) M).inv ≫
        (podOrdinaryReindex l E g).map ((PodCompletedReflection.closed l E Y).evaluation M N) := by
  let F := podOrdinaryReindex.{u, u} l E g
  let SX := PodCompletedReflection.closed l E X
  let SY := PodCompletedReflection.closed l E Y
  -- Fix the smallness witnesses before elaborating the comparison projections.
  have hev := @PodReindexingCoherence.evaluation_laws.{u} l _ E _ _ _ X Y g _
    (inferInstance : ∀ x : X, Invertible (l : X.residueField x))
    (inferInstance : ∀ y : Y, Invertible (l : Y.residueField y))
    (essentiallySmallSelf.{0, u, u + 1} X.ProEt)
    (essentiallySmallSelf.{0, u, u + 1} Y.ProEt) none
    (PodCompletedReflection.closed.{u} l E X) (PodCompletedReflection.closed.{u} l E Y)
    (PodCompletedReflection.models.{u} l E X)
    (PodCompletedReflection.models.{u} l E Y) c
  let ct := @PodReindexingCoherence.Comparison.tensor.{u} l _ E _ _ _ X Y g _
    (essentiallySmallSelf.{0, u, u + 1} X.ProEt)
    (essentiallySmallSelf.{0, u, u + 1} Y.ProEt) none SX SY
    (PodCompletedReflection.models l E X) (PodCompletedReflection.models l E Y) c
  let ch := @PodReindexingCoherence.Comparison.derived.{u} l _ E _ _ _ X Y g _
    (essentiallySmallSelf.{0, u, u + 1} X.ProEt)
    (essentiallySmallSelf.{0, u, u + 1} Y.ProEt) none SX SY
    (PodCompletedReflection.models l E X) (PodCompletedReflection.models l E Y) c
  have he := @PodReindexingCoherence.EvaluationLaws.evaluation.{u} l _ E _ _ _ X Y g _
    (essentiallySmallSelf.{0, u, u + 1} X.ProEt)
    (essentiallySmallSelf.{0, u, u + 1} Y.ProEt) none SX SY
    (PodCompletedReflection.models l E X) (PodCompletedReflection.models l E Y) c hev
  have hc := transportedEvaluation.{u + 2, u + 2, u + 2, u + 2}
    (C := PodCompletedReflection.D l E Y) (D := PodCompletedReflection.D l E X)
    (HC := podReindexingDerivedHom l E Y none)
    (HD := podReindexingDerivedHom l E X none) SY SX
    (podReindexingDerivedFunctor l E g none) F (PodCompletedReflection.reindex_eq l E g)
    ct ch he M N
  rw [uncurry_eq]
  apply (cancel_epi
    (PodCompletedReflection.tensorComparison l E g c
      ((podReindexingDerivedHom l E Y none).obj (op M, N)) M).hom).1
  simpa only [ct, ch, F, SX, SY, PodCompletedReflection.tensorComparison,
    PodCompletedReflection.homComparison, PodCompletedReflection.reindexIso,
    PodCompletedReflection.hom, Category.assoc, Iso.hom_inv_id_assoc] using hc
end

private theorem integralTransposeNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (L : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (f : (constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2) :
    ((podIntegralClosed l E W).transpose L P f).hom =
      (pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f.hom) := by
  exact eq_of_heq ((podIntegralClosed_existsUnique l E W).exists.choose_spec L P f)

private theorem integralEvaluationNormalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory) :
    podCompletedTensorUnit l E W ((constructibleIntegralHom l E W).obj P).obj
        P.obj.1.unop.obj ≫ ((podIntegralClosed l E W).evaluation P).hom =
      (pullbackTensorCalculus l E W).integralClosed.evaluation
        P.obj.1.unop.obj P.obj.2.obj := by
  apply ((pullbackTensorCalculus l E W).integralClosed.transpose _ _ _).injective
  rw [← integralTransposeNormalization]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply]
  let S := (pullbackTensorCalculus l E W).integralClosed
  change 𝟙 _ = S.transpose _ P.obj.1.unop.obj P.obj.2.obj
    (S.evaluation P.obj.1.unop.obj P.obj.2.obj)
  let := S.monoidal
  have he : (S.transpose _ _ _).symm (𝟙 _) = S.evaluation P.obj.1.unop.obj P.obj.2.obj := by
    rw [uncurry_eq]
    simp only [← CategoryTheory.prod_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← he, Equiv.apply_symm_apply]

private theorem tensorUnitNaturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (M N M' N' : PodCompletedReflection.D l E W)
    (f : M ⟶ M') (g : N ⟶ N') :
    (pullbackTensorCalculus l E W).integralClosed.tensor.map (Prod.mkHom f g) ≫
        podCompletedTensorUnit l E W M' N' =
      podCompletedTensorUnit l E W M N ≫
        (integralCompletedTensor.{u, u} l E W).map (Prod.mkHom f g) := by
  have ht := (PodCompletedReflection.tensorUnitNat.{u} l E W).naturality
    (X := (M, N)) (Y := (M', N')) (Prod.mkHom f g)
  simpa only [PodCompletedReflection.tensorUnitNat, podCompletedTensorUnit,
    PodCompletedReflection.closed, podReindexCalculus, pullbackTensorCalculus,
    Functor.comp_obj, Functor.comp_map, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj,
    Category.id_comp, Category.assoc] using ht

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The normalized comparison is the evaluation-defined partial comparison.

Source: Stacks Project, Tag 0GMX, proof Steps 8--11.  The normalized integral
comparison is characterized by its completion-unit equation.  Expand the
completion-unit normalization and use the defining transposition of
`podIntegralClosed`; parameter naturality and the tensor comparison identify its
transpose with the inverse-transpose formula defining
`podPartialHomComparison`.  Since each closed transposition is an additive
equivalence, equality of these transposes gives equality of the arrows.

(blueprint: stage3-derived-automorphism-continuation-a-integral-comparison-identification).
Proof: expand the normalization, compare inverse transposes, and apply injectivity
of the closed additive equivalence. -/
theorem podIntegralHomComparison_eq_integralComparison :
    ∀ P : (constructibleIntegralHomPairs l E Y).FullSubcategory,
      podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
        (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
          (canonicalIntegralPullbackTensor l E g) P =
        (PodCoefficientDescent.integralComparison l E g).hom.app P := by
  intro P
  obtain ⟨A, T, c, hA, hT, hα⟩ :=
    (PodCoefficientDescent.integral_existsUnique l E g).exists.choose_spec
  let F := podOrdinaryReindex.{u, u} l E g
  let G := integralDerivedPullback.{u, u} l E g
  let κ := podOrdinaryToCompleted l E g A
  let SX := PodCompletedReflection.closed l E X
  let H := integralDerivedInternalHom.{u, u} l E X
  let M := P.obj.1.unop
  let N := P.obj.2
  let L := (constructibleIntegralHom l E Y).obj P
  let β := podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
    (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
      (canonicalIntegralPullbackTensor l E g) P
  have hκ (K : sfIntegralConstructibleCategory l E Y) : IsIso (κ.app K.obj) :=
    PodCoefficientDescent.completionUnit_isIso l E g A hA K
  let d := H.mapIso ((asIso (κ.app M.obj)).op.prod (Iso.refl (G.obj N.obj)))
  have hβ : β.hom = SX.transpose (G.obj L.obj) (G.obj M.obj) (G.obj N.obj)
      (podCompletedTensorUnit l E X (G.obj L.obj) (G.obj M.obj) ≫
        (canonicalIntegralPullbackTensor l E g L M).inv.hom ≫
        G.map ((podIntegralClosed l E Y).evaluation P).hom) := by
    exact integralTransposeNormalization l E X _ _ _
  have hunit : F.map (podCompletedTensorUnit l E Y L.obj M.obj) ≫ (T.tensor L M).hom =
      (PodCompletedReflection.tensorComparison l E g c L.obj M.obj).hom ≫
        podCompletedTensorUnit l E X (F.obj L.obj) (F.obj M.obj) :=
    (PodCompletedReflection.reindexing_laws l E g A T hA hT c).1 L M
  have hcan := hT.2.2.2.2.2 L M
  have hinv : (integralCompletedTensor.{u, u} l E X).map
        (Prod.mkHom (κ.app L.obj) (κ.app M.obj)) ≫
          (canonicalIntegralPullbackTensor l E g L M).inv.hom =
      (T.tensor L M).inv ≫ κ.app ((integralCompletedTensor.{u, u} l E Y).obj (L.obj, M.obj)) := by
    apply (cancel_epi (T.tensor L M).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hcan]
    have he := congrArg (fun f ↦ f.hom)
      (canonicalIntegralPullbackTensor l E g L M).hom_inv_id
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom] at he
    simpa only [Category.assoc] using
      (congrArg (κ.app ((integralCompletedTensor.{u, u} l E Y).obj (L.obj, M.obj)) ≫ ·)
        he).trans (Category.comp_id _)
  have hunitinv : podCompletedTensorUnit l E X (F.obj L.obj) (F.obj M.obj) ≫
        (T.tensor L M).inv =
      (PodCompletedReflection.tensorComparison l E g c L.obj M.obj).inv ≫
        F.map (podCompletedTensorUnit l E Y L.obj M.obj) := by
    apply (cancel_epi
      (PodCompletedReflection.tensorComparison l E g c L.obj M.obj).hom).1
    rw [← Category.assoc, ← hunit]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have hce := ordinaryComparisonEvaluation l E g c M.obj N.obj
  -- Verify the defining completion-unit equation by ordinary uncurrying.
  have hn : κ.app L.obj ≫ β.hom ≫ H.map
        (Prod.mkHom (κ.app M.obj).op (𝟙 (G.obj N.obj))) =
      (PodCompletedReflection.homComparison l E g c M.obj N.obj).hom ≫
        H.map (Prod.mkHom (𝟙 _) (κ.app N.obj)) := by
    rw [hβ]
    apply (SX.transpose (F.obj L.obj) (F.obj M.obj) (G.obj N.obj)).symm.injective
    erw [uncurry_comp, uncurry_hom_map, Equiv.symm_apply_apply,
      uncurry_hom_map, hce]
    simp only [Category.comp_id]
    erw [← CategoryTheory.prod_id, SX.tensor.map_id]
    simp only [Category.id_comp]
    have ht := tensorUnitNaturality l E X (F.obj L.obj) (F.obj M.obj)
      (G.obj L.obj) (G.obj M.obj) (κ.app L.obj) (κ.app M.obj)
    calc
      _ = podCompletedTensorUnit l E X (F.obj L.obj) (F.obj M.obj) ≫
          (integralCompletedTensor.{u, u} l E X).map
            (Prod.mkHom (κ.app L.obj) (κ.app M.obj)) ≫
          (canonicalIntegralPullbackTensor l E g L M).inv.hom ≫
          G.map ((podIntegralClosed l E Y).evaluation P).hom := by
        simp only [← Category.assoc, ← SX.tensor.map_comp, prod_comp,
          Category.comp_id, Category.id_comp]
        erw [ht]
      _ = podCompletedTensorUnit l E X (F.obj L.obj) (F.obj M.obj) ≫
          (T.tensor L M).inv ≫ F.map ((podIntegralClosed l E Y).evaluation P).hom ≫
          κ.app N.obj := by
        rw [reassoc_of% hinv]
        erw [← κ.naturality ((podIntegralClosed l E Y).evaluation P).hom]
      _ = _ := by
        erw [reassoc_of% hunitinv, ← F.map_comp_assoc, integralEvaluationNormalization]
        simp only [Category.assoc]
        rfl
  -- The two completion maps are invertible on the constructible inputs.
  apply ObjectProperty.hom_ext
  change β.hom = ((PodCoefficientDescent.integralComparison l E g).hom.app P).hom
  apply (cancel_epi (κ.app L.obj)).1
  apply (cancel_mono d.hom).1
  simpa only [d, Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom, asIso_hom,
    Iso.refl_hom, κ, L, M, N, H, PodCoefficientDescent.integralComparison,
    constructibleIntegralHom, constructibleIntegralPullback, G,
    PodCoefficientDescent.integralPair, ObjectProperty.lift,
    Functor.comp_obj, Functor.prod_obj, Functor.op_obj, ObjectProperty.ι_obj,
    Category.assoc] using hn.trans (hα P).symm

end WeilConjectures

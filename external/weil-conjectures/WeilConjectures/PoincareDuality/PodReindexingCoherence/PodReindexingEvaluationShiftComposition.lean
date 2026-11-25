/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingHomResolutionModel
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluatedComparison
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingSignedShifts
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingTensorCompositor
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingTensorIdentity
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
public import WeilConjectures.SixFunctors.Supporting.OneKFlatChainTranspose
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Evaluation and signed coherence for the reindexed Hom complex

Source: blueprint `theorem-poincare-duality-frobenius--2`, proof Steps 1, 2 and 4;
Stacks Project, Tags 0GMX, 0A8X and 08J9
(blueprint: lem-pod-reindexing-evaluation-shift-composition).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

-- Cache the sheaf composition witness without repeatedly reconstructing the small site.
set_option linter.defProp false in
@[instance_reducible]
private def cachedCompose {C : Type*} [Category C] (J : GrothendieckTopology C)
    [EssentiallySmall.{u + 1} C] :
    J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  exact (equivSmallModel.{u + 1} C).hasSheafCompose J
    ((equivSmallModel.{u + 1} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

attribute [local instance 1000001] cachedCompose

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] signedShift podReindexingCoefficient podReindexingHomModel
  homComplexFunctor homComplexπ
  derivedInternalHomOfUniverses coefficientTotalTensor coefficientTensorGenerator
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors
  SheafOfModules.monoidalCategory

set_option allowUnsafeReducibility true in
attribute [local semireducible] podReindexingFunctor podReindexingComplexFunctor
  podReindexingDerivedFunctor podReindexingDerivedFactors

attribute [local irreducible] complexShift siteComp siteId

private theorem uncurry_formula {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {U M N : D} (f : U ⟶ H.obj (op M, N)) :
    (S.transpose U M N).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 M)) ≫ S.evaluation M N := by
  let : MonoidalCategory D := S.monoidal
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation, Adjunction.homEquiv, Equiv.symm,
    MonoidalCategory.tensor, MonoidalCategory.tensorRight, Functor.flip,
    MonoidalCategory.curriedTensor, Functor.comp_obj, Prod.sectR_obj]
  simp only [MonoidalCategory.tensorHom_id]
  rfl

private theorem evaluation_natural {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {M M' N N' : D} (a : M' ⟶ M) (b : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op b)) (𝟙 M')) ≫
      S.evaluation M' N' =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op M, N))) a) ≫
        S.evaluation M N ≫ b := by
  have hs : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 N))) (𝟙 M')) ≫
      S.evaluation M' N =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op M, N))) a) ≫ S.evaluation M N := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom, MonoidalCategory.tensorRight,
      MonoidalCategory.tensorLeft, Functor.flip, MonoidalCategory.curriedTensor,
      Functor.comp_map, Prod.sectR_map, Prod.sectL_map] using
        S.evaluation_naturality M M' N a
  have ht : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op M')) b)) (𝟙 M')) ≫
      S.evaluation M' N' = S.evaluation M' N ≫ b := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_obj, MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorRight, Functor.flip, MonoidalCategory.curriedTensor,
      Functor.comp_obj, Functor.comp_map, Prod.sectR_obj, Prod.sectR_map,
      Functor.id_obj, Functor.id_map] using (S.adjunction M').counit.naturality b
  have hp : Prod.mkHom a.op b =
      Prod.mkHom a.op (𝟙 N) ≫ Prod.mkHom (𝟙 (op M')) b := by simp
  rw [hp, H.map_comp]
  have hsplit : Prod.mkHom
      (H.map (Prod.mkHom a.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op M')) b)) (𝟙 M') =
      Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 N))) (𝟙 M') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op M')) b)) (𝟙 M') := by simp
  rw [hsplit, S.tensor.map_comp, Category.assoc, ht, ← Category.assoc, hs]
  exact Category.assoc _ _ _

private theorem uncurry_transport {D : Type*} [Category D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    {U M M' N N' : D} (f : U ⟶ H.obj (op M, N))
    (a : M' ⟶ M) (b : N ⟶ N') :
    S.tensor.map (Prod.mkHom (f ≫ H.map (Prod.mkHom a.op b)) (𝟙 M')) ≫
      S.evaluation M' N' =
      S.tensor.map (Prod.mkHom f a) ≫ S.evaluation M N ≫ b := by
  have hp : Prod.mkHom (f ≫ H.map (Prod.mkHom a.op b)) (𝟙 M') =
      Prod.mkHom f (𝟙 M') ≫
        Prod.mkHom (H.map (Prod.mkHom a.op b)) (𝟙 M') := by simp
  rw [hp, S.tensor.map_comp, Category.assoc, evaluation_natural,
    ← Category.assoc, ← Category.assoc, ← S.tensor.map_comp]
  simp

private theorem hom_transport {A B : Type*} [Category A] [Category B]
    (TA : A × A ⥤ A) (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B)
    (S : CoefficientClosedStructure HB) (F F' : A ⥤ B)
    (t : TA ⋙ F ≅ (F.prod F) ⋙ S.tensor)
    (t' : TA ⋙ F' ≅ (F'.prod F') ⋙ S.tensor)
    (c : ∀ M N, F.obj (HA.obj (op M, N)) ⟶ HB.obj (op (F.obj M), F.obj N))
    (c' : ∀ M N, F'.obj (HA.obj (op M, N)) ⟶ HB.obj (op (F'.obj M), F'.obj N))
    (ev : ∀ M N, TA.obj (HA.obj (op M, N), M) ⟶ N)
    (hc : ∀ M N, t.hom.app (HA.obj (op M, N), M) ≫
      S.tensor.map (Prod.mkHom (c M N) (𝟙 (F.obj M))) ≫
        S.evaluation (F.obj M) (F.obj N) = F.map (ev M N))
    (hc' : ∀ M N, t'.hom.app (HA.obj (op M, N), M) ≫
      S.tensor.map (Prod.mkHom (c' M N) (𝟙 (F'.obj M))) ≫
        S.evaluation (F'.obj M) (F'.obj N) = F'.map (ev M N))
    (k : F ≅ F')
    (hk : ∀ M N, t.hom.app (M, N) ≫ S.tensor.map
      (Prod.mkHom (k.hom.app M) (k.hom.app N)) =
        k.hom.app (TA.obj (M, N)) ≫ t'.hom.app (M, N)) (M N : A) :
    c M N ≫ HB.map (Prod.mkHom (k.inv.app M).op (k.hom.app N)) =
      k.hom.app (HA.obj (op M, N)) ≫ c' M N := by
  let H := HA.obj (op M, N)
  let a := k.hom.app H
  let b := k.hom.app M
  let e : F.obj (TA.obj (H, M)) ≅ S.tensor.obj (F.obj H, F'.obj M) :=
    t.app (H, M) ≪≫ S.tensor.mapIso ((Iso.refl (F.obj H)).prod (k.app M))
  apply (S.transpose _ (F'.obj M) (F'.obj N)).symm.injective
  rw [uncurry_formula, uncurry_formula]
  apply (cancel_epi e.hom).1
  have h₁ : S.tensor.map (Prod.mkHom (𝟙 (F.obj H)) b) ≫
      S.tensor.map (Prod.mkHom (c M N) (k.inv.app M)) =
      S.tensor.map (Prod.mkHom (c M N) (𝟙 (F.obj M))) := by
    rw [← S.tensor.map_comp]
    simp [b]
  have h₂ : S.tensor.map (Prod.mkHom (𝟙 (F.obj H)) b) ≫
      S.tensor.map (Prod.mkHom (a ≫ c' M N) (𝟙 (F'.obj M))) =
      S.tensor.map (Prod.mkHom a b) ≫
        S.tensor.map (Prod.mkHom (c' M N) (𝟙 (F'.obj M))) := by
    simp only [← S.tensor.map_comp]
    congr 1
    ext <;> simp
  have hl : e.hom ≫
      (S.tensor.map (Prod.mkHom
        (c M N ≫ HB.map (Prod.mkHom (k.inv.app M).op (k.hom.app N)))
        (𝟙 (F'.obj M))) ≫ S.evaluation (F'.obj M) (F'.obj N)) =
      F.map (ev M N) ≫ k.hom.app N := by
    rw [uncurry_transport]
    change (t.hom.app (H, M) ≫ S.tensor.map (Prod.mkHom (𝟙 (F.obj H)) b)) ≫
      (S.tensor.map (Prod.mkHom (c M N) (k.inv.app M)) ≫
        S.evaluation (F.obj M) (F.obj N) ≫ k.hom.app N) = _
    rw [← Category.assoc, ← Category.assoc, Category.assoc (t.hom.app (H, M)), h₁]
    simpa only [Category.assoc] using congrArg (· ≫ k.hom.app N) (hc M N)
  have hr : e.hom ≫
      (S.tensor.map (Prod.mkHom (a ≫ c' M N) (𝟙 (F'.obj M))) ≫
        S.evaluation (F'.obj M) (F'.obj N)) =
      F.map (ev M N) ≫ k.hom.app N := by
    change (t.hom.app (H, M) ≫ S.tensor.map (Prod.mkHom (𝟙 (F.obj H)) b)) ≫
      (S.tensor.map (Prod.mkHom (a ≫ c' M N) (𝟙 (F'.obj M))) ≫
        S.evaluation (F'.obj M) (F'.obj N)) = _
    rw [← Category.assoc, Category.assoc (t.hom.app (H, M)), h₂,
      ← Category.assoc (t.hom.app (H, M)), hk]
    simp only [Category.assoc]
    rw [hc']
    exact (k.hom.naturality (ev M N)).symm
  exact hl.trans hr.symm

private theorem composite_evaluation {A B C : Type*}
    [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C)
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C)
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B) (HC : Cᵒᵖ × C ⥤ C)
    (t : TA ⋙ F ≅ (F.prod F) ⋙ TB) (t' : TB ⋙ G ≅ (G.prod G) ⋙ TC)
    (c : ∀ M N, F.obj (HA.obj (op M, N)) ⟶ HB.obj (op (F.obj M), F.obj N))
    (c' : ∀ M N, G.obj (HB.obj (op M, N)) ⟶ HC.obj (op (G.obj M), G.obj N))
    (evA : ∀ M N, TA.obj (HA.obj (op M, N), M) ⟶ N)
    (evB : ∀ M N, TB.obj (HB.obj (op M, N), M) ⟶ N)
    (evC : ∀ M N, TC.obj (HC.obj (op M, N), M) ⟶ N)
    (hc : ∀ M N, t.hom.app (HA.obj (op M, N), M) ≫
      TB.map (Prod.mkHom (c M N) (𝟙 (F.obj M))) ≫ evB (F.obj M) (F.obj N) =
        F.map (evA M N))
    (hc' : ∀ M N, t'.hom.app (HB.obj (op M, N), M) ≫
      TC.map (Prod.mkHom (c' M N) (𝟙 (G.obj M))) ≫ evC (G.obj M) (G.obj N) =
        G.map (evB M N)) (M N : A) :
    G.map (t.hom.app (HA.obj (op M, N), M)) ≫
      t'.hom.app (F.obj (HA.obj (op M, N)), F.obj M) ≫
        TC.map (Prod.mkHom (G.map (c M N) ≫ c' (F.obj M) (F.obj N))
          (𝟙 (G.obj (F.obj M)))) ≫ evC (G.obj (F.obj M)) (G.obj (F.obj N)) =
      G.map (F.map (evA M N)) := by
  have hn := t'.hom.naturality (Prod.mkHom (c M N) (𝟙 (F.obj M)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [G.map_id] at hn
  have hp : Prod.mkHom (G.map (c M N) ≫ c' (F.obj M) (F.obj N))
      (𝟙 (G.obj (F.obj M))) =
      Prod.mkHom (G.map (c M N)) (𝟙 (G.obj (F.obj M))) ≫
        Prod.mkHom (c' (F.obj M) (F.obj N)) (𝟙 (G.obj (F.obj M))) := by simp
  rw [hp, TC.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (t'.hom.app _), ← hn]
  simp only [Category.assoc]
  rw [hc', ← G.map_comp, ← G.map_comp, hc]

/-- Existence of the normalized comparison and the evaluation and signed-shift laws.
Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 0GMX, 0A8X, 08J9
(blueprint: lem-pod-reindexing-evaluation-shift-composition).

Proof: choose flat-term K-flat and K-injective representatives using
lem-pc-kflat-resolution and prop-pur-kinjective-resolutions-exist. Reindexing preserves
these by lem-pod-reindexing-hom-resolution-model. Its product projections give chain,
and its localization factorization gives derived. Reindex the total-tensor summands
and localize them, using def-coef-ringed-tensor-hom-model, to obtain tensor.
The chain-transpose lemma lem-sfb-hom-kflat-chain-transpose computes evaluation as
f tensor x maps to f(x), followed by inverse localized augmentation. The terms f(d x)
in the chain identity cancel. The two reindexed evaluations therefore coincide on
pure tensors and hence locally on every section. Koszul symmetry gives the M-first
formula with the same sign on each side. The closed adjunction of
lem-sf-ringed-derived-closed-symmetric-monoidal makes uncurrying bijective, proving
uniqueness. Uncurry the two proposed transported transposes and use tensor naturality;
injectivity gives the transpose formula for every derived arrow. The same argument
with precomposition in M and postcomposition in N gives naturality.
For shifts put q=p+a and s=r+b-a. Multiply the reindexed factor by (-1)^(a*r).
Its ratio in consecutive degrees is (-1)^a, so both terms in the Hom differential
commute. Both routes of the reindexing square have component (-1)^(a*r) F(f^(q-a)).
Localize using the preserved K-injective targets; the normalized source and target
shifts are exactly the localization of this signed comparison. This proves ShiftLaws,
including negative integers and unbounded representatives. -/
theorem comparison_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    ∃ c : Comparison l E g s SX SY TX TY,
      EvaluationLaws l E g s SX SY TX TY c ∧
      (∃ (sX : ChainShift l E X s) (sY : ChainShift l E Y s),
        ShiftLaws l E g s SX SY TX TY c sX sY) ∧
      (∀ c' : Comparison l E g s SX SY TX TY,
        ∃ (sX : ChainShift l E X s) (sY : ChainShift l E Y s),
          ShiftLaws l E g s SX SY TX TY c' sX sY) := by
  obtain ⟨c, he⟩ := evaluated_comparison_exists l E g s SX SY TX TY
  refine ⟨c, ?_, signed_shift_laws l E g s SX SY TX TY c, ?_⟩
  · refine ⟨he, ?_, ?_, ?_⟩
    · intro M N d
      constructor
      · intro hd
        apply (SX.transpose _ _ _).symm.injective
        rw [uncurry_formula, uncurry_formula]
        apply (cancel_epi (c.tensor.hom.app
          ((podReindexingDerivedHom l E Y s).obj (op M, N), M))).1
        exact hd.trans (he M N).symm
      · rintro rfl
        exact he M N
    · intro L M N b
      let F := podReindexingDerivedFunctor l E g s
      let f := SY.transpose L M N b
      have hb : SY.tensor.map (Prod.mkHom f (𝟙 M)) ≫ SY.evaluation M N = b :=
        (uncurry_formula SY f).symm.trans ((SY.transpose L M N).symm_apply_apply b)
      have hn := c.tensor.hom.naturality (Prod.mkHom f (𝟙 M))
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      rw [F.map_id] at hn
      apply (SX.transpose _ _ _).symm.injective
      rw [uncurry_formula, Equiv.symm_apply_apply]
      apply (cancel_epi (c.tensor.hom.app (L, M))).1
      have hp : Prod.mkHom (F.map f ≫ c.derived.hom.app (op M, N)) (𝟙 (F.obj M)) =
          Prod.mkHom (F.map f) (𝟙 (F.obj M)) ≫
            Prod.mkHom (c.derived.hom.app (op M, N)) (𝟙 (F.obj M)) := by simp
      rw [hp, SX.tensor.map_comp]
      simp only [Category.assoc]
      rw [← Category.assoc (c.tensor.hom.app _), ← hn]
      simp only [Category.assoc]
      rw [he, ← F.map_comp, hb]
      simp
      rfl
    · intro M M' N N' a b
      exact c.derived.hom.naturality (Prod.mkHom a.op b)
  · intro c'
    exact signed_shift_laws l E g s SX SY TX TY c'

set_option backward.defeqAttrib.useBackward true
set_option allowUnsafeReducibility true in
attribute [local reducible] podReindexingFunctor podReindexingComplexFunctor
  podReindexingDerivedFunctor podReindexingDerivedFactors

private theorem app_eq_of_iso {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (α β : F ⟶ G) {X Y : A} (e : X ≅ Y)
    (h : α.app X = β.app X) : α.app Y = β.app Y := by
  apply (cancel_epi (F.map e.hom)).1
  exact (α.naturality e.hom).trans
    ((congrArg (fun f ↦ f ≫ G.map e.hom) h).trans (β.naturality e.hom).symm)

-- Bound elaboration of the explicit representative model equations.
private theorem chain_comparison_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c c' : Comparison l E g s SX SY TX TY) (P I : K l E Y s) :
    (c.chain P I).hom = (c'.chain P I).hom := by
  apply HomologicalComplex.hom_ext
  intro r
  apply homComplex_hom_ext
  intro p q hpq
  subst q
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (c.chain_projection P I r p U.unop V.unop.left V.unop.hom f x).trans
    (c'.chain_projection P I r p U.unop V.unop.left V.unop.hom f x).symm

private theorem total_hom_ext (W : Scheme.{u}) (s : Option ℕ)
    (P L I : K l E W s) (f g : (total l E W s).obj (P, L) ⟶ I)
    (h : ∀ (p q : ℤ) (U : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (L.X q).val.obj U),
      (f.f (p + q)).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
            (podReindexingRing l E W s) P L p q (p + q) rfl U x y) =
        (g.f (p + q)).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
            (podReindexingRing l E W s) P L p q (p + q) rfl U x y)) : f = g := by
  exact WeilConjectures.coefficient_total_ext.{u, u + 1, u}
    (ProEt.topology W) (podReindexingRing l E W s) P L I f g h

-- Bound elaboration of the explicit representative model equations.
private theorem tensor_chain_comparison_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c c' : Comparison l E g s SX SY TX TY) (P L : K l E Y s) :
    (c.tensorChain P L).hom = (c'.tensorChain P L).hom := by
  let F₀ := podReindexingComplexFunctor l E g s
  let A := F₀.obj ((total l E Y s).obj (P,L))
  let B := (total l E X s).obj (F₀.obj P,F₀.obj L)
  let e : A ≅ B := c.tensorChain P L
  let e' : A ≅ B := c'.tensorChain P L
  apply (cancel_epi e'.inv).1
  rw [Iso.inv_hom_id]
  apply total_hom_ext l E X s
  intro p q U x y
  let gy := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (podReindexingRing l E Y s) P L p q (p + q) rfl
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x y
  let gx := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
    (podReindexingRing l E X s) (F₀.obj P) (F₀.obj L) p q (p + q) rfl U x y
  let evA (f : A ⟶ A) := (f.f (p+q)).val.app U gy
  have hi : (e'.inv.f (p+q)).val.app U ((e'.hom.f (p+q)).val.app U gy) = gy :=
    congrArg evA e'.hom_inv_id
  have hc : (e.hom.f (p + q)).val.app U gy = gx :=
    c.tensorChain_pure P L p q (p + q) rfl U.unop x y
  have hc' : (e'.hom.f (p + q)).val.app U gy = gx :=
    c'.tensorChain_pure P L p q (p + q) rfl U.unop x y
  have hi' : (e'.inv.f (p + q)).val.app U gx = gy :=
    (congrArg (fun z ↦ (e'.inv.f (p + q)).val.app U z) hc'.symm).trans hi
  change (e.hom.f (p + q)).val.app U ((e'.inv.f (p + q)).val.app U gx) = gx
  exact (congrArg (fun z ↦ (e.hom.f (p + q)).val.app U z) hi').trans hc

-- Bound elaboration of the explicit representative model equations.
private theorem derived_comparison_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c c' : Comparison l E g s SX SY TX TY) : c.derived.hom = c'.derived.hom := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,u}
      (ProEt.topology Y) (podReindexingRing l E Y s)).1
  let Q := podReindexingQ l E Y s
  have hc (P I : K l E Y s) (hI : I.IsKInjective) :
      c.derived.hom.app (op (Q.obj P), Q.obj I) =
        c'.derived.hom.app (op (Q.obj P), Q.obj I) := by
    obtain ⟨hFI, he⟩ := c.derived_model P I hI
    obtain ⟨hFI', he'⟩ := c'.derived_model P I hI
    have hh := chain_comparison_eq l E g s SX SY TX TY c c' P I
    exact he.trans ((congrArg (fun z ↦
      (podReindexingDerivedFunctor l E g s).map
        (@podReindexingHomModel l _ E _ _ _ Y s P I hI).hom ≫
      (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s P I) ≫
      (podReindexingQ l E X s).map z ≫
      (@podReindexingHomModel l _ E _ _ _ X s
        ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I) hFI).inv ≫
      ((podReindexingDerivedHom l E X s).mapIso
        (((podReindexingDerivedFactors l E g s).app P).op.prod
          ((podReindexingDerivedFactors l E g s).app I).symm)).hom) hh).trans he'.symm)
  apply NatTrans.ext
  funext MN
  obtain ⟨M, N⟩ := MN
  let P := Q.objPreimage M.unop
  let N₀ := Q.objPreimage N
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1}
    (podReindexingModules l E Y s)).obj N₀
  let η := (CochainComplex.toKInjectiveResolution.{u + 1}
    (podReindexingModules l E Y s)).app N₀
  have hI : I.IsKInjective := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ N₀
  have hη : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ N₀).2
  have : IsIso (Q.map η) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hη
  let eM : Q.obj P ≅ M.unop := Q.objObjPreimageIso M.unop
  let eN : Q.obj I ≅ N := (asIso (Q.map η)).symm ≪≫ Q.objObjPreimageIso N
  let e := eM.symm.op.prod eN
  exact app_eq_of_iso c.derived.hom c'.derived.hom e (hc P I hI)

-- Bound elaboration of the explicit representative model equations.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem tensor_comparison_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c c' : Comparison l E g s SX SY TX TY) : c.tensor.hom = c'.tensor.hom := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let Q := podReindexingQ l E Y s
  let F := podReindexingDerivedFunctor l E g s
  have hc (P L : K l E Y s)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology Y) (R := podReindexingRing l E Y s) P)
      (hL : CochainComplex.IsKFlatIndependentCoefficients
        (J := ProEt.topology Y) (R := podReindexingRing l E Y s) L) :
      c.tensor.hom.app (Q.obj P, Q.obj L) = c'.tensor.hom.app (Q.obj P, Q.obj L) := by
    obtain ⟨hFP, hFL, he⟩ := c.tensor_model P L hP hL
    obtain ⟨hFP', hFL', he'⟩ := c'.tensor_model P L hP hL
    have hh := tensor_chain_comparison_eq l E g s SX SY TX TY c c' P L
    have heq := he.trans ((congrArg (fun z ↦
      (podReindexingDerivedFactors l E g s).hom.app ((total l E Y s).obj (P,L)) ≫
        (podReindexingQ l E X s).map z ≫
          TX.comparison.hom.app (⟨_,hFP⟩,⟨_,hFL⟩)) hh).trans he'.symm)
    apply (cancel_epi (F.map
      (TY.comparison.hom.app (⟨P, hP⟩, ⟨L, hL⟩)))).1
    let e := SX.tensor.mapIso
      (((podReindexingDerivedFactors l E g s).app P).prod
        ((podReindexingDerivedFactors l E g s).app L))
    apply (cancel_mono e.hom).1
    change (F.map (TY.comparison.hom.app (⟨P, hP⟩, ⟨L, hL⟩)) ≫
        c.tensor.hom.app (Q.obj P, Q.obj L)) ≫ SX.tensor.map
          (Prod.mkHom ((podReindexingDerivedFactors l E g s).hom.app P)
            ((podReindexingDerivedFactors l E g s).hom.app L)) =
      (F.map (TY.comparison.hom.app (⟨P, hP⟩, ⟨L, hL⟩)) ≫
        c'.tensor.hom.app (Q.obj P, Q.obj L)) ≫ SX.tensor.map
          (Prod.mkHom ((podReindexingDerivedFactors l E g s).hom.app P)
            ((podReindexingDerivedFactors l E g s).hom.app L))
    exact (Category.assoc _ _ _).trans
      (heq.trans (Category.assoc _ _ _).symm)
  apply NatTrans.ext
  funext MN
  obtain ⟨M, N⟩ := MN
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Q.objPreimage M)
  obtain ⟨L, q, hL, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Q.objPreimage N)
  have : IsIso (Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  have : IsIso (Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  let eM : Q.obj P ≅ M := asIso (Q.map p) ≪≫ Q.objObjPreimageIso M
  let eN : Q.obj L ≅ N := asIso (Q.map q) ≪≫ Q.objObjPreimageIso N
  let e := eM.prod eN
  exact app_eq_of_iso c.tensor.hom c'.tensor.hom e (hc P L hP hL)

/-- Every product-normalized comparison satisfies the evaluation laws.
Source: Stacks 0GMX, 08J9 and blueprint dual-Tate compatibility, Step 2
(blueprint: lem-pod-reindexing-evaluation-shift-composition).

Proof: the projection and total-tensor normalizations of Comparison identify its
representatives with those of lem-pod-reindexing-hom-resolution-model. On every pure
tensor the two evaluations equal F(f(x)); the chain-transpose lemma and localization
give evaluation. Closed-adjunction bijectivity proves unique; naturality of tensor
and evaluation proves transpose and naturality by uncurrying, as in node Steps 2--5. -/
theorem evaluation_laws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) : EvaluationLaws l E g s SX SY TX TY c := by
  obtain ⟨c₀, h₀, _⟩ := comparison_exists l E g s SX SY TX TY
  have hd := derived_comparison_eq l E g s SX SY TX TY c c₀
  have ht := tensor_comparison_eq l E g s SX SY TX TY c c₀
  rcases h₀ with ⟨he, hu, htr, hn⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hd, ht] using he
  · simpa only [hd, ht] using hu
  · have hi : c.tensor = c₀.tensor := Iso.ext ht
    simpa only [hd, hi] using htr
  · simpa only [hd] using hn

/-- The specified monoidal compositor identifies the product-Hom comparison with
successive reindexing. The tensor equation specifies the same compositor as the
canonical derived monoidal comparison; it is not an independent equivalence.
Source: blueprint dual-Tate compatibility, Steps 1, 2 and 4; Stacks 0GMX, 07A4, 0FPI
(blueprint: lem-pod-reindexing-evaluation-shift-composition).

Proof: compose the site postcomposition functors, whose comparison is identity on
underlying schemes. The finite ring maps commute, and the completed ring maps commute
by all quotient projections. Thus restrictions give the ordinary module compositor.
Apply it termwise and localize to give the displayed model. On pure total-tensor
summands both routes of the tensor equation are identical. K-flat localization and
naturality give that equation for all derived objects. This is the representative
normalization of lem-sfb-ringed-derived-monoidal-comparisons. Apply evaluation twice
to the successive Hom comparison and this tensor equation. The resulting arrow is
F_h F_g(ev). Naturality of the compositor identifies it with F_gh(ev), and uniqueness
from EvaluationLaws proves the Hom equation. This is node Step 8. -/
theorem composition {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Z ⟶ X) [IsIso g] [IsIso h]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    [EssentiallySmall.{u + 1} Z.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s) (SZ : Closed l E Z s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) (TZ : Models l E Z s SZ)
    (cg : Comparison l E g s SX SY TX TY) (ch : Comparison l E h s SZ SX TZ TX)
    (cgh : Comparison l E (h ≫ g) s SZ SY TZ TY) :
    ∃ k : Compositor l E g h s,
      (∀ M N : podReindexingDerived l E Y s,
        cgh.tensor.hom.app (M, N) ≫ SZ.tensor.map
          (Prod.mkHom (k.derived.hom.app M) (k.derived.hom.app N)) =
        k.derived.hom.app (SY.tensor.obj (M, N)) ≫
          (podReindexingDerivedFunctor l E h s).map (cg.tensor.hom.app (M, N)) ≫
          ch.tensor.hom.app ((podReindexingDerivedFunctor l E g s).obj M,
            (podReindexingDerivedFunctor l E g s).obj N)) ∧
      (∀ M N : podReindexingDerived l E Y s,
        cgh.derived.hom.app (op M, N) ≫ (podReindexingDerivedHom l E Z s).map
          (Prod.mkHom (k.derived.inv.app M).op (k.derived.hom.app N)) =
        k.derived.hom.app ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
          (podReindexingDerivedFunctor l E h s).map (cg.derived.hom.app (op M, N)) ≫
          ch.derived.hom.app (op ((podReindexingDerivedFunctor l E g s).obj M),
            (podReindexingDerivedFunctor l E g s).obj N)) := by
  obtain ⟨k, hk⟩ := tensor_compositor_exists l E g h s SX SY SZ TX TY TZ cg ch cgh
  refine ⟨k, hk, ?_⟩
  let F := podReindexingDerivedFunctor l E g s
  let G := podReindexingDerivedFunctor l E h s
  let V := podReindexingDerivedFunctor l E (h ≫ g) s
  let tc : SY.tensor ⋙ (F ⋙ G) ≅ ((F ⋙ G).prod (F ⋙ G)) ⋙ SZ.tensor :=
    NatIso.ofComponents (fun MN ↦ G.mapIso (cg.tensor.app MN) ≪≫
      ch.tensor.app (F.obj MN.1, F.obj MN.2)) (by
        intro MN MN' f
        have hf := cg.tensor.hom.naturality f
        have hg := ch.tensor.hom.naturality ((F.prod F).map f)
        dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj] at hf hg ⊢
        dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
        rw [← Category.assoc, ← G.map_comp, hf, G.map_comp, Category.assoc]
        simpa only [Category.assoc] using
          congrArg (G.map (cg.tensor.hom.app MN) ≫ ·) hg)
  have he := (evaluation_laws l E g s SX SY TX TY cg).evaluation
  have he' := (evaluation_laws l E h s SZ SX TZ TX ch).evaluation
  have hev := (evaluation_laws l E (h ≫ g) s SZ SY TZ TY cgh).evaluation
  intro M N
  apply hom_transport SY.tensor (podReindexingDerivedHom l E Y s)
    (podReindexingDerivedHom l E Z s) SZ V (F ⋙ G) cgh.tensor tc
    (fun M N ↦ cgh.derived.hom.app (op M, N))
    (fun M N ↦ G.map (cg.derived.hom.app (op M, N)) ≫
      ch.derived.hom.app (op (F.obj M), F.obj N)) SY.evaluation hev ?_ k.derived ?_ M N
  · intro M N
    simpa only [tc, NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Functor.comp_obj, Functor.comp_map, Category.assoc] using
      composite_evaluation F G SY.tensor SX.tensor SZ.tensor
      (podReindexingDerivedHom l E Y s) (podReindexingDerivedHom l E X s)
      (podReindexingDerivedHom l E Z s) cg.tensor ch.tensor
      (fun M N ↦ cg.derived.hom.app (op M, N))
      (fun M N ↦ ch.derived.hom.app (op M, N))
      SY.evaluation SX.evaluation SZ.evaluation he he' M N
  · exact hk

/-- Identity reindexing gives the identity Hom and tensor comparisons under their
canonical identity pullback identifications.
Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 0GMX, 0FPI
(blueprint: lem-pod-reindexing-evaluation-shift-composition).

Proof: the site identity comparison induces the restriction map on module sections.
Its termwise localization is the displayed derived identity. The total-tensor pure
sections make the tensor equation the identity. The identity Hom comparison has the
required evaluation; uniqueness in EvaluationLaws makes it the specified comparison.
This is the identity case of node Step 8 and of the monoidal comparison lemma. -/
theorem identity (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    [EssentiallySmall.{u + 1} X.ProEt] (s : Option ℕ)
    (S : Closed l E X s) (T : Models l E X s S)
    (c : Comparison l E (𝟙 X) s S S T T) :
    ∃ k : Identity l E X s,
      (∀ M N : podReindexingDerived l E X s,
        c.tensor.hom.app (M, N) ≫ S.tensor.map
          (Prod.mkHom (k.derived.hom.app M) (k.derived.hom.app N)) =
        k.derived.hom.app (S.tensor.obj (M, N))) ∧
      (∀ M N : podReindexingDerived l E X s,
        c.derived.hom.app (op M, N) ≫ (podReindexingDerivedHom l E X s).map
          (Prod.mkHom (k.derived.inv.app M).op (k.derived.hom.app N)) =
        k.derived.hom.app ((podReindexingDerivedHom l E X s).obj (op M, N))) := by
  obtain ⟨k, hk⟩ := tensor_identity_exists l E X s S T c
  refine ⟨k, hk, ?_⟩
  have he := (evaluation_laws l E (𝟙 X) s S S T T c).evaluation
  intro M N
  have h := hom_transport S.tensor (podReindexingDerivedHom l E X s)
    (podReindexingDerivedHom l E X s) S (podReindexingDerivedFunctor l E (𝟙 X) s)
    (𝟭 _) c.tensor (Iso.refl S.tensor)
    (fun M N ↦ c.derived.hom.app (op M, N)) (fun _ _ ↦ 𝟙 _) S.evaluation he
    (by intro M N; simp) k.derived (by simpa using hk) M N
  simpa only [Category.comp_id] using h

/-- The one-sided flat-term representative normalization already supplied by the
chain-transpose dependency. Source: Stacks 08J9, 06YU
(blueprint: lem-pod-reindexing-evaluation-shift-composition). -/
abbrev TransposeModel (W : Scheme.{u}) (s : Option ℕ)
    (S : Closed l E W s) (T : Models l E W s S) :=
  @OneKFlatChainTransposeData.{u + 1, u, u, u + 2} _ _ (ProEt.topology W) _ _
    (podReindexingRing l E W s) (HasDerivedCategory.standard.{u + 1, u + 2} _) S T

private theorem uncurry_postcompose {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) {A : D} {B : C} {I N : D}
    (x : A ⟶ L.obj B) (j : B ⟶ R.obj I) (e : I ⟶ N) (y : A ⟶ I)
    (h : x ≫ (a.homEquiv B I).symm j = y) :
    x ≫ L.map (j ≫ R.map e) ≫ a.counit.app N = y ≫ e := by
  have hn := a.homEquiv_naturality_right_symm j e
  rw [Adjunction.homEquiv_counit] at hn
  rw [hn, ← Category.assoc, h]

set_option maxHeartbeats 60000 in
-- Elaborate the representative adjunction and localization identifications.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation on flat-term K-flat representatives is ordinary Hom evaluation followed
by the inverse localized augmentation of the K-injective target. The pure formula is
`d.uncurry_pure` applied to the identity of the actual Hom complex.
Source: Stacks 08J9 and blueprint dual-Tate compatibility, Step 2
(blueprint: lem-pod-reindexing-evaluation-shift-composition).

Proof: apply lem-sfb-hom-kflat-chain-transpose with A=Hom(P, I) and its identity map.
The resulting chain map is f tensor x maps to f(x), by uncurry_pure. Its transpose
is the canonical inverse Hom resolution comparison. Postcompose by inverse Q(e)
and use naturality in the target of the adjunction counit. This is exactly node
Steps 1--2, with no K-flatness requirement on Hom(P, I). -/
theorem representative_evaluation (W : Scheme.{u})
    [EssentiallySmall.{u + 1} W.ProEt] (s : Option ℕ)
    (S : Closed l E W s) (T : Models l E W s S) (d : TransposeModel l E W s S T)
    (P I N : K l E W s) (hI : I.IsKInjective)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology W) (R := podReindexingRing l E W s) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology W) (R := podReindexingRing l E W s) (P.X i))
    (e : N ⟶ I) [QuasiIso e] :
    ((@OneKFlatChainTransposeData.comparison.{u + 1, u, u, u + 2} _ _
        (ProEt.topology W) _ _ (podReindexingRing l E W s)
        (HasDerivedCategory.standard.{u + 1, u + 2} _) S T d)
          (hom l E W s P I) P hP hf).hom ≫
      S.tensor.map (Prod.mkHom
        ((@podReindexingHomModel l _ E _ _ _ W s P I hI).inv ≫
          (podReindexingDerivedHom l E W s).map
            (Prod.mkHom (𝟙 ((podReindexingQ l E W s).obj P)).op
              (inv ((podReindexingQ l E W s).map e))))
        (𝟙 ((podReindexingQ l E W s).obj P))) ≫
      S.evaluation ((podReindexingQ l E W s).obj P) ((podReindexingQ l E W s).obj N) =
      (podReindexingQ l E W s).map
        ((@OneKFlatChainTransposeData.uncurry.{u + 1, u, u, u + 2} _ _
          (ProEt.topology W) _ _ (podReindexingRing l E W s)
          (HasDerivedCategory.standard.{u + 1, u + 2} _) S T d)
            (hom l E W s P I) P hP hf I hI (𝟙 _)) ≫
          inv ((podReindexingQ l E W s).map e) := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E W s)
  let Q := podReindexingQ l E W s
  let H := podReindexingDerivedHom l E W s
  let c₁ : Q.obj ((total l E W s).obj (hom l E W s P I, P)) ≅
      S.tensor.obj (Q.obj (hom l E W s P I), Q.obj P) :=
    (@OneKFlatChainTransposeData.comparison.{u + 1, u, u, u + 2} _ _
      (ProEt.topology W) _ _ (podReindexingRing l E W s)
      (HasDerivedCategory.standard.{u + 1, u + 2} _) S T d)
        (hom l E W s P I) P hP hf
  let ev : (total l E W s).obj (hom l E W s P I, P) ⟶ I :=
    (@OneKFlatChainTransposeData.uncurry.{u + 1, u, u, u + 2} _ _
      (ProEt.topology W) _ _ (podReindexingRing l E W s)
      (HasDerivedCategory.standard.{u + 1, u + 2} _) S T d)
        (hom l E W s P I) P hP hf I hI (𝟙 _)
  let j := (@podReindexingHomModel l _ E _ _ _ W s P I hI).inv
  change c₁.hom ≫ S.tensor.map
      (Prod.mkHom (j ≫ H.map (Prod.mkHom (𝟙 (Q.obj P)).op (inv (Q.map e))))
        (𝟙 (Q.obj P))) ≫ S.evaluation (Q.obj P) (Q.obj N) =
    Q.map ev ≫ inv (Q.map e)
  have hj :
      Q.map (((podReindexingHom l E W s).obj (op P)).map
          (CategoryTheory.coefficientHomAugmentation.{u + 1, u, u}
            (ProEt.topology W) (podReindexingRing l E W s) I)) ≫
        (coefficientHomResolutionIso.{u, u + 1, u, u + 2}
          (ProEt.topology W) (podReindexingRing l E W s) P I).inv = j := by
    unfold j podReindexingHomModel
    rfl
  have harg : Q.map (𝟙 (hom l E W s P I)) ≫
      Q.map (((podReindexingHom l E W s).obj (op P)).map
        (CategoryTheory.coefficientHomAugmentation.{u + 1, u, u}
          (ProEt.topology W) (podReindexingRing l E W s) I)) ≫
        (coefficientHomResolutionIso.{u, u + 1, u, u + 2}
          (ProEt.topology W) (podReindexingRing l E W s) P I).inv = j := by
    rw [Q.map_id, Category.id_comp]
    exact hj
  have ht : c₁.hom ≫
      (S.transpose (Q.obj (hom l E W s P I)) (Q.obj P) (Q.obj I)).symm j =
        Q.map ev :=
    (congrArg (fun z ↦ c₁.hom ≫
      (S.transpose (Q.obj (hom l E W s P I)) (Q.obj P) (Q.obj I)).symm z)
        harg).symm.trans
      ((@OneKFlatChainTransposeData.transpose_eq.{u + 1, u, u, u + 2}
        _ _ (ProEt.topology W) _ _ (podReindexingRing l E W s)
        (HasDerivedCategory.standard.{u + 1, u + 2} _) S T d)
          (hom l E W s P I) P I hP hf hI (𝟙 _))
  simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensorRight, Functor.flip, MonoidalCategory.curriedTensor,
    Functor.comp_map, Prod.sectR_map, op_id] using
      uncurry_postcompose (S.adjunction (Q.obj P)) c₁.hom j (inv (Q.map e)) (Q.map ev) ht

/-- The canonical Koszul symmetry data of the closed derived tensor.
Source: Stacks 06YN, 08J9
(blueprint: lem-pod-reindexing-evaluation-shift-composition). -/
abbrev SymmetryModel (W : Scheme.{u}) (s : Option ℕ)
    (S : Closed l E W s) (T : Models l E W s S)
    (β : @SymmetricCategory (podReindexingDerived l E W s) _ S.monoidal) :=
  @RingedDerivedTensorCoherence.{u + 1, u, u, u + 2} _ _ (ProEt.topology W) _ _
    (podReindexingRing l E W s) (HasDerivedCategory.standard.{u + 1, u + 2} _) S T β

private theorem symmetry_models {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (c : TA ⋙ F ≅ (F.prod F) ⋙ TB)
    (sA : ∀ P Q, TA.obj (P, Q) ≅ TA.obj (Q, P))
    (sB : ∀ P Q, TB.obj (P, Q) ≅ TB.obj (Q, P))
    (sBn : ∀ {P Q P' Q'} (f : P ⟶ P') (g : Q ⟶ Q'),
      TB.map (Prod.mkHom f g) ≫ (sB P' Q').hom =
        (sB P Q).hom ≫ TB.map (Prod.mkHom g f))
    {P Q X Y : A} {PU QU XU YU : B}
    (i : X ≅ TA.obj (P, Q)) (i' : Y ≅ TA.obj (Q, P))
    (j : XU ≅ TB.obj (PU, QU)) (j' : YU ≅ TB.obj (QU, PU))
    (aP : F.obj P ≅ PU) (aQ : F.obj Q ≅ QU)
    (k : F.obj X ≅ XU) (k' : F.obj Y ≅ YU)
    (t : X ≅ Y) (tU : XU ≅ YU)
    (hr : F.map i.hom ≫ c.hom.app (P, Q) ≫
      TB.map (Prod.mkHom aP.hom aQ.hom) = k.hom ≫ j.hom)
    (hr' : F.map i'.hom ≫ c.hom.app (Q, P) ≫
      TB.map (Prod.mkHom aQ.hom aP.hom) = k'.hom ≫ j'.hom)
    (hs : i.hom ≫ (sA P Q).hom = t.hom ≫ i'.hom)
    (hsU : j.hom ≫ (sB PU QU).hom = tU.hom ≫ j'.hom)
    (hk : F.map t.hom ≫ k'.hom = k.hom ≫ tU.hom) :
    F.map (sA P Q).hom ≫ c.hom.app (Q, P) =
      c.hom.app (P, Q) ≫ (sB (F.obj P) (F.obj Q)).hom := by
  have : IsIso (Prod.mkHom aQ.hom aP.hom) :=
    (isIso_prod_iff (f := Prod.mkHom aQ.hom aP.hom)).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (F.map i.hom)).1
  apply (cancel_mono (TB.map (Prod.mkHom aQ.hom aP.hom))).1
  calc
    _ = F.map t.hom ≫ (F.map i'.hom ≫ c.hom.app (Q, P) ≫
          TB.map (Prod.mkHom aQ.hom aP.hom)) := by
      simp only [← F.map_comp, ← Category.assoc, hs]
    _ = F.map t.hom ≫ k'.hom ≫ j'.hom := by rw [hr']
    _ = k.hom ≫ tU.hom ≫ j'.hom := by rw [← Category.assoc, hk, Category.assoc]
    _ = k.hom ≫ j.hom ≫ (sB PU QU).hom := by rw [← hsU]
    _ = _ := by
      rw [← Category.assoc, ← hr]
      simp only [Category.assoc]
      rw [sBn]

private theorem symmetry_iso {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (c : TA ⋙ F ≅ (F.prod F) ⋙ TB)
    (sA : ∀ P Q, TA.obj (P, Q) ≅ TA.obj (Q, P))
    (sB : ∀ P Q, TB.obj (P, Q) ≅ TB.obj (Q, P))
    (sAn : ∀ {P Q P' Q'} (f : P ⟶ P') (g : Q ⟶ Q'),
      TA.map (Prod.mkHom f g) ≫ (sA P' Q').hom =
        (sA P Q).hom ≫ TA.map (Prod.mkHom g f))
    (sBn : ∀ {P Q P' Q'} (f : P ⟶ P') (g : Q ⟶ Q'),
      TB.map (Prod.mkHom f g) ≫ (sB P' Q').hom =
        (sB P Q).hom ≫ TB.map (Prod.mkHom g f))
    {P Q M N : A} (e : P ≅ M) (e' : Q ≅ N)
    (h : F.map (sA P Q).hom ≫ c.hom.app (Q, P) =
      c.hom.app (P, Q) ≫ (sB (F.obj P) (F.obj Q)).hom) :
    F.map (sA M N).hom ≫ c.hom.app (N, M) =
      c.hom.app (M, N) ≫ (sB (F.obj M) (F.obj N)).hom := by
  have : IsIso (Prod.mkHom e.hom e'.hom) :=
    (isIso_prod_iff (f := Prod.mkHom e.hom e'.hom)).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (F.map (TA.map (Prod.mkHom e.hom e'.hom)))).1
  calc
    _ = F.map (sA P Q).hom ≫
        (F.map (TA.map (Prod.mkHom e'.hom e.hom)) ≫ c.hom.app (N, M)) := by
      rw [← Category.assoc, ← F.map_comp, sAn, F.map_comp]
      simp only [Category.assoc]
    _ = F.map (sA P Q).hom ≫ c.hom.app (Q, P) ≫
        TB.map (Prod.mkHom (F.map e'.hom) (F.map e.hom)) := by
      have hn := c.hom.naturality (Prod.mkHom e'.hom e.hom)
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      exact congrArg (F.map (sA P Q).hom ≫ ·) hn
    _ = c.hom.app (P, Q) ≫ (sB (F.obj P) (F.obj Q)).hom ≫
        TB.map (Prod.mkHom (F.map e'.hom) (F.map e.hom)) := by
      rw [← Category.assoc, h, Category.assoc]
    _ = c.hom.app (P, Q) ≫ TB.map (Prod.mkHom (F.map e.hom) (F.map e'.hom)) ≫
        (sB (F.obj M) (F.obj N)).hom := by rw [← sBn]
    _ = _ := by
      have hn := c.hom.naturality (Prod.mkHom e.hom e'.hom)
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      simpa only [Category.assoc] using
        congrArg (· ≫ (sB (F.obj M) (F.obj N)).hom) hn.symm

private theorem symmetry_chain {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) (P L : K l E Y s)
    (t : (total l E Y s).obj (P, L) ≅ (total l E Y s).obj (L, P))
    (tX : (total l E X s).obj
        ((podReindexingComplexFunctor l E g s).obj P,
          (podReindexingComplexFunctor l E g s).obj L) ≅
      (total l E X s).obj ((podReindexingComplexFunctor l E g s).obj L,
        (podReindexingComplexFunctor l E g s).obj P))
    (ht : ∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k)
      (U : Y.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (L.X q).val.obj U),
      (t.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
          (podReindexingRing l E Y s) P L p q k h U x y) =
        (p * q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology Y) (podReindexingRing l E Y s) L P q p k h' U y x)
    (htX : ∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k)
      (U : X.ProEtᵒᵖ)
      (x : (((podReindexingComplexFunctor l E g s).obj P).X p).val.obj U)
      (y : (((podReindexingComplexFunctor l E g s).obj L).X q).val.obj U),
      (tX.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (podReindexingRing l E X s) ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj L) p q k h U x y) =
        (p * q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology X) (podReindexingRing l E X s)
          ((podReindexingComplexFunctor l E g s).obj L)
          ((podReindexingComplexFunctor l E g s).obj P) q p k h' U y x) :
    (podReindexingComplexFunctor l E g s).map t.hom ≫ (c.tensorChain L P).hom =
      (c.tensorChain P L).hom ≫ tX.hom := by
  let R := podReindexingComplexFunctor l E g s
  apply (cancel_epi (c.tensorChain P L).inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply total_hom_ext l E X s
  intro p q U x y
  let gy := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (podReindexingRing l E Y s) P L p q (p + q) rfl
      (op ((proEtaleIsoPostcompose g).obj U.unop)) x y
  let gx := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
    (podReindexingRing l E X s) (R.obj P) (R.obj L) p q (p + q) rfl U x y
  have hi : ((c.tensorChain P L).inv.f (p + q)).val.app U gx = gy := by
    have hc : ((c.tensorChain P L).hom.f (p + q)).val.app U gy = gx :=
      c.tensorChain_pure P L p q (p + q) rfl U.unop x y
    have he : ((c.tensorChain P L).inv.f (p + q)).val.app U
        (((c.tensorChain P L).hom.f (p + q)).val.app U gy) = gy :=
      congrArg (fun f ↦ (f.f (p + q)).val.app U gy) (c.tensorChain P L).hom_inv_id
    exact (congrArg (fun z ↦ ((c.tensorChain P L).inv.f (p + q)).val.app U z)
      hc.symm).trans he
  change ((c.tensorChain L P).hom.f (p + q)).val.app U
    ((t.hom.f (p + q)).val.app
      (op ((proEtaleIsoPostcompose g).obj U.unop))
      (((c.tensorChain P L).inv.f (p + q)).val.app U gx)) = _
  rw [hi]
  let gy' := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
    (podReindexingRing l E Y s) L P q p (p + q) (by omega)
      (op ((proEtaleIsoPostcompose g).obj U.unop)) y x
  let gx' := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
    (podReindexingRing l E X s) (R.obj L) (R.obj P) q p (p + q) (by omega) U y x
  calc
    _ = ((c.tensorChain L P).hom.f (p + q)).val.app U
        ((p * q).negOnePow • gy') :=
      congrArg (((c.tensorChain L P).hom.f (p + q)).val.app U)
        (ht p q (p + q) rfl (by omega) _ x y)
    _ = (p * q).negOnePow •
        ((c.tensorChain L P).hom.f (p + q)).val.app U gy' := map_zsmul_unit _ _ _
    _ = (p * q).negOnePow • gx' :=
      congrArg ((p * q).negOnePow • ·)
        (c.tensorChain_pure L P q p (p + q) (by omega) U.unop y x)
    _ = _ := (htX p q (p + q) rfl (by omega) U x y).symm

private theorem symmetry_base {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (βX : @SymmetricCategory (podReindexingDerived l E X s) _ SX.monoidal)
    (βY : @SymmetricCategory (podReindexingDerived l E Y s) _ SY.monoidal)
    (_hX : SymmetryModel l E X s SX TX βX) (_hY : SymmetryModel l E Y s SY TY βY)
    (P L : K l E Y s)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) P)
    (hL : CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s) L) :
    let F := podReindexingDerivedFunctor l E g s
    let Q := podReindexingQ l E Y s
    F.map (βY.braiding (Q.obj P) (Q.obj L)).hom ≫
        c.tensor.hom.app (Q.obj L, Q.obj P) =
      c.tensor.hom.app (Q.obj P, Q.obj L) ≫
        (βX.braiding (F.obj (Q.obj P)) (F.obj (Q.obj L))).hom := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let F := podReindexingDerivedFunctor l E g s
  let R := podReindexingComplexFunctor l E g s
  let QY := podReindexingQ l E Y s
  let QX := podReindexingQ l E X s
  have bnX {P Q P' Q' : podReindexingDerived l E X s} (f : P ⟶ P') (h : Q ⟶ Q') :
      SX.tensor.map (Prod.mkHom f h) ≫ (βX.braiding P' Q').hom =
        (βX.braiding P Q).hom ≫ SX.tensor.map (Prod.mkHom h f) := by
    exact @BraidedCategory.braiding_naturality _ _ SX.monoidal βX.toBraidedCategory
      _ _ _ _ f h
  obtain ⟨hRP, hRL, hρ⟩ := c.tensor_model P L hP hL
  obtain ⟨_, _, hρ'⟩ := c.tensor_model L P hL hP
  obtain ⟨t, ht, hs⟩ := _hY.symmetry_model P L hP hL
  obtain ⟨tX, htX, hsX⟩ := _hX.symmetry_model (R.obj P) (R.obj L) hRP hRL
  have hchain := symmetry_chain l E g s SX SY TX TY c P L t tX ht htX
  apply symmetry_models F SY.tensor SX.tensor c.tensor
    (fun P Q ↦ βY.braiding P Q) (fun P Q ↦ βX.braiding P Q) bnX
    (TY.iso _ _ SY P L hP hL) (TY.iso _ _ SY L P hL hP)
    (TX.iso _ _ SX (R.obj P) (R.obj L) hRP hRL)
    (TX.iso _ _ SX (R.obj L) (R.obj P) hRL hRP)
    ((podReindexingDerivedFactors l E g s).app P)
    ((podReindexingDerivedFactors l E g s).app L)
    (((podReindexingDerivedFactors l E g s).app _) ≪≫ QX.mapIso (c.tensorChain P L))
    (((podReindexingDerivedFactors l E g s).app _) ≪≫ QX.mapIso (c.tensorChain L P))
    (QY.mapIso t) (QX.mapIso tX)
  · dsimp only [CoefficientTensorModels.iso, Iso.app_hom, Iso.trans_hom,
      Functor.mapIso_hom, F, QX, QY, R, Functor.comp_obj, Functor.prod_obj,
      coefficientKFlatInclusion, ObjectProperty.ι_obj, total] at hρ ⊢
    exact hρ.trans (Category.assoc _ _ _).symm
  · dsimp only [CoefficientTensorModels.iso, Iso.app_hom, Iso.trans_hom,
      Functor.mapIso_hom, F, QX, QY, R, Functor.comp_obj, Functor.prod_obj,
      coefficientKFlatInclusion, ObjectProperty.ι_obj, total] at hρ' ⊢
    exact hρ'.trans (Category.assoc _ _ _).symm
  · exact hs
  · exact hsX
  · have hn := (podReindexingDerivedFactors l E g s).hom.naturality t.hom
    change F.map (QY.map t.hom) ≫
        ((podReindexingDerivedFactors l E g s).hom.app _ ≫
          QX.map (c.tensorChain L P).hom) =
      ((podReindexingDerivedFactors l E g s).hom.app _ ≫
        QX.map (c.tensorChain P L).hom) ≫ QX.map tX.hom
    change F.map (QY.map t.hom) ≫
        (podReindexingDerivedFactors l E g s).hom.app _ =
      (podReindexingDerivedFactors l E g s).hom.app _ ≫ QX.map (R.map t.hom) at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    exact congrArg ((podReindexingDerivedFactors l E g s).hom.app _ ≫ ·)
      ((QX.map_comp _ _).symm.trans
        ((congrArg QX.map hchain).trans (QX.map_comp _ _)))

/-- Reversing the Hom-first order to M-first order uses the same Koszul symmetry
on both sides of the evaluation equation.
Source: blueprint dual-Tate compatibility, Step 2; Stacks 06YN, 08J9
(blueprint: lem-pod-reindexing-evaluation-shift-composition).

Proof: on total-tensor generators the two maps swap degrees p and r and multiply
by (-1)^(p*r). The coefficient reindexing is additive and fixes integer signs,
so both composites coincide. Sheafification, the direct-sum total, and K-flat
localization give the symmetry equation. Precompose the Hom-first evaluation
formula with this symmetry; it becomes exactly the M-first formula of the node. -/
theorem symmetry {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (βX : @SymmetricCategory (podReindexingDerived l E X s) _ SX.monoidal)
    (βY : @SymmetricCategory (podReindexingDerived l E Y s) _ SY.monoidal)
    (_hX : SymmetryModel l E X s SX TX βX) (_hY : SymmetryModel l E Y s SY TY βY) :
    ∀ M N : podReindexingDerived l E Y s,
      (podReindexingDerivedFunctor l E g s).map (βY.braiding M N).hom ≫
        c.tensor.hom.app (N, M) =
      c.tensor.hom.app (M, N) ≫
        (βX.braiding ((podReindexingDerivedFunctor l E g s).obj M)
          ((podReindexingDerivedFunctor l E g s).obj N)).hom := by
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  let F := podReindexingDerivedFunctor l E g s
  let QY := podReindexingQ l E Y s
  have bnX {P Q P' Q' : podReindexingDerived l E X s} (f : P ⟶ P') (h : Q ⟶ Q') :
      SX.tensor.map (Prod.mkHom f h) ≫ (βX.braiding P' Q').hom =
        (βX.braiding P Q).hom ≫ SX.tensor.map (Prod.mkHom h f) := by
    exact @BraidedCategory.braiding_naturality _ _ SX.monoidal βX.toBraidedCategory
      _ _ _ _ f h
  have bnY {P Q P' Q' : podReindexingDerived l E Y s} (f : P ⟶ P') (h : Q ⟶ Q') :
      SY.tensor.map (Prod.mkHom f h) ≫ (βY.braiding P' Q').hom =
        (βY.braiding P Q).hom ≫ SY.tensor.map (Prod.mkHom h f) := by
    exact @BraidedCategory.braiding_naturality _ _ SY.monoidal βY.toBraidedCategory
      _ _ _ _ f h
  intro M N
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (QY.objPreimage M)
  obtain ⟨L, q, hL, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (QY.objPreimage N)
  have : IsIso (QY.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hp
  have : IsIso (QY.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  let eM : QY.obj P ≅ M := asIso (QY.map p) ≪≫ QY.objObjPreimageIso M
  let eN : QY.obj L ≅ N := asIso (QY.map q) ≪≫ QY.objObjPreimageIso N
  exact symmetry_iso F SY.tensor SX.tensor c.tensor
    (fun P Q ↦ βY.braiding P Q) (fun P Q ↦ βX.braiding P Q) bnY bnX eM eN
      (symmetry_base l E g s SX SY TX TY c βX βY _hX _hY P L hP hL)

end WeilConjectures.PodReindexingCoherence

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.IntegralSystemRealization.Pull.IntegralPullEvaluationCochainSquare
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralScalarPullbackMateNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain

/-! # The pullback evaluation quotient square

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 0941
(blueprint: lem-sf-integral-pull-evaluation-quotient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors pullbackTensorDerivedEvaluation
  pullbackTensorInverseEvaluationComplex pullbackTensorLevelIntrinsic
  constantSheaf presheafToSheaf Functor.leftAdjoint
  sfIntrinsicPullback coefficientSequenceEvaluation pullbackTensorSequenceInverse
attribute [local implicit_reducible]
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived coefficientSequenceHasDerived scalarReductionTargetDerived
  coefficientFiniteHasDerived proEtaleRingModules_hasDerivedCategory

section Pasting
universe a v w z
variable {ι : Type z} {S : ι → Type a} {C : ι → ℕ → Type a}
  [∀ W, Category.{v} (S W)] [∀ W k, Category.{v} (C W k)]
  [∀ W, Abelian (S W)] [∀ W k, Abelian (C W k)]
  [∀ W, HasDerivedCategory.{w} (S W)] [∀ W k, HasDerivedCategory.{w} (C W k)]
  {X Y : ι} (n : ℕ) (I : S Y ⥤ S X)
  (V : ∀ W k, S W ⥤ C W k) (F : ∀ k, C Y k ⥤ C X k)
  (R : ∀ W, C W n ⥤ C W (n + 1))
  [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [∀ W k, (V W k).Additive]
  [∀ W k, PreservesFiniteLimits (V W k)] [∀ W k, PreservesFiniteColimits (V W k)]
  [∀ k, (F k).Additive]
  [∀ k, PreservesFiniteLimits (F k)] [∀ k, PreservesFiniteColimits (F k)]
  [∀ W, (R W).Additive]
  [∀ W, PreservesFiniteLimits (R W)] [∀ W, PreservesFiniteColimits (R W)]

private theorem evaluation_pasting
    (α : ∀ k, I.mapDerivedCategory ⋙ (V X k).mapDerivedCategory ⟶
      (V Y k).mapDerivedCategory ⋙ (F k).mapDerivedCategory)
    (τ : ∀ W, (V W (n + 1)).mapDerivedCategory ⟶
      (V W n).mapDerivedCategory ⋙ (R W).mapDerivedCategory)
    (T : ∀ W, V W (n + 1) ⟶ V W n ⋙ R W)
    (χ : ∀ k, I.mapHomologicalComplex (.up ℤ) ⋙
        (V X k).mapHomologicalComplex (.up ℤ) ⟶
      (V Y k).mapHomologicalComplex (.up ℤ) ⋙ (F k).mapHomologicalComplex (.up ℤ))
    (δ₀ : R Y ⋙ F (n + 1) ⟶ F n ⋙ R X)
    (δ : (R Y).mapDerivedCategory ⋙ (F (n + 1)).mapDerivedCategory ⟶
      (F n).mapDerivedCategory ⋙ (R X).mapDerivedCategory)
    (hα_normal : ∀ k (P : CochainComplex (S Y) ℤ),
      (α k).app (DerivedCategory.Q.obj P) ≫
          (F k).mapDerivedCategory.map ((V Y k).mapDerivedCategoryFactors.hom.app P) ≫
          (F k).mapDerivedCategoryFactors.hom.app
            (((V Y k).mapHomologicalComplex (.up ℤ)).obj P) =
        (V X k).mapDerivedCategory.map (I.mapDerivedCategoryFactors.hom.app P) ≫
          (V X k).mapDerivedCategoryFactors.hom.app
            ((I.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((χ k).app P))
    (hτ_normal : ∀ W (P : CochainComplex (S W) ℤ),
      (τ W).app (DerivedCategory.Q.obj P) ≫
          (R W).mapDerivedCategory.map ((V W n).mapDerivedCategoryFactors.hom.app P) ≫
          (R W).mapDerivedCategoryFactors.hom.app
            (((V W n).mapHomologicalComplex (.up ℤ)).obj P) =
        (V W (n + 1)).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (T W) (.up ℤ)).app P))
    (hδ_normal : ∀ (P : CochainComplex (C Y n) ℤ),
      δ.app (DerivedCategory.Q.obj P) ≫
          (R X).mapDerivedCategory.map ((F n).mapDerivedCategoryFactors.hom.app P) ≫
          (R X).mapDerivedCategoryFactors.hom.app
            (((F n).mapHomologicalComplex (.up ℤ)).obj P) =
        (F (n + 1)).mapDerivedCategory.map ((R Y).mapDerivedCategoryFactors.hom.app P) ≫
          (F (n + 1)).mapDerivedCategoryFactors.hom.app
            (((R Y).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex δ₀ (.up ℤ)).app P))
    (hcochain : ∀ P : CochainComplex (S Y) ℤ,
      (NatTrans.mapHomologicalComplex (T X) (.up ℤ)).app
          ((I.mapHomologicalComplex (.up ℤ)).obj P) ≫
          ((R X).mapHomologicalComplex (.up ℤ)).map ((χ n).app P) =
        (χ (n + 1)).app P ≫
          ((F (n + 1)).mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (T Y) (.up ℤ)).app P) ≫
          (NatTrans.mapHomologicalComplex δ₀ (.up ℤ)).app
            (((V Y n).mapHomologicalComplex (.up ℤ)).obj P))
    (M : DerivedCategory (S Y)) :
    (τ X).app (I.mapDerivedCategory.obj M) ≫
        (R X).mapDerivedCategory.map ((α n).app M) =
      (α (n + 1)).app M ≫ (F (n + 1)).mapDerivedCategory.map ((τ Y).app M) ≫
        δ.app ((V Y n).mapDerivedCategory.obj M) := by
  let a : I.mapDerivedCategory ⋙ (V X (n + 1)).mapDerivedCategory ⟶
      (V Y n).mapDerivedCategory ⋙
        (F n).mapDerivedCategory ⋙ (R X).mapDerivedCategory :=
    Functor.whiskerLeft (I.mapDerivedCategory) (τ X) ≫
      Functor.whiskerRight (α n) ((R X).mapDerivedCategory)
  let b : I.mapDerivedCategory ⋙ (V X (n + 1)).mapDerivedCategory ⟶
      (V Y n).mapDerivedCategory ⋙
        (F n).mapDerivedCategory ⋙ (R X).mapDerivedCategory :=
    α (n + 1) ≫ Functor.whiskerRight (τ Y) ((F (n + 1)).mapDerivedCategory) ≫
      Functor.whiskerLeft ((V Y n).mapDerivedCategory) δ
  have hab : a = b := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (S Y) (.up ℤ))
    intro P
    let Pc := (I.mapHomologicalComplex (.up ℤ)).obj P
    let Pn := ((V Y n).mapHomologicalComplex (.up ℤ)).obj P
    let v := (R X).mapDerivedCategory.mapIso
        ((F n).mapDerivedCategory.mapIso ((V Y n).mapDerivedCategoryFactors.app P)) ≪≫
      (R X).mapDerivedCategory.mapIso ((F n).mapDerivedCategoryFactors.app Pn) ≪≫
      (R X).mapDerivedCategoryFactors.app (((F n).mapHomologicalComplex (.up ℤ)).obj Pn)
    apply (cancel_mono v.hom).mp
    let hI := I.mapDerivedCategoryFactors.hom.app P
    let eX (k : ℕ) := (V X k).mapDerivedCategoryFactors.hom.app Pc
    let eY (k : ℕ) := (V Y k).mapDerivedCategoryFactors.hom.app P
    let c (k : ℕ) := (χ k).app P
    let tX := (NatTrans.mapHomologicalComplex
      (T X) (.up ℤ)).app Pc
    let tY := (NatTrans.mapHomologicalComplex
      (T Y) (.up ℤ)).app P
    let d := (NatTrans.mapHomologicalComplex δ₀ (.up ℤ)).app Pn
    have hα (k : ℕ) := hα_normal k P
    have htX := hτ_normal X Pc
    have htY := hτ_normal Y P
    have hδ := hδ_normal Pn
    have hnatX := (τ X).naturality hI
    have hnatδ := δ.naturality (eY n)
    have hnatR := (R X).mapDerivedCategoryFactors_hom_naturality (c n)
    have hnatF := (F (n + 1)).mapDerivedCategoryFactors_hom_naturality tY
    dsimp only [Functor.comp_map] at hnatX hnatδ
    have ha : a.app (DerivedCategory.Q.obj P) ≫ v.hom =
        (V X (n + 1)).mapDerivedCategory.map hI ≫ eX (n + 1) ≫
          DerivedCategory.Q.map
            (tX ≫ ((R X).mapHomologicalComplex (.up ℤ)).map (c n)) := by
      dsimp only [a, v, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
      simp only [Category.assoc]
      rw [hα n]
      simp only [Functor.map_comp, Category.assoc]
      erw [hnatR]
      rw [← Category.assoc]
      erw [← hnatX]
      simp only [Category.assoc]
      erw [reassoc_of% htX]
    have hb : b.app (DerivedCategory.Q.obj P) ≫ v.hom =
        (V X (n + 1)).mapDerivedCategory.map hI ≫ eX (n + 1) ≫
          DerivedCategory.Q.map
            (c (n + 1) ≫ ((F (n + 1)).mapHomologicalComplex (.up ℤ)).map tY ≫ d) := by
      dsimp only [b, v, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      simp only [Category.assoc]
      rw [← reassoc_of% hnatδ, hδ]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
      simp only [Category.assoc]
      rw [htY]
      simp only [Functor.map_comp, Category.assoc]
      erw [reassoc_of% hnatF]
      rw [reassoc_of% (hα (n + 1))]
    rw [ha, hb, hcochain P]
  exact congr_app hab M

end Pasting

private theorem evaluation_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (pullbackTensorDerivedEvaluation l E f n).hom.app (DerivedCategory.Q.obj P) ≫
        (finiteDerivedPullback l E n f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app P) ≫
        (Functor.mapDerivedCategoryFactors
          (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)).hom.app _ =
      (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P) ≫
        (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((integralPullEvaluationComplex l E f n).hom.app P) := by
  have h : pullbackTensorDerivedEvaluationNormalization l E f n
      (pullbackTensorDerivedEvaluation l E f n) := by
    unfold pullbackTensorDerivedEvaluation pullbackTensorUniqueChoice
    exact (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose_spec
  simpa only [pullbackTensorDerivedEvaluationNormalization, integralPullEvaluationComplex,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc] using h P

private theorem transition_normalization (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (coefficientSequenceDerivedTransition l E W h).app (DerivedCategory.Q.obj P) ≫
        (normalizedDVRRes l E W h).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P) ≫
        (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P) =
      (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (coefficientSequenceTransition l E W h) (.up ℤ)).app P) := by
  dsimp only [coefficientSequenceDerivedTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  change ((coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app P ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (coefficientSequenceTransition l E W h) (.up ℤ)).app P) ≫
    (Functor.mapDerivedCategoryFactors
      (coefficientSequenceEvaluation l E W n ⋙ normalizedDVRModuleRes l E W h)).inv.app P) ≫
    (Functor.mapDerivedCategoryFactors
      (coefficientSequenceEvaluation l E W n ⋙ normalizedDVRModuleRes l E W h)).hom.app P = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem ordinary_restriction_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃ r₀ : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n),
      HEq r₀ (proEtaleCoefficientDirectImageComparison f
        (Padic.coefficientExtensionTransition l E (n + 1))).symm := by
  rw [← originRestrictionEquality l E X n, ← originRestrictionEquality l E Y n]
  exact ⟨(proEtaleCoefficientDirectImageComparison f
    (Padic.coefficientExtensionTransition l E (n + 1))).symm, HEq.rfl⟩

/-- Pullback evaluation respects adjacent quotient transitions, with the scalar
comparison obtained by transposing the published restricted direct-image map.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941 and 07A7
(blueprint: lem-sf-integral-pull-evaluation-quotient-square).

Proof: express both transitions on strict cochain representatives by horizontal
restriction on the sequence site. The ordinary evaluation/pullback map is the
mate of the identity on direct-image sections. The scalar-restriction/direct-image
comparison is also the identity on sections. Its mate is therefore precisely the
restriction/pullback comparison appearing here. At every component both routes
apply the same coefficient quotient to a pulled-back section. The equality is
compatible with differentials and hence descends through exact localization.
The normalization of pullbackTensorDerivedEvaluation fixes the localized map;
the K-injective normalization of sfDerivedImageRestriction fixes its mate.
Consequently the identity holds for every derived system, without any inference
from equality at evaluations. Zero objects and n = 0 use the same section formula;
no coefficient-flatness or normalization of the input is needed. -/
theorem integralPullEvaluation_quotientSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ)
    (r : normalizedDVRRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRRes l E Y (Nat.le_succ n))
    (hr : HEq r
      (sfDerivedImageRestriction f (Padic.coefficientExtensionTransition l E (n + 1))))
    (M : System l E Y) :
    (coefficientSequenceDerivedTransition l E X (Nat.le_succ n)).app ((pull l E f).obj M) ≫
      (normalizedDVRRes l E X (Nat.le_succ n)).map
        ((pullbackTensorDerivedEvaluation l E f n).hom.app M) =
    (pullbackTensorDerivedEvaluation l E f (n + 1)).hom.app M ≫
      (finiteDerivedPullback l E (n + 1) f).map
        ((coefficientSequenceDerivedTransition l E Y (Nat.le_succ n)).app M) ≫
      ((mateEquiv (finiteAdj l E f n) (finiteAdj l E f (n + 1))).symm
        (TwoSquare.mk _ _ _ _ r.inv)).app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M) := by
  obtain ⟨r₀, hr₀⟩ := ordinary_restriction_exists l E f n
  let I := pullbackTensorSequenceInverse l E f
  let F (k : ℕ) : normalizedDVRModules l E Y k ⥤ normalizedDVRModules l E X k :=
    sfIntrinsicPullback (finiteCoefficientRing l E (k + 1)) f
  let V (W : Scheme.{u}) (k : ℕ) := coefficientSequenceEvaluation l E W k
  let R (W : Scheme.{u}) := normalizedDVRModuleRes l E W (Nat.le_succ n)
  let : ∀ k, (F k).Additive := fun k ↦
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (k + 1)) f
  let : ∀ k, PreservesFiniteLimits (F k) := fun k ↦
    sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (k + 1)) f
  let : ∀ k, PreservesFiniteColimits (F k) := fun k ↦
    sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (k + 1)) f
  let : ∀ W k, (V W k).Additive := fun W k ↦
    coefficientSequenceEvaluation_additiveInstance l E W k
  let : ∀ W k, PreservesFiniteLimits (V W k) := fun W k ↦
    coefficientSequenceEvaluation_limits l E W k
  let : ∀ W k, PreservesFiniteColimits (V W k) := fun W k ↦
    coefficientSequenceEvaluation_colimits l E W k
  let : ∀ W, (R W).Additive := fun W ↦
    normalizedDVRModuleRes_additive l E W (Nat.le_succ n)
  let : ∀ W, PreservesFiniteLimits (R W) := fun W ↦
    normalizedDVRModuleRes_limits l E W (Nat.le_succ n)
  let : ∀ W, PreservesFiniteColimits (R W) := fun W ↦
    normalizedDVRModuleRes_colimits l E W (Nat.le_succ n)
  let δ₀ := ((mateEquiv
    (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
    (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2)))).symm
      (TwoSquare.mk _ _ _ _ r₀.inv))
  let δ := ((mateEquiv (finiteAdj l E f n) (finiteAdj l E f (n + 1))).symm
    (TwoSquare.mk _ _ _ _ r.inv))
  let α (k : ℕ) : I.mapDerivedCategory ⋙ (V X k).mapDerivedCategory ⟶
      (V Y k).mapDerivedCategory ⋙ (F k).mapDerivedCategory :=
    (pullbackTensorDerivedEvaluation l E f k).hom
  let τ (W : Scheme.{u}) : (V W (n + 1)).mapDerivedCategory ⟶
      (V W n).mapDerivedCategory ⋙ (R W).mapDerivedCategory :=
    coefficientSequenceDerivedTransition l E W (Nat.le_succ n)
  exact evaluation_pasting (S := coefficientSequenceModules l E)
    (C := normalizedDVRModules l E) (X := X) (Y := Y) n I V F R α τ
    (fun W ↦ coefficientSequenceTransition l E W (Nat.le_succ n))
    (fun k ↦ (integralPullEvaluationComplex l E f k).hom) δ₀ δ
    (evaluation_normalization l E f)
    (fun W P ↦ transition_normalization l E W (Nat.le_succ n) P)
    (integralScalarPullback_mateNormalization l E f n r₀ hr₀ r hr)
    (integralPullEvaluation_cochainSquare l E f n r₀ hr₀) M

end WeilConjectures.IntegralSystemRealization

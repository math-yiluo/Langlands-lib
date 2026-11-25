/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.IntegralSystemRealization.Pull.IntegralPullEvaluationDirectTransitionSquare

/-! The degreewise module-map core of the ordinary pullback evaluation square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]


private theorem evaluation_transition_mate
    {A B C D C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {L : C ⥤ D} {G : D ⥤ C}
    {L' : C' ⥤ D'} {G' : D' ⥤ C'}
    (adj : F ⊣ R) (a : L ⊣ G) (b : L' ⊣ G')
    {e : A ⥤ C} {v : B ⥤ D} {e' : A ⥤ C'} {v' : B ⥤ D'}
    {S : C ⥤ C'} {T : D ⥤ D'}
    (q : F ⋙ v ≅ e ⋙ L) (q' : F ⋙ v' ≅ e' ⋙ L')
    (d : R ⋙ e ⟶ v ⋙ G) (d' : R ⋙ e' ⟶ v' ⋙ G')
    (hq : (mateEquiv adj a q.inv) = d)
    (hq' : (mateEquiv adj b q'.inv) = d')
    (t : e' ⟶ e ⋙ S) (s : v' ⟶ v ⋙ T) (r : G ⋙ S ⟶ T ⋙ G')
    (h : ∀ N, t.app (R.obj N) ≫ S.map (d.app N) ≫ r.app (v.obj N) =
      d'.app N ≫ G'.map (s.app N)) (M : A) :
    s.app (F.obj M) ≫ T.map (q.hom.app M) =
      q'.hom.app M ≫ L'.map (t.app M) ≫
        ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r)).app (e.obj M) := by
  apply (cancel_epi (q'.inv.app M)).mp
  apply (cancel_mono (T.map (q.inv.app M))).mp
  simp only [Category.assoc, ← T.map_comp, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc]
  dsimp only [Functor.comp_obj]
  erw [T.map_id, Category.comp_id]
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  have hu := unit_mateEquiv adj a q.inv M
  change e.map (adj.unit.app M) ≫
    ((mateEquiv adj a q.inv)).app (F.obj M) =
      a.unit.app (e.obj M) ≫ G.map (q.inv.app M) at hu
  rw [hq] at hu
  have hu' := unit_mateEquiv adj b q'.inv M
  change e'.map (adj.unit.app M) ≫
    ((mateEquiv adj b q'.inv)).app (F.obj M) =
      b.unit.app (e'.obj M) ≫ G'.map (q'.inv.app M) at hu'
  rw [hq'] at hu'
  have hδ : b.homEquiv _ _
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r)).app (e.obj M)) =
        S.map (a.unit.app (e.obj M)) ≫ r.app (L.obj (e.obj M)) := by
    rw [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ r) (e.obj M)).symm
  dsimp only [Functor.comp_obj] at hδ
  rw [hδ, Adjunction.homEquiv_unit, ← hu']
  simp only [Category.assoc]
  have hn := r.naturality (q.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn, ← S.map_comp_assoc, ← hu, S.map_comp]
  have ht := t.naturality (adj.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ht
  simp only [Category.assoc]
  rw [← reassoc_of% ht]
  rw [h]

private theorem evaluation_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {R : D ⥤ C} {P V : C' ⥤ D'} {U : D' ⥤ C'}
    (a : F ⊣ R) (b : P ⊣ U) (c : V ⊣ U)
    (e₀ : C ⥤ C') (e₁ : D ⥤ D')
    (i : e₀ ⋙ P ≅ F ⋙ e₁) (j : P ≅ V) (d : R ⋙ e₀ ⟶ e₁ ⋙ U)
    (hi : ∀ M, b.homEquiv _ _ (i.hom.app M) =
      e₀.map (a.unit.app M) ≫ d.app (F.obj M))
    (hj : ∀ M, b.unit.app M ≫ U.map (j.hom.app M) = c.unit.app M) :
    (mateEquiv a c (i.symm ≪≫ Functor.isoWhiskerLeft e₀ j).inv) = d := by
  apply (mateEquiv a c).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext M
  apply (c.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp]
  rw [← hj]
  simp only [Category.assoc, ← U.map_comp_assoc, j.hom_inv_id_app, U.map_id,
    Category.id_comp]
  change b.homEquiv _ _ (i.hom.app M) = _
  rw [hi, Adjunction.homEquiv_unit]
  exact unit_mateEquiv_symm a c d M

private def directEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        proEtaleConstantModuleDirectImage f (finiteCoefficientRing l E (n + 1)) :=
  pullbackTensorSequenceDirectEvaluation l E f n

private theorem ordinary_evaluation_mate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (pullbackTensorSequenceAdjunction l E f)
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
      ((pullbackTensorSequenceInverseEvaluation l E f n).symm ≪≫
        Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
          (pullbackTensorLevelIntrinsic l E f n)).inv) =
      (directEvaluation l E f n).hom := by
  unfold directEvaluation
  apply evaluation_mate (pullbackTensorSequenceAdjunction l E f)
    (coefficientProEtaleModuleAdjunction f
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
  · exact (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec
  · intro M
    ext U x
    exact (pullbackTensorLevelIntrinsic_existsUnique l E f n).exists.choose_spec M U.unop x

attribute [local irreducible] constantSheaf presheafToSheaf Functor.leftAdjoint
  coefficientSequenceCommRingSystem coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSheaf pullbackTensorSequenceRing coefficientProEtaleDirectRingMap
  proEtaleConstantDirectImageMap
attribute [local implicit_reducible] coefficientSequenceEvaluation
  pullbackTensorSequenceDirect pullbackTensorSequenceBase coefficientProEtaleModuleDirectImage
  proEtaleConstantModuleDirectImage integralCoefficientSheaf integralCoefficientCommRingSheaf
  SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

attribute [local irreducible] proEtaleCoefficientDirectImageComparison
  directEvaluation pullbackTensorSequenceInverseEvaluation
  pullbackTensorLevelIntrinsic Functor.ofSequence Functor.ofOpSequence

/--
The residual degreewise module-map identity obtained by expanding the mapped
homological-complex component of the ordinary pullback evaluation square.
Source: Zheng Construction 4.1 and the paragraph preceding Lemma 4.10.
(blueprint: lem-sf-integral-pull-evaluation-cochain-square-component-core).
The proof is the sectionwise quotient-transition calculation: the inverse-image
comparison is the inverse mate of direct-image evaluation, the intrinsic finite
comparison preserves the adjunction unit, and the normalized scalar comparison
is identity on sections. Naturality in the coefficient transition then identifies
both composites. This statement records only the resulting module maps at one
object, so the cochain wrappers and degree bookkeeping are absent.
-/
theorem integralPullEvaluation_cochainSquare_component_core_expanded
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r₀ : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr₀ : HEq r₀ (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) (i : ℤ) :
    ((NatTrans.mapHomologicalComplex
        (coefficientSequenceTransition l E X (Nat.le_succ n)) (.up ℤ)).app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P)).f i ≫
      (((normalizedDVRModuleRes l E X (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
        (((pullbackTensorInverseEvaluationComplex l E f n).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
        (.up ℤ))).hom.app P)).f i =
    ((((pullbackTensorInverseEvaluationComplex l E f (n + 1)).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y (n + 1)).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f (n + 1))
        (.up ℤ))).hom.app P)).f i ≫
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 2)) f).mapHomologicalComplex
        (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (coefficientSequenceTransition l E Y (Nat.le_succ n)) (.up ℤ)).app P)).f i ≫
      ((NatTrans.mapHomologicalComplex
        ((mateEquiv
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2)))).symm
          (TwoSquare.mk _ _ _ _ r₀.inv)) (.up ℤ)).app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)).f i  := by
  have ho := evaluation_transition_mate
    (pullbackTensorSequenceAdjunction l E f)
    (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
    (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2)))
    ((pullbackTensorSequenceInverseEvaluation l E f n).symm ≪≫
      Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
        (pullbackTensorLevelIntrinsic l E f n))
    ((pullbackTensorSequenceInverseEvaluation l E f (n + 1)).symm ≪≫
      Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y (n + 1))
        (pullbackTensorLevelIntrinsic l E f (n + 1)))
    (directEvaluation l E f n).hom
    (directEvaluation l E f (n + 1)).hom
    (ordinary_evaluation_mate l E f n) (ordinary_evaluation_mate l E f (n + 1))
    (coefficientSequenceTransition l E Y (Nat.le_succ n))
    (coefficientSequenceTransition l E X (Nat.le_succ n)) r₀.inv
    (by simpa only [directEvaluation] using
      (integralPullEvaluation_directTransitionSquare l E f n r₀ hr₀))
  have ho' := ho (P.X i)
  convert ho' using 1 <;>
    simp only [pullbackTensorInverseEvaluationComplex, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
    Functor.map_comp, Functor.comp_obj, Category.assoc]
  all_goals simp

end WeilConjectures.IntegralSystemRealization

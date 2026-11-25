/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation

/-! # The ordinary finite evaluation square for section-normalized pullback

Source: Stacks Project, Tag 03D8, and the ordinary adjunction unit normalizations.
(blueprint: lem-pur-ordinary-system-pullback-compositor-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped CategoryTheory.TwoSquare

-- Pasting and cancellation in the abstract mate correspondence.
private theorem evaluation_composition
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₀ ⥤ C₂}
    {R : C₁ ⥤ C₀} {S : C₂ ⥤ C₁} {T : C₂ ⥤ C₀}
    {P : D₀ ⥤ D₁} {Q : D₁ ⥤ D₂} {V : D₀ ⥤ D₂}
    {U : D₁ ⥤ D₀} {W : D₂ ⥤ D₁} {J : D₂ ⥤ D₀}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ T)
    (a' : P ⊣ U) (b' : Q ⊣ W) (c' : V ⊣ J)
    (e₀ : C₀ ⥤ D₀) (e₁ : C₁ ⥤ D₁) (e₂ : C₂ ⥤ D₂)
    (qF : F ⋙ e₁ ≅ e₀ ⋙ P) (qG : G ⋙ e₂ ≅ e₁ ⋙ Q)
    (qH : H ⋙ e₂ ≅ e₀ ⋙ V)
    (dF : R ⋙ e₀ ⟶ e₁ ⋙ U) (dG : S ⋙ e₁ ⟶ e₂ ⋙ W)
    (dH : T ⋙ e₀ ⟶ e₂ ⋙ J)
    (hF : (mateEquiv a a' qF.inv) = dF)
    (hG : (mateEquiv b b' qG.inv) = dG)
    (hH : (mateEquiv c c' qH.inv) = dH)
    (k : H ≅ F ⋙ G) (k' : V ≅ P ⋙ Q)
    (hd : ∀ N : C₂,
      e₀.map ((conjugateEquiv (a.comp b) c k.hom).app N) ≫ dH.app N =
        dF.app (S.obj N) ≫ U.map (dG.app N) ≫
          (conjugateEquiv (a'.comp b') c' k'.hom).app (e₂.obj N))
    (M : C₀) :
    e₂.map (k.hom.app M) ≫ qG.hom.app (F.obj M) ≫ Q.map (qF.hom.app M) =
      qH.hom.app M ≫ k'.hom.app (e₀.obj M) := by
  have hh : (TwoSquare.mk _ _ _ _ qH.inv).whiskerLeft k.hom =
      ((TwoSquare.mk _ _ _ _ qF.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ qG.inv)).whiskerRight k'.hom := by
    apply (mateEquiv (a.comp b) c').injective
    rw [conjugateEquiv_mateEquiv_vcomp (a.comp b) c c',
      mateEquiv_conjugateEquiv_vcomp (a.comp b) (a'.comp b') c',
      mateEquiv_hcomp a a' b b']
    change (mateEquiv a a' (TwoSquare.mk _ _ _ _ qF.inv)) =
      TwoSquare.mk _ _ _ _ dF at hF
    change (mateEquiv b b' (TwoSquare.mk _ _ _ _ qG.inv)) =
      TwoSquare.mk _ _ _ _ dG at hG
    change (mateEquiv c c' (TwoSquare.mk _ _ _ _ qH.inv)) =
      TwoSquare.mk _ _ _ _ dH at hH
    rw [hF, hG, hH]
    ext N
    simpa only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.hComp_app, Category.assoc] using hd N
  have hhM := congrArg (fun z ↦ z.app M) hh
  simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
    TwoSquare.vComp_app] at hhM
  apply (cancel_epi (qH.inv.app M)).mp
  apply (cancel_mono (Q.map (qF.inv.app M) ≫ qG.inv.app (F.obj M))).mp
  simp only [Category.assoc, ← Q.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc]
  dsimp only [Functor.comp_obj]
  rw [Q.map_id, Category.id_comp, qG.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id]
  exact hhM

-- Unit normalizations determine the mate of the inverse evaluation comparison.
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

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def directEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        proEtaleConstantModuleDirectImage f (finiteCoefficientRing l E (n + 1)) :=
  pullbackTensorSequenceDirectEvaluation l E f n

private theorem directEvaluation_spec {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
      (x : ((pullbackTensorSequenceDirect l E f ⋙
        coefficientSequenceEvaluation l E Y n).obj M).val.obj (Opposite.op U)),
      HEq (((directEvaluation l E f n).hom.app M).val.app (Opposite.op U) x) x := by
  unfold directEvaluation
  exact (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec

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

-- Transport the fixed-scalar compositor calculation back to intrinsic sections.
private theorem intrinsic_compositor_sections
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
    (x : ((proEtaleConstantModuleDirectImage f A ⋙
      proEtaleConstantModuleDirectImage g A).obj M).val.obj (Opposite.op V)) :
    ((conjugateEquiv
      ((sfIntrinsicConstantModuleAdjunction g A).comp
        (sfIntrinsicConstantModuleAdjunction f A))
      (sfIntrinsicConstantModuleAdjunction (f ≫ g) A)
      (sfIntrinsicPullbackComp A f g).hom).app M).val.app (Opposite.op V) x =
        M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op x := by
  open WeilConjectures.AmbientCompositor in
    obtain ⟨y, hy⟩ := (sectionRealization_bijective A Z
      ((proEtaleConstantModuleDirectImage g A).obj
        ((proEtaleConstantModuleDirectImage f A).obj M)) (Opposite.op V)).surjective x
    have hm := finite_comp_mate A f g M
    have hv := congrArg (fun t ↦ sectionRealization A X M
      (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
        ((t.hom.app (Opposite.op V)) y)) hm
    change sectionRealization A X M (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
        (((sectionDirectImageIso A (f ≫ g)).hom.app M).hom.app (Opposite.op V)
          (((sfIntrinsicModuleEquivalence Z A).inverse.map
            (((finite A).ordinaryC f g).hom.app M)).hom.app (Opposite.op V) y)) =
      sectionRealization A X M (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
        (((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map
          ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
          (((sectionDirectImageIso A f).hom.app M).hom.app
            (Opposite.op ((proEtaleBaseChange g).obj V))
            (((sectionDirectImageIso A g).hom.app
              ((proEtaleConstantModuleDirectImage f A).obj M)).hom.app (Opposite.op V) y)))
      at hv
    erw [sectionDirectImageIso_normalization, sectionRealization_naturality,
      sectionRealization_restrict, sectionDirectImageIso_normalization,
      sectionDirectImageIso_normalization, hy] at hv
    exact hv

private def baseComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proEtaleBaseChange (f ≫ g) ≅ proEtaleBaseChange g ⋙ proEtaleBaseChange f := by
  exact MorphismProperty.Over.pullbackComp f g

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] Scheme.ProEt baseComp
-- Scalar restriction preserves carriers; do not unfold the coefficient constructions.
attribute [local irreducible] constantSheaf presheafToSheaf Functor.leftAdjoint
  coefficientSequenceCommRingSystem coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSheaf

attribute [local irreducible] directEvaluation

attribute [local implicit_reducible] coefficientSequenceEvaluation
  pullbackTensorSequenceDirect pullbackTensorSequenceBase coefficientProEtaleModuleDirectImage
  proEtaleConstantModuleDirectImage integralCoefficientSheaf integralCoefficientCommRingSheaf
  Functor.sheafPushforwardContinuous Prod.sectR SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
attribute [local irreducible] pullbackTensorSequenceRing coefficientProEtaleDirectRingMap
  proEtaleConstantDirectImageMap

private theorem evaluation_map_section (X : Scheme.{u}) (n : ℕ)
    {M N : coefficientSequenceModules l E X} (a : M ⟶ N) (U : X.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E X n).obj M).val.obj U) :
    (((coefficientSequenceEvaluation l E X n).map a).val.app U) x =
      a.val.app (Opposite.op (n, U.unop)) x := rfl

private theorem direct_map_section (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)} (a : M ⟶ N)
    (U : Y.ProEtᵒᵖ)
    (x : ((proEtaleConstantModuleDirectImage f A).obj M).val.obj U) :
    (((proEtaleConstantModuleDirectImage f A).map a).val.app U) x =
      a.val.app ((proEtaleBaseChange f).op.obj U) x := rfl

private theorem direct_map_identity (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)} (a : M ⟶ N)
    (ha : ∀ (U : X.ProEtᵒᵖ) (x : M.val.obj U), HEq (a.val.app U x) x)
    (U : Y.ProEtᵒᵖ)
    (x : ((proEtaleConstantModuleDirectImage f A).obj M).val.obj U) :
    HEq ((((proEtaleConstantModuleDirectImage f A).map a).val.app U) x) x := by
  rw [direct_map_section]
  exact ha ((proEtaleBaseChange f).op.obj U) x

private theorem direct_compositor_left
    (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (N : coefficientSequenceModules l E X) (U : Z.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f ⋙ pullbackTensorSequenceDirect l E g).obj
      N).val.obj (Opposite.op (n, U))) :
    HEq (((directEvaluation l E (f ≫ g) n).hom.app N).val.app (Opposite.op U)
      ((((coefficientSequenceEvaluation l E Z n).map
        ((c.ordinaryDirect f g).hom.app N)).val.app (Opposite.op U)) x))
      (N.val.map (@Quiver.Hom.op (ℕ × X.ProEt) _
        (n, (proEtaleBaseChange (f ≫ g)).obj U)
        (n, (proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U))
        (𝟙 n, (baseComp f g).hom.app U)) x) := by
  exact (directEvaluation_spec l E (f ≫ g) n N U
    ((((coefficientSequenceEvaluation l E Z n).map
      ((c.ordinaryDirect f g).hom.app N)).val.app (Opposite.op U)) x)).trans
    (heq_of_eq ((evaluation_map_section l E Z n
      ((c.ordinaryDirect f g).hom.app N) (Opposite.op U) x).trans
        (c.sections f g N n U x)))

private theorem direct_compositor_right
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (N : coefficientSequenceModules l E X) (U : Z.ProEt)
    (x : ((pullbackTensorSequenceDirect l E f ⋙ pullbackTensorSequenceDirect l E g).obj
      N).val.obj (Opposite.op (n, U))) :
    HEq (((conjugateEquiv
      ((sfIntrinsicConstantModuleAdjunction g (finiteCoefficientRing l E (n + 1))).comp
        (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))))
      (sfIntrinsicConstantModuleAdjunction (f ≫ g) (finiteCoefficientRing l E (n + 1)))
      (sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) f g).hom).app
        ((coefficientSequenceEvaluation l E X n).obj N)).val.app (Opposite.op U)
      ((((proEtaleConstantModuleDirectImage g (finiteCoefficientRing l E (n + 1))).map
        ((directEvaluation l E f n).hom.app N)).val.app (Opposite.op U))
        (((directEvaluation l E g n).hom.app
          ((pullbackTensorSequenceDirect l E f).obj N)).val.app (Opposite.op U) x)))
      (N.val.map (@Quiver.Hom.op (ℕ × X.ProEt) _
        (n, (proEtaleBaseChange (f ≫ g)).obj U)
        (n, (proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U))
        (𝟙 n, (baseComp f g).hom.app U)) x) := by
  -- Heterogeneous identities retain the distinct scalar restrictions.
  let y := ((directEvaluation l E g n).hom.app
    ((pullbackTensorSequenceDirect l E f).obj N)).val.app (Opposite.op U) x
  let z := (((proEtaleConstantModuleDirectImage g
    (finiteCoefficientRing l E (n + 1))).map
      ((directEvaluation l E f n).hom.app N)).val.app (Opposite.op U)) y
  have hy : HEq y x := directEvaluation_spec l E g n
    ((pullbackTensorSequenceDirect l E f).obj N) U x
  have hz : HEq z y := direct_map_identity (finiteCoefficientRing l E (n + 1)) g
    ((directEvaluation l E f n).hom.app N)
    (fun V t ↦ directEvaluation_spec l E f n N V.unop t) (Opposite.op U) y
  refine (heq_of_eq (intrinsic_compositor_sections
    (finiteCoefficientRing l E (n + 1)) f g
    ((coefficientSequenceEvaluation l E X n).obj N) U z)).trans ?_
  apply heq_of_eq
  apply congr_heq ?_ (hz.trans hy)
  rfl

attribute [local irreducible] pullbackTensorSequenceInverseEvaluation
  pullbackTensorLevelIntrinsic pullbackTensorSequenceAdjunction
  sfIntrinsicConstantModuleAdjunction sfIntrinsicPullbackComp

/-- Ordinary evaluation commutes with the specified section-normalized compositor.
This concerns module sheaves, without complexes or derived localization.
Source: Stacks Project, Tag 03D8; steps 1 and 2 of the parent proof.
(blueprint: lem-pur-ordinary-system-pullback-compositor-evaluation).
Proof: the section equation of c identifies its direct compositor with restriction
along the canonical iterated-base-change isomorphism. Extensionality of module-sheaf
morphisms and then natural transformations proves that identification. Transpose
under the composite ordinary adjunction and use c.conjugate to identify its left
mate. The inverse-evaluation comparisons are fixed by their adjunction unit
formulas. Apply ordinaryCompositionEvaluation for the canonical sequence and
coefficient-module pullbacks: it is the equality obtained by transposing the two
paths under the finite adjunctions and restricting along that same base-change map.
The unit formulas identify its evaluation comparisons with those displayed here.
Finally the unit characterization of pullbackTensorLevelIntrinsic transports this
identity from the coefficient-module pullback to the intrinsic pullback, whose
compositor is the conjugate of the same base-change restriction. Injectivity of
adjunction hom equivalences gives the displayed ordinary square. This argument
uses arbitrary sections, so applies to zero sheaves and n=0 without exceptions;
identity scheme morphisms use the same adjunction unit equations. -/
theorem ordinarySystemPullbackCompositorEvaluation
    (o : Operations l E) (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (M : coefficientSequenceModules l E Z) :
    (coefficientSequenceEvaluation l E X n).map ((c.ordinaryPull f g).hom.app M) ≫
      ((pullbackTensorSequenceInverseEvaluation l E f n).symm ≪≫
        Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
          (pullbackTensorLevelIntrinsic l E f n)).hom.app
            ((pullbackTensorSequenceInverse l E g).obj M) ≫
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).map
        (((pullbackTensorSequenceInverseEvaluation l E g n).symm ≪≫
          Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Z n)
            (pullbackTensorLevelIntrinsic l E g n)).hom.app M) =
    ((pullbackTensorSequenceInverseEvaluation l E (f ≫ g) n).symm ≪≫
      Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Z n)
        (pullbackTensorLevelIntrinsic l E (f ≫ g) n)).hom.app M ≫
      (sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) f g).hom.app
        ((coefficientSequenceEvaluation l E Z n).obj M)  := by
  apply evaluation_composition
    (pullbackTensorSequenceAdjunction l E g) (pullbackTensorSequenceAdjunction l E f)
    (pullbackTensorSequenceAdjunction l E (f ≫ g))
    (sfIntrinsicConstantModuleAdjunction g (finiteCoefficientRing l E (n + 1)))
    (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
    (sfIntrinsicConstantModuleAdjunction (f ≫ g) (finiteCoefficientRing l E (n + 1)))
    (coefficientSequenceEvaluation l E Z n) (coefficientSequenceEvaluation l E Y n)
    (coefficientSequenceEvaluation l E X n)
    _ _ _
    (directEvaluation l E g n).hom
    (directEvaluation l E f n).hom
    (directEvaluation l E (f ≫ g) n).hom
    (ordinary_evaluation_mate l E g n) (ordinary_evaluation_mate l E f n)
    (ordinary_evaluation_mate l E (f ≫ g) n)
    (c.ordinaryPull f g) (sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) f g)
    ?_ M
  intro N
  have hc := congrArg Iso.hom (c.conjugate f g)
  change conjugateEquiv _ _ (c.ordinaryPull f g).hom = _ at hc
  rw [hc]
  ext U x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact eq_of_heq ((direct_compositor_left l E o c f g n N U.unop x).trans
    (direct_compositor_right l E f g n N U.unop x).symm)

end WeilConjectures.IntegralSystemRealization

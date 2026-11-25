/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SixFunctors.System.SystemDirectImageReductionTransitions
public import WeilConjectures.SixFunctors.Completed.CompletedDirectImageFiniteProjection
public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import all WeilConjectures.SmoothPurity.Sf.SfDirectImageRestrictionPasting
import all WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
import all WeilConjectures.TraceFormula.Compact.CompactSupportFiniteCoefficientPresentation

/-! # Quotient compatibility of the completed direct-image projection formula

Source: Zheng, Construction 4.1, Lemma 4.10 and Proposition 4.21;
Stacks 0941, 0944 and 099N.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem projection_mate_quotient
    {C D A₀ A₁ B₀ B₁ : Type*}
    [Category C] [Category D] [Category A₀] [Category A₁] [Category B₀] [Category B₁]
    {LX₀ : C ⥤ A₀} {RX₀ : A₀ ⥤ C} {LX₁ : C ⥤ A₁} {RX₁ : A₁ ⥤ C}
    {LY₀ : D ⥤ B₀} {RY₀ : B₀ ⥤ D} {LY₁ : D ⥤ B₁} {RY₁ : B₁ ⥤ D}
    (ax₀ : LX₀ ⊣ RX₀) (ax₁ : LX₁ ⊣ RX₁)
    (ay₀ : LY₀ ⊣ RY₀) (ay₁ : LY₁ ⊣ RY₁)
    (H : C ⥤ D) (F₀ : A₀ ⥤ B₀) (F₁ : A₁ ⥤ B₁)
    (P : A₁ ⥤ A₀) (Q : B₁ ⥤ B₀)
    (cX : P ⋙ RX₀ ≅ RX₁) (cY : Q ⋙ RY₀ ≅ RY₁)
    (d₀ : RX₀ ⋙ H ≅ F₀ ⋙ RY₀) (d₁ : RX₁ ⋙ H ≅ F₁ ⋙ RY₁)
    (a : P ⋙ F₀ ≅ F₁ ⋙ Q)
    (hc : ∀ N, d₀.hom.app (P.obj N) ≫ RY₀.map (a.hom.app N) ≫
      cY.hom.app (F₁.obj N) = H.map (cX.hom.app N) ≫ d₁.hom.app N)
    (K : C) :
    (coefficientQuotientNatTrans ay₀ ay₁ Q cY).app (H.obj K) ≫
        Q.map ((ay₁.homEquiv _ _).symm
          (H.map (ax₁.unit.app K) ≫ d₁.hom.app (LX₁.obj K))) =
      (ay₀.homEquiv _ _).symm
          (H.map (ax₀.unit.app K) ≫ d₀.hom.app (LX₀.obj K)) ≫
        F₀.map ((coefficientQuotientNatTrans ax₀ ax₁ P cX).app K) ≫
        a.hom.app (LX₁.obj K) := by
  let q := (coefficientQuotientNatTrans ax₀ ax₁ P cX).app K
  have hu : ax₀.unit.app K ≫ RX₀.map q =
      ax₁.unit.app K ≫ cX.inv.app (LX₁.obj K) := by
    exact (ax₀.homEquiv K (P.obj (LX₁.obj K))).apply_symm_apply _
  symm
  apply compactSupportAdjointTransition ay₀ ay₁ Q cY
  simp only [Functor.map_comp, Category.assoc]
  change H.map (ax₀.unit.app K) ≫ d₀.hom.app (LX₀.obj K) ≫
    RY₀.map (F₀.map q) ≫ RY₀.map (a.hom.app (LX₁.obj K)) ≫
    cY.hom.app (F₁.obj (LX₁.obj K)) = _
  have hd := d₀.hom.naturality q
  dsimp only [Functor.comp_map, Functor.comp_obj] at hd
  rw [← reassoc_of% hd, ← H.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, ← H.map_comp_assoc (cX.inv.app (LX₁.obj K)) (cX.hom.app (LX₁.obj K)),
    Iso.inv_hom_id_app, H.map_id, Category.id_comp]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [(integralComparisonSequenceDirectImage l E f).Additive]
  [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
  [∀ n : ℕ, (compactSupportLevelDirectImage l E f n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (normalizedDVRModules l E X n)]

omit [(integralComparisonSequenceDirectImage l E f).Additive]
  [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)] in
private theorem finite_restriction_pasting {m n : ℕ} (h : n ≤ m)
    (a₀ : normalizedDVRModuleRes l E X h ⋙ compactSupportLevelDirectImage l E f m ≅
      compactSupportLevelDirectImage l E f n ⋙ normalizedDVRModuleRes l E Y h)
    (a : normalizedDVRRes l E X h ⋙
        (compactSupportLevelDirectImage l E f m).rightDerivedFunctor ≅
      (compactSupportLevelDirectImage l E f n).rightDerivedFunctor ⋙ normalizedDVRRes l E Y h)
    (ha : ∀ (M : normalizedDVRModules l E X n) (V : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (a₀.hom.app M).val.app V x)
        (fun x : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj V) ↦ x))
    (hn : CompactSupportDerivedSquareNormalization
      (compactSupportLevelDirectImage l E f n) (compactSupportLevelDirectImage l E f m)
      (normalizedDVRModuleRes l E X h) (normalizedDVRModuleRes l E Y h) a₀ a)
    (B : normalizedDVRDerived l E X n) :
    (sfDerivedRestrictionComparison l E f m).hom.app ((normalizedDVRRes l E X h).obj B) ≫
        (coefficientFiniteDerivedRestriction l E Y m).map (a.hom.app B) ≫
        (compactSupportSystemRestrictionComp l E Y h).hom.app
          ((compactSupportLevelDirectImage l E f n).rightDerivedFunctor.obj B) =
      (sfCompletedDerivedDirectImage l E f).map
          ((compactSupportSystemRestrictionComp l E X h).hom.app B) ≫
        (sfDerivedRestrictionComparison l E f n).hom.app B := by
  have hs (M : normalizedDVRModules l E X n) (V : Y.ProEtᵒᵖ)
      (x : ((normalizedDVRModuleRes l E X h ⋙
        compactSupportLevelDirectImage l E f m).obj M).val.obj V) :
      HEq ((a₀.hom.app M).val.app V x) x := by
    have eA := (level_carrier_eq l E f m
      ((normalizedDVRModuleRes l E X h).obj M) V).trans
      (normalized_res_carrier_eq l E X h M ((proEtaleBaseChange f).op.obj V))
    have eB := (normalized_res_carrier_eq l E Y h
      ((compactSupportLevelDirectImage l E f n).obj M) V).trans
        (level_carrier_eq l E f n M V)
    exact function_identity_of_heq eA eB _ (ha M V) x
  exact sheafDerivedTriangle
    (compactSupportLevelDirectImage l E f n) (compactSupportLevelDirectImage l E f m)
    (sfCompletedModuleDirectImage l E f)
    (scalarReductionRestriction l E X n) (normalizedDVRModuleRes l E X h)
    (scalarReductionRestriction l E X m)
    (scalarReductionRestriction l E Y n) (normalizedDVRModuleRes l E Y h)
    (scalarReductionRestriction l E Y m)
    (coefficientRestrictionComp l E X h) (coefficientRestrictionComp l E Y h) a₀
    (sfDirectImageRestrictionComparison l E f n)
    (sfDirectImageRestrictionComparison l E f m)
    (sfDerivedRestrictionComparison l E f m) (sfDerivedRestrictionComparison l E f n) a
    (sfDerivedRestrictionComparison_existsUnique l E f m).exists.choose_spec
    (sfDerivedRestrictionComparison_existsUnique l E f n).exists.choose_spec hn
    (scalarRestriction_identity l E Y m) hs
    (completedComparison_identity l E f n) (completedComparison_identity l E f m) B

omit [(integralComparisonSequenceDirectImage l E f).Additive]
  [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)] in
/-- The canonical perfect-quotient projection arrows commute with scalar quotient maps.
Source: Zheng Proposition 4.21, equation (4.21.1); Lemma 4.10; Stacks 0944.
(blueprint: lem-weil-completed-direct-image-finite-projection-transitions).

Proof: the section-normalized finite direct-image restriction square pastes with
both completed restriction comparisons. Apply the derived triangle identity to
this sectionwise equation. Taking scalar-adjunction mates, use naturality of the
comparison and both adjunction unit equations to obtain precisely the displayed
finite-category equality. No restriction functor is assumed faithful. -/
theorem completedDirectImageFiniteProjection_transitions {m n : ℕ} (h : n ≤ m)
    (a₀ : normalizedDVRModuleRes l E X h ⋙ compactSupportLevelDirectImage l E f m ≅
      compactSupportLevelDirectImage l E f n ⋙ normalizedDVRModuleRes l E Y h)
    (a : normalizedDVRRes l E X h ⋙
        (compactSupportLevelDirectImage l E f m).rightDerivedFunctor ≅
      (compactSupportLevelDirectImage l E f n).rightDerivedFunctor ⋙ normalizedDVRRes l E Y h)
    (ha : ∀ (M : normalizedDVRModules l E X n) (V : Y.ProEtᵒᵖ),
      HEq (fun x ↦ (a₀.hom.app M).val.app V x)
        (fun x : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj V) ↦ x))
    (hn : CompactSupportDerivedSquareNormalization
      (compactSupportLevelDirectImage l E f n) (compactSupportLevelDirectImage l E f m)
      (normalizedDVRModuleRes l E X h) (normalizedDVRModuleRes l E Y h) a₀ a)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (systemReductionQuotient l E Y h).app ((sfCompletedDerivedDirectImage l E f).obj K) ≫
        (normalizedDVRRes l E Y h).map (completedDirectImageFiniteProjection l E f n K) =
      completedDirectImageFiniteProjection l E f m K ≫
        (compactSupportLevelDirectImage l E f m).rightDerivedFunctor.map
          ((systemReductionQuotient l E X h).app K) ≫
        a.hom.app ((coefficientFiniteDerivedExtension l E X n).obj K) := by
  exact projection_mate_quotient
    (coefficientFiniteAdjunction l E X m) (coefficientFiniteAdjunction l E X n)
    (coefficientFiniteAdjunction l E Y m) (coefficientFiniteAdjunction l E Y n)
    (sfCompletedDerivedDirectImage l E f)
    (compactSupportLevelDirectImage l E f m).rightDerivedFunctor
    (compactSupportLevelDirectImage l E f n).rightDerivedFunctor
    (normalizedDVRRes l E X h) (normalizedDVRRes l E Y h)
    (compactSupportSystemRestrictionComp l E X h) (compactSupportSystemRestrictionComp l E Y h)
    (sfDerivedRestrictionComparison l E f m) (sfDerivedRestrictionComparison l E f n) a
    (finite_restriction_pasting l E f h a₀ a ha hn) K

end WeilConjectures

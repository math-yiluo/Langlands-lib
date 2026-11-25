/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Roos comparison of strict coefficient-extension representatives

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf HasDerivedCategory.standard
  SemilinearSections.hasDerived

private theorem hcongr_apply {α γ : Sort a} {β δ : Sort b} {f : α → β} {g : γ → δ}
    {x : α} {y : γ} (hcod : β = δ) (h : HEq f g) (hx : HEq x y) :
    HEq (f x) (g y) := by
  subst δ
  exact heq_of_eq (congr_heq h hx)

private theorem ab_fun_heq_of_conj
    {M N M' N' : AddCommGrpCat.{a}}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : f = eqToHom hM ≫ g ≫ eqToHom hN.symm) :
    HEq (fun x ↦ f x) (fun x ↦ g x) := by
  subst M' N'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst g
  rfl

private theorem module_eqToHom_apply_heq
    {M N : scalarReductionSource l L W}
    (h : M = N) (V : W.ProEtᵒᵖ) (x : M.val.obj V) :
    HEq (((eqToHom h).val.app V) x) x := by
  subst N
  rfl

private theorem restrictionMap_apply_heq (n : ℕ)
    {M N : normalizedDVRModules l L W n} (f : M ⟶ N) (V : W.ProEtᵒᵖ)
    (x : ((scalarReductionRestriction l L W n).obj M).val.obj V)
    (y : M.val.obj V) (h : HEq x y) :
    HEq ((((scalarReductionRestriction l L W n).map f).val.app V) x)
      ((f.val.app V) y) := by
  have h' : x = y := eq_of_heq h
  subst y
  rfl

private theorem restriction_transition_heq
    (M : coefficientSequenceModules l L W) {m n : ℕ} (h : n ≤ m) (V : W.ProEtᵒᵖ) :
    HEq (fun x ↦ (((coefficientSequenceRestriction l L W).obj M).map
        (homOfLE h).op).val.app V x)
      (fun x ↦ ((coefficientSequenceTransition l L W h).app M).val.app V x) := by
  have hU := (coefficientSequenceRestriction_exists l L W).exists.choose_spec.2.1 M m n h V
  have hτ := (coefficientSequenceTransition_exists l L W h).exists.choose_spec M V
  exact hU.trans (ab_fun_heq_of_conj
    (coefficientSequenceEvaluationAb_eq l L W M m V).symm
    (coefficientSequenceRestrictedEvaluationAb_eq l L W M h V).symm _ _ hτ.symm)

private theorem restriction_transition_apply_heq
    (M : coefficientSequenceModules l L W) {m n : ℕ} (h : n ≤ m) (V : W.ProEtᵒᵖ)
    (x : (((coefficientSequenceRestriction l L W).obj M).obj (op m)).val.obj V)
    (y : ((coefficientSequenceEvaluation l L W m).obj M).val.obj V) (hxy : HEq x y) :
    HEq (((((coefficientSequenceRestriction l L W).obj M).map
        (homOfLE h).op).val.app V) x)
      ((((coefficientSequenceTransition l L W h).app M).val.app V) y) := by
  have hobj := congrArg (fun F ↦ F.obj M)
    (coefficientSequenceRestriction_evaluation l L W n)
  have hs := restrictScalars_presheaf_obj
    ((sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l L W n))
    ((coefficientSequenceEvaluation l L W n).obj M) V
  have hcod :
      ↥((((coefficientSequenceRestriction l L W).obj M).obj (op n)).val.obj V) =
        ↥(((normalizedDVRModuleRes l L W h).obj
          ((coefficientSequenceEvaluation l L W n).obj M)).val.obj V) :=
    congrArg (fun G : AddCommGrpCat ↦ ↥G)
      ((congrArg (fun N : scalarReductionSource l L W ↦ N.val.presheaf.obj V) hobj).trans
        (hs.trans (restrictScalars_presheaf_obj
          (normalizedDVRQuotient l L W h)
          ((coefficientSequenceEvaluation l L W n).obj M) V).symm))
  exact hcongr_apply hcod (restriction_transition_heq l L W M h V) hxy

/-- Evaluation of a restricted strict complex, using the actual evaluation equality.
Source: Stacks 0941 (blueprint: stage3-pur-extension-restricted-tower). -/
def coefficientRestrictedComplexEvaluation (n : ℕ) :
    (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
        ((evaluation ℕᵒᵖ (scalarReductionSource l L W)).obj (op n)).mapHomologicalComplex
          (.up ℤ) ≅
      (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ⋙
        (scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l L W n)) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

private theorem restrictedEvaluation_hom_f
    (X : CochainComplex (coefficientSequenceModules l L W) ℤ) (n : ℕ) (i : ℤ) :
    ((coefficientRestrictedComplexEvaluation l L W n).hom.app X).f i =
      eqToHom (congrArg (fun F ↦ F.obj (X.X i))
        (coefficientSequenceRestriction_evaluation l L W n)) := by
  simp only [coefficientRestrictedComplexEvaluation, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, eqToIso.hom, eqToHom_app]
  erw [Category.id_comp, Category.comp_id]

private theorem restrictedEvaluation_inv_f
    (X : CochainComplex (coefficientSequenceModules l L W) ℤ) (n : ℕ) (i : ℤ) :
    ((coefficientRestrictedComplexEvaluation l L W n).inv.app X).f i =
      eqToHom (congrArg (fun F ↦ F.obj (X.X i))
        (coefficientSequenceRestriction_evaluation l L W n)).symm := by
  simp only [coefficientRestrictedComplexEvaluation, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    NatIso.mapHomologicalComplex_inv_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, eqToIso.inv, eqToHom_app]
  erw [Category.id_comp, Category.comp_id]

private theorem assembleTowerIso
    {I B : Type*} [Category I] [Category B] [HasZeroMorphisms B]
    (H : I ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (T : I ⥤ (ℕᵒᵖ ⥤ CochainComplex B ℤ))
    (a : ∀ n : ℕ, H ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex
      (.up ℤ) ≅ T ⋙ (evaluation ℕᵒᵖ (CochainComplex B ℤ)).obj (op n))
    (ha : ∀ P n, (H.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op ≫
      (a n).hom.app P = (a (n + 1)).hom.app P ≫
        (T.obj P).map (homOfLE (Nat.le_succ n)).op) :
    ∃ e : H ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ T,
      ∀ P n, (e.hom.app P).app (op n) = (a n).hom.app P := by
  let f (P : I) : (H.obj P).asFunctor ⟶ T.obj P :=
    NatTrans.ofOpSequence (fun n ↦ (a n).hom.app P) (fun n ↦ ha P n)
  let eP (P : I) : (H.obj P).asFunctor ≅ T.obj P :=
    NatIso.ofComponents (fun n ↦ (a n.unop).app P) (fun g ↦ (f P).naturality g)
  let e : H ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ T :=
    NatIso.ofComponents eP (by
      intro P Q g
      apply NatTrans.ext
      funext n
      exact (a n.unop).hom.naturality g)
  refine ⟨e, ?_⟩
  intro P n
  rfl

/-- The specified strict level comparisons assemble after restriction of scalars.
Source: Stacks 0941 and the strict quotient construction of integral operations
(blueprint: stage3-pur-extension-restricted-tower).
Proof: restrict each level of the direct representative to the completed target
ring. The canonical restriction-evaluation equality and the given level comparison
give its isomorphism with the finite scalar complex. The specified transition
formula identifies the successor squares on every section in every degree.
Extensionality gives the chain-map squares, and successor naturality gives a map
of towers. Each level map is invertible, so this map is a tower isomorphism.
Naturality in the good complex follows from naturality of the level comparisons;
the evaluations jointly detect this equality. -/
theorem coefficientExtensionRestrictedTower_exists
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (htransition : IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation) :
    ∃ e : direct ⋙ (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      (integralOperationsGoodComplex l E W).ι ⋙ integralScalarTowerFunctor l E L ι W,
      ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
        (e.hom.app P).app (op n) =
          (coefficientRestrictedComplexEvaluation l L W n).hom.app (direct.obj P) ≫
            ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ)).map
              ((directEvaluation n).hom.app P) := by
  classical
  let H := direct ⋙ (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)
  let a (n : ℕ) : H ⋙
      ((evaluation ℕᵒᵖ (scalarReductionSource l L W)).obj (op n)).mapHomologicalComplex
        (.up ℤ) ≅ (integralOperationsGoodComplex l E W).ι ⋙ integralScalarLevel l E L ι W n :=
    Functor.isoWhiskerLeft direct (coefficientRestrictedComplexEvaluation l L W n) ≪≫
      Functor.isoWhiskerRight (directEvaluation n)
        ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ))
  have ha (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) :
      (H.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ (a n).hom.app P =
        (a (n + 1)).hom.app P ≫ (integralScalarTransition l E L ι W n).app P.obj := by
    apply (cancel_mono ((a n).inv.app P)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    have hobj (k : ℕ) := congrArg (fun F ↦ F.obj ((direct.obj P).X i))
      (coefficientSequenceRestriction_evaluation l L W k)
    have hs (k : ℕ) :
        ((scalarReductionRestriction l L W k).obj
          ((coefficientSequenceEvaluation l L W k).obj ((direct.obj P).X i))).val.presheaf.obj V =
          ((coefficientSequenceEvaluation l L W k).obj ((direct.obj P).X i)).val.presheaf.obj V :=
      restrictScalars_presheaf_obj _ _ _
    let y : ((coefficientSequenceEvaluation l L W (n + 1)).obj
        ((direct.obj P).X i)).val.obj V :=
      cast (congrArg (fun G : AddCommGrpCat ↦ ↥G)
        ((congrArg (fun M : scalarReductionSource l L W ↦ M.val.presheaf.obj V)
          (hobj (n + 1))).trans (hs (n + 1)))) x
    have hy : HEq y x := by
      exact cast_heq _ x
    have hh := restriction_transition_apply_heq l L W ((direct.obj P).X i)
      (Nat.le_succ n) V x y hy.symm
    have ht := htransition P n i V y
    simp only [a, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Functor.mapHomologicalComplex_map_f,
      restrictedEvaluation_hom_f, restrictedEvaluation_inv_f]
    erw [Category.comp_id]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    apply eq_of_heq
    refine (hh.trans ht).trans ?_
    have hc0 := module_eqToHom_apply_heq l L W (hobj (n + 1)) V x
    have hc1 := restrictionMap_apply_heq l L W (n + 1)
      (((directEvaluation (n + 1)).hom.app P).f i) V _ y (hc0.trans hy.symm)
    have hc2 := hcongr_apply rfl
      (HEq.rfl (a := fun x ↦
        ((((integralScalarTransition l E L ι W n).app P.obj).f i).val.app V) x)) hc1
    have hc3 := restrictionMap_apply_heq l L W n
      (((directEvaluation n).inv.app P).f i) V _ _ hc2
    have hc4 := module_eqToHom_apply_heq l L W (hobj n).symm V
      (((((scalarReductionRestriction l L W n).map
        (((directEvaluation n).inv.app P).f i)).val.app V))
          (((((integralScalarTransition l E L ι W n).app P.obj).f i).val.app V)
            (((((scalarReductionRestriction l L W (n + 1)).map
              (((directEvaluation (n + 1)).hom.app P).f i)).val.app V))
                (((eqToHom (hobj (n + 1))).val.app V) x))))
    exact (hc4.trans hc3).symm
  let T := (integralOperationsGoodComplex l E W).ι ⋙ integralScalarTowerFunctor l E L ι W
  obtain ⟨e, he⟩ := assembleTowerIso H T a (fun P n ↦ by
    dsimp only [T, Functor.comp_obj, integralScalarTowerFunctor]
    erw [Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
    exact ha P n)
  refine ⟨e, ?_⟩
  intro P n
  rw [he]
  simp only [a, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]

end WeilConjectures

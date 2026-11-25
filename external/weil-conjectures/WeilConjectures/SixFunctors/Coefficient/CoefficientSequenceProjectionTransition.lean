/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Total-limit projections and quotient transitions

Source: Stacks 0940, 0941 and 07A6.

The total-limit projections of a coefficient system are compatible with its quotient
transitions. Consequently every left adjoint of the total limit whose finite evaluations
are the derived scalar extensions, compatibly with the projections, takes values in
normalized coefficient systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (G : C ⥤ E) (R : E ⥤ D)
  [F.Additive] [G.Additive] [R.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

@[irreducible] private def derivedTransition (τ : F ⟶ G ⋙ R) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ R.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ F.mapDerivedCategory (G ⋙ R).mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso G R).inv

@[reassoc] private theorem derivedTransition_fac (τ : F ⟶ G ⋙ R)
    (K : CochainComplex C ℤ) :
    (derivedTransition F G R τ).app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) := by
  unfold derivedTransition
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rfl
end CategoryTheory

namespace CategoryTheory
variable {C A B D E : Type*} [Category C] [Category A] [Category B]
  [Category D] [Category E] [Abelian C] [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory E]

@[irreducible] private def derivedMap
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    _ _ F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ)) DerivedCategory.Q)

@[reassoc] private theorem derivedMap_fac
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G)
    (K : CochainComplex A ℤ) :
    (derivedMap F G τ).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) := by
  unfold derivedMap
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

variable (U : C ⥤ A) (F : A ⥤ B) (G : C ⥤ D) (R : D ⥤ B)
  [U.Additive] [F.Additive] [G.Additive] [R.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

@[irreducible] private def derivedEvaluationIso (e : U ⋙ F ≅ G ⋙ R) :
    U.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ R.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso U F ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
    (Functor.mapDerivedCategoryCompIso G R).symm

@[reassoc] private theorem derivedEvaluationIso_fac (e : U ⋙ F ≅ G ⋙ R)
    (K : CochainComplex C ℤ) :
    (derivedEvaluationIso U F G R e).hom.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      F.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  unfold derivedEvaluationIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors U F K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem derivedSquare
    (F' : A ⥤ B) [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (S : E ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : E ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e₀ : U ⋙ F ≅ G ⋙ R) (e₁ : U ⋙ F' ≅ H ⋙ T) (e₂ : S ⋙ R ≅ T)
    (τ : F ⟶ F') (γ : G ⟶ H ⋙ S)
    (hc : ∀ M, τ.app (U.obj M) ≫ e₁.hom.app M =
      e₀.hom.app M ≫ R.map (γ.app M) ≫ e₂.hom.app (H.obj M))
    (X : DerivedCategory C) :
    (derivedMap F F' τ).app (U.mapDerivedCategory.obj X) ≫
        (derivedEvaluationIso U F' H T e₁).hom.app X =
      (derivedEvaluationIso U F G R e₀).hom.app X ≫
        R.mapDerivedCategory.map ((derivedTransition G H S γ).app X) ≫
        (Functor.mapDerivedCategoryCompNatIso e₂).hom.app (H.mapDerivedCategory.obj X) := by
  suffices hh : Functor.whiskerLeft U.mapDerivedCategory (derivedMap F F' τ) ≫
      (derivedEvaluationIso U F' H T e₁).hom =
      (derivedEvaluationIso U F G R e₀).hom ≫
        Functor.whiskerRight (derivedTransition G H S γ) R.mapDerivedCategory ≫
        Functor.whiskerLeft H.mapDerivedCategory (Functor.mapDerivedCategoryCompNatIso e₂).hom by
    exact congr_app hh X
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_mono (T.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
    T.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K))).1
  simp only [Category.assoc]
  rw [derivedEvaluationIso_fac]
  have hn := (derivedMap F F' τ).naturality (U.mapDerivedCategoryFactors.hom.app K)
  rw [← reassoc_of% hn, derivedMap_fac_assoc]
  have hn₂ := (Functor.mapDerivedCategoryCompNatIso e₂).hom.naturality
    (H.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hn₂
  rw [← reassoc_of% hn₂]
  have he := Functor.mapDerivedCategoryCompNatIso_hom_app_Q e₂
    ((H.mapHomologicalComplex (.up ℤ)).obj K)
  dsimp only [Functor.mapHomologicalComplexCompIsoHomOfIso] at he
  erw [Functor.mapHomologicalComplexCompIso_refl_hom_app, Category.id_comp] at he
  rw [he]
  have hγ := congrArg (fun z ↦ R.mapDerivedCategory.map z)
    (derivedTransition_fac G H S γ K)
  simp only [CategoryTheory.Functor.map_comp] at hγ
  rw [reassoc_of% hγ]
  have hn₃ := R.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex γ (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hn₃
  erw [reassoc_of% hn₃, derivedEvaluationIso_fac_assoc]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
    ← DerivedCategory.Q.map_comp]
  congr 3
  ext i
  exact hc _
end CategoryTheory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace WeilConjectures
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  coefficientSequenceEvaluation coefficientSequenceTransition
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

private def restrictedUnderlying
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat} (f : R ⟶ S)
    {M : SheafOfModules.{u} R} {N : SheafOfModules.{u} S}
    (g : M ⟶ (SheafOfModules.restrictScalars f).obj N) (U : Cᵒᵖ) :
    M.val.presheaf.obj U ⟶ N.val.presheaf.obj U :=
  (forget₂ (ModuleCat (R.obj.obj U)) AddCommGrpCat).map (g.val.app U)

private theorem restrictedUnderlying_fac
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat} (f : R ⟶ S)
    {M : SheafOfModules.{u} R} {N : SheafOfModules.{u} S}
    (g : M ⟶ (SheafOfModules.restrictScalars f).obj N) (U : Cᵒᵖ)
    {X Y : AddCommGrpCat.{u}}
    (eM : M.val.presheaf.obj U = X) (eN : N.val.presheaf.obj U = Y)
    (eR : ((SheafOfModules.restrictScalars f).obj N).val.presheaf.obj U = Y)
    (t : X ⟶ Y)
    (h : eqToHom eM.symm ≫
      (forget₂ (ModuleCat (R.obj.obj U)) AddCommGrpCat).map (g.val.app U) ≫
      eqToHom eR = t) :
    eqToHom eM.symm ≫ restrictedUnderlying f g U ≫ eqToHom eN = t := by
  exact h

private def transitionAb (M : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m)
    (U : W.ProEtᵒᵖ) :
    ((coefficientSequenceEvaluation l E W m).obj M).val.presheaf.obj U ⟶
      ((coefficientSequenceEvaluation l E W n).obj M).val.presheaf.obj U :=
  restrictedUnderlying (normalizedDVRQuotient l E W h)
    ((coefficientSequenceTransition l E W h).app M) U

private theorem transitionAb_fac (M : coefficientSequenceModules l E W) {m n : ℕ}
    (h : n ≤ m) (U : W.ProEtᵒᵖ) :
    eqToHom (coefficientSequenceEvaluationAb_eq l E W M m U).symm ≫
        transitionAb l E W M h U ≫ eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U) =
      M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op := by
  unfold transitionAb
  apply restrictedUnderlying_fac _ _ _
    (coefficientSequenceEvaluationAb_eq l E W M m U)
    (coefficientSequenceEvaluationAb_eq l E W M n U)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W M h U)
  unfold coefficientSequenceTransition
  exact (coefficientSequenceTransition_exists l E W h).exists.choose_spec M U

@[irreducible] private def restrictCompIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (e : f ≫ g = h) :
    SheafOfModules.restrictScalars.{u} g ⋙ SheafOfModules.restrictScalars.{u} f ≅
      SheafOfModules.restrictScalars.{u} h :=
  let e₀ : SheafOfModules.restrictScalars.{u} g ⋙ SheafOfModules.restrictScalars.{u} f ≅
      SheafOfModules.restrictScalars.{u} (f ≫ g) := normalizedDVRRestrictionCompIso f g
  e₀ ≪≫ eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{u} z) e)

private theorem restrictCompIso_inv_underlying
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (e : f ≫ g = h) (M : SheafOfModules.{u} T) (U : Cᵒᵖ) :
    ((SheafOfModules.toSheaf R).map ((restrictCompIso f g h e).inv.app M)).hom.app U =
      𝟙 (M.val.presheaf.obj U) := by
  cases e
  unfold restrictCompIso normalizedDVRRestrictionCompIso
  rfl


private theorem restrictedUnderlying_heq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat} (f : R ⟶ S)
    {M : SheafOfModules.{u} R} {N : SheafOfModules.{u} S}
    (g : M ⟶ (SheafOfModules.restrictScalars f).obj N) (U : Cᵒᵖ)
    {X Y : AddCommGrpCat.{u}}
    (eM : M.val.presheaf.obj U = X) (eN : N.val.presheaf.obj U = Y)
    (t : X ⟶ Y)
    (h : eqToHom eM.symm ≫ restrictedUnderlying f g U ≫ eqToHom eN = t) :
    HEq (fun x : M.val.obj U ↦ (g.val.app U) x) (fun x : X ↦ t x) := by
  cases eM
  cases eN
  apply heq_of_eq
  funext x
  have hx := congrArg (fun z ↦ z x) h
  exact hx

private theorem transition_heq (M : coefficientSequenceModules l E W) {m n : ℕ}
    (h : n ≤ m) (U : W.ProEtᵒᵖ) :
    HEq (fun x : ((coefficientSequenceEvaluation l E W m).obj M).val.obj U ↦
      ((((coefficientSequenceTransition l E W h).app M).val.app U) x))
      (fun x : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  exact restrictedUnderlying_heq (normalizedDVRQuotient l E W h)
    ((coefficientSequenceTransition l E W h).app M) U
    (coefficientSequenceEvaluationAb_eq l E W M m U)
    (coefficientSequenceEvaluationAb_eq l E W M n U) _
    (transitionAb_fac l E W M h U)

private theorem moduleHom_eq_of_heq
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    {M₀ M₁ N₀ N₁ : SheafOfModules.{u} R} (e₀ : M₀ = N₀) (e₁ : M₁ = N₁)
    (f : M₀ ⟶ M₁) (g : N₀ ⟶ N₁)
    (h : ∀ U, HEq (fun x : M₀.val.obj U ↦ (f.val.app U) x)
      (fun x : N₀.val.obj U ↦ (g.val.app U) x)) :
    f ≫ eqToHom e₁ = eqToHom e₀ ≫ g := by
  cases e₀
  cases e₁
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  ext U x
  exact congrFun (eq_of_heq (h U)) x

private theorem restrictionComposite_heq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (he : f ≫ g = h) {M : SheafOfModules.{u} S} {N : SheafOfModules.{u} T}
    (τ : M ⟶ (SheafOfModules.restrictScalars g).obj N) (U : Cᵒᵖ) :
    HEq (fun x : ((SheafOfModules.restrictScalars f).obj M).val.obj U ↦
      (((SheafOfModules.restrictScalars f).map τ ≫
        (restrictCompIso f g h he).hom.app N).val.app U) x)
      (fun x : M.val.obj U ↦ (τ.val.app U) x) := by
  cases he
  unfold restrictCompIso normalizedDVRRestrictionCompIso
  rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projectionComp {m n : ℕ} (h : n ≤ m) :
    (sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W m) ≫
      normalizedDVRQuotient l E W h =
    (sheafCompose (Scheme.ProEt.topology W)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E W n) :=
  limit.w (integralCoefficientSheafSystem l E W) (homOfLE h).op

private abbrev compO {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ scalarReductionRestriction l E W m ≅
      scalarReductionRestriction l E W n :=
  restrictCompIso ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W m))
    (normalizedDVRQuotient l E W h)
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
    (projectionComp l E W h)

private theorem restrictedTransition (M : coefficientSequenceModules l E W)
    {m n : ℕ} (h : n ≤ m) :
    ((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app M =
      (eqToIso (coefficientSequenceRestriction_evaluation l E W m)).hom.app M ≫
        (scalarReductionRestriction l E W m).map
          ((coefficientSequenceTransition l E W h).app M) ≫
        (compO l E W h).hom.app ((coefficientSequenceEvaluation l E W n).obj M) := by
  have hU := (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  simp only [eqToIso.hom, eqToHom_app]
  apply moduleHom_eq_of_heq (hU.1 M m) (hU.1 M n)
  intro U
  have hτ := restrictionComposite_heq
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W m))
    (normalizedDVRQuotient l E W h)
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n))
    (projectionComp l E W h)
    ((coefficientSequenceTransition l E W h).app M) U
  exact (hU.2.1 M m n h U).trans (hτ.trans (transition_heq l E W M h U)).symm

private theorem derivedTransition_eq {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedTransition l E W h =
      CategoryTheory.derivedTransition (coefficientSequenceEvaluation l E W m)
        (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientSequenceTransition l E W h) := by
  unfold coefficientSequenceDerivedTransition CategoryTheory.derivedTransition
  rfl

private theorem restrictedEvaluation_eq (n : ℕ) :
    coefficientRestrictedEvaluationIso l E W n = CategoryTheory.derivedEvaluationIso
      (coefficientSequenceRestriction l E W)
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
      (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) := by
  unfold coefficientRestrictedEvaluationIso CategoryTheory.derivedEvaluationIso
  rfl

end WeilConjectures

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The total-limit projection at level m followed by the tower transition is the
projection at level n. -/
private theorem towerProjection_transition {m n : ℕ} (h : n ≤ m) :
    coefficientConstantTowerProjection l E W m ≫
      CategoryTheory.derivedMap ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op m))
        ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
        ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op) =
    coefficientConstantTowerProjection l E W n := by
  apply (coefficientConstantTowerProjection_exists l E W n).unique ?_
    (coefficientConstantTowerProjection_exists l E W n).choose_spec.1
  intro I _
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc]
  erw [CategoryTheory.derivedMap_fac]
  erw [← Category.assoc, (coefficientConstantTowerProjection_exists l E W m).choose_spec.1 I]
  rw [Category.assoc, ← DerivedCategory.Q.map_comp]
  congr 2
  ext p : 1
  exact limit.w (I.X p) (homOfLE h).op

/-- The total-limit projections are compatible with the quotient transitions. -/
private theorem projection_transition (N : coefficientSequenceDerived l E W)
    {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceProjection l E W m).app N ≫
        (coefficientFiniteDerivedRestriction l E W m).map
          ((coefficientSequenceDerivedTransition l E W h).app N) ≫
        (Functor.mapDerivedCategoryCompNatIso (compO l E W h)).hom.app
          ((coefficientSequenceDerivedEvaluation l E W n).obj N) =
      (coefficientSequenceProjection l E W n).app N := by
  have hs := CategoryTheory.derivedSquare
    (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op m))
    (coefficientSequenceEvaluation l E W m) (scalarReductionRestriction l E W m)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
    (scalarReductionRestriction l E W n)
    (eqToIso (coefficientSequenceRestriction_evaluation l E W m))
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n))
    (compO l E W h)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op)
    (coefficientSequenceTransition l E W h) (fun M ↦ restrictedTransition l E W M h) N
  rw [← restrictedEvaluation_eq, ← restrictedEvaluation_eq, ← derivedTransition_eq] at hs
  dsimp only [coefficientSequenceProjection, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← towerProjection_transition l E W h]
  rw [NatTrans.comp_app, Category.assoc, Category.assoc]
  erw [hs]
  rfl

private theorem bijective_comp_iso {C : Type*} [Category C] {X Y Z Z' : C}
    (e : X ≅ Y) (e' : Z ≅ Z') :
    Function.Bijective (fun f : Y ⟶ Z ↦ e.hom ≫ f ≫ e'.hom) :=
  ⟨fun f g hfg ↦ by
    have := congrArg (fun k ↦ e.inv ≫ k ≫ e'.inv) hfg
    simpa using this,
   fun g ↦ ⟨e.inv ≫ g ≫ e'.inv, by simp⟩⟩

/-- A left adjoint of the total limit whose finite evaluations are derived scalar
extension, compatibly with the adjunction units and the total-limit projections, takes
values in normalized coefficient systems.

Source: Stacks 0941 and 07A6.

Proof: under the finite scalar adjunctions and the evaluation isomorphisms, the map
`f ↦ τ ≫ Res f` becomes the composition with the restriction comparison
`Res_m ∘ Res_{m,n} ≅ Res_n`. This uses the unit-projection identity at both levels and
the compatibility of total-limit projections with the quotient transitions. -/
theorem isNormalizedCoefficientSequence_of_unitProjection
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (ρ : ∀ n : ℕ, L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n)
    (hunitproj : ∀ (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
      adj.unit.app P ≫ (coefficientSequenceProjection l E W n).app (L.obj P) =
        (coefficientFiniteAdjunction l E W n).unit.app P ≫
          (coefficientFiniteDerivedRestriction l E W n).map ((ρ n).inv.app P))
    (P : DerivedCategory (scalarReductionSource l E W)) :
    IsNormalizedCoefficientSequence l E W (L.obj P) := by
  intro m n h X
  let c := Functor.mapDerivedCategoryCompNatIso (compO l E W h)
  let Φn := fun f : (coefficientSequenceDerivedEvaluation l E W n).obj (L.obj P) ⟶ X ↦
    (coefficientFiniteAdjunction l E W n).homEquiv _ _ ((ρ n).inv.app P ≫ f)
  let Φm := fun g : (coefficientSequenceDerivedEvaluation l E W m).obj (L.obj P) ⟶
      (normalizedDVRRes l E W h).obj X ↦
    (coefficientFiniteAdjunction l E W m).homEquiv _ _ ((ρ m).inv.app P ≫ g) ≫ c.hom.app X
  have hn₀ := bijective_comp_iso ((ρ n).app P).symm (Iso.refl X)
  simp only [Iso.symm_hom, Iso.app_inv, Iso.refl_hom, Category.comp_id] at hn₀
  have hΦn : Function.Bijective Φn :=
    ((coefficientFiniteAdjunction l E W n).homEquiv _ _).bijective.comp hn₀
  have hm₀ := bijective_comp_iso ((ρ m).app P).symm (Iso.refl ((normalizedDVRRes l E W h).obj X))
  simp only [Iso.symm_hom, Iso.app_inv, Iso.refl_hom, Category.comp_id] at hm₀
  have hΦm : Function.Bijective Φm := by
    have h₁ := ((coefficientFiniteAdjunction l E W m).homEquiv P
      ((normalizedDVRRes l E W h).obj X)).bijective.comp hm₀
    have h₂ := bijective_comp_iso (Iso.refl P) (c.app X)
    simp only [Iso.refl_hom, Category.id_comp, Iso.app_hom] at h₂
    exact h₂.comp h₁
  refine (Function.Bijective.of_comp_iff' hΦm _).1 ?_
  convert hΦn using 1
  funext f
  dsimp only [Function.comp_apply, Φm, Φn]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hunitproj P m), ← reassoc_of% (hunitproj P n)]
  have hc := c.hom.naturality f
  dsimp only [Functor.comp_map] at hc
  erw [hc]
  erw [← reassoc_of% (projection_transition l E W (L.obj P) h)]
  rfl

end WeilConjectures

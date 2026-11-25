/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle

/-! # Canonical Roos triangle of a completed-coefficient tower

Source: Stacks Tags 0941, 079P, 0BK6 and 0BK7.
(blueprint: lem-coef-constant-tower-roos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasLimitsOfShape ℕᵒᵖ A]

private def limComplexCone (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Cone I.asFunctor where
  pt := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) |>.obj I
  π := {
    app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
    naturality := by
      intro n m f
      ext i
      simp }

private def limComplexCone_isLimit (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (limComplexCone A I) := by
  apply HomologicalComplex.isLimitOfEval
  intro i
  exact limit.isLimit (I.X i)

variable [HasCountableProducts A] [CountableAB4Star A]
  [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]

private abbrev evD (n : ℕ) := ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
private abbrev evF (n : ℕ) := ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors
private def trD (n : ℕ) : evD A (n+1) ⟶ evD A n :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    _ _ (evD A (n+1)) (evD A n)
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ A).map (homOfLE n.le_succ).op) (.up ℤ)) DerivedCategory.Q)

omit [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A] [CountableAB4Star A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] in
private theorem trD_fac (n : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (trD A n).app (DerivedCategory.Q.obj I) ≫ (evF A n).hom.app I =
    (evF A (n+1)).hom.app I ≫
      DerivedCategory.Q.map (I.asFunctor.map (homOfLE n.le_succ).op) := by
  dsimp only [trD]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rfl

private theorem derivedLimitTriangle [EnoughInjectives A]
    (hP : HasCountableProducts (DerivedCategory A))
    (π : ∀ n, (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⟶ evD A n)
    (hπ : ∀ n (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
      (π n).app (DerivedCategory.Q.obj I) ≫ (evF A n).hom.app I =
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I))
    (X : DerivedCategory (ℕᵒᵖ ⥤ A)) :
    letI := hP
    ∃ δ, IsDerivedLimitTriangle (fun n ↦ (trD A n).app X)
      ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.obj X)
      (Pi.lift (fun n : ℕ ↦ (π n).app X)) δ := by
  let := hP
  let R := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  let : I.IsKInjective := hI
  obtain ⟨δ₀, hδ₀⟩ := derivedCategory_towerLimit_triangle A hP inferInstance I
    (limComplexCone A I) (limComplexCone_isLimit A I)
  let en (n : ℕ) : DerivedCategory.Q.obj (I.asFunctor.obj (op n)) ≅ (evD A n).obj X :=
    ((evF A n).app I).symm ≪≫ (evD A n).mapIso e.symm
  let eR : DerivedCategory.Q.obj (limComplexCone A I).pt ≅ R.obj X :=
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).symm ≪≫ R.mapIso e.symm
  let E := Pi.mapIso en
  have hEn (n : ℕ) : E.hom ≫ Pi.π _ n = Pi.π _ n ≫ (en n).hom := by simp [E]
  have hn (n : ℕ) : (en (n+1)).hom ≫ (trD A n).app X =
      DerivedCategory.Q.map (I.asFunctor.map (homOfLE n.le_succ).op) ≫ (en n).hom := by
    dsimp only [en, Iso.trans_hom, Iso.symm_hom, Iso.app, Functor.mapIso_hom]
    rw [Category.assoc, (trD A n).naturality e.inv]
    apply (cancel_epi ((evF A (n+1)).hom.app I)).1
    simp only [Iso.hom_inv_id_app_assoc]
    have hh := congrArg (fun z ↦ z ≫ (evF A n).inv.app I ≫ (evD A n).map e.inv)
      (trD_fac A n I)
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hh
  have hp : Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)) ≫ E.hom =
      eR.hom ≫ Pi.lift (fun n : ℕ ↦ (π n).app X) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hEn, Pi.lift_comp_π]
    rw [← Category.assoc]
    have hp₀ := Pi.lift_comp_π (fun n : ℕ ↦ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)) n
    have hh₀ := congrArg (fun z ↦ z ≫ (en n).hom) hp₀
    apply hh₀.trans
    dsimp only [eR, en, Iso.trans_hom, Iso.symm_hom, Iso.app, Functor.mapIso_hom]
    rw [Category.assoc, (π n).naturality e.inv]
    apply (cancel_epi
      ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).hom).1
    simp only [Iso.hom_inv_id_assoc]
    have hh := congrArg (fun z ↦ z ≫ (evF A n).inv.app I ≫ (evD A n).map e.inv)
      (hπ n I)
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hh.symm
  have ht : towerTransitionEndomorphism
      (fun n : ℕ ↦ DerivedCategory.Q.map (I.asFunctor.map (homOfLE n.le_succ).op)) ≫ E.hom =
      E.hom ≫ towerTransitionEndomorphism (fun n ↦ (trD A n).app X) := by
    exact towerTransitionEndomorphism_natural_backward _ _ (fun n ↦ (en n).hom) hn |>.symm
  refine ⟨E.inv ≫ δ₀ ≫ (shiftFunctor _ (1 : ℤ)).map eR.hom, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk _ _ eR E E hp ht (by simp))).mp hδ₀
end CategoryTheory

namespace WeilConjectures
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The canonical total limit of a completed-coefficient derived tower has the Roos
triangle with its resolution-normalized projections.
Source: Stacks Tags 0941, 079P, 0BK6 and 0BK7.
(blueprint: lem-coef-constant-tower-roos).

Proof: choose a simultaneous K-injective complex representing the tower. Evaluation
preserves K-injectivity. Its ordinary limit complex is the degreewise limit cone,
so the proved tower-limit Roos theorem gives a distinguished triangle. Exact
countable products on the pro-etale site supply both AB4-star and the products in
the derived category. Transport the triangle through the derived evaluation and
right-derived limit comparison isomorphisms. On each projection the normalization
formula for coefficientConstantTowerProjection identifies the transported first
arrow with the specified projection; localization of evaluation identifies the
successor transitions. Naturality transports the same equations from the chosen
K-injective representative to the original tower. -/
theorem coefficientConstantTower_roos
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
    (D : FiniteFieldDatum.{v}) (hl : l ≠ D.p)
    (X : coefficientSequenceRestrictedDerived l E W) :
    ∃ hp : HasProduct (fun n : ℕ ↦ (coefficientConstantTowerEvaluation l E W n).obj X),
      letI := hp
      ∃ δ, IsDerivedLimitTriangle
        (fun n : ℕ ↦ (normalizedDVRTowerTransition l E W D hl n.le_succ).app X)
        ((coefficientConstantTowerLimit l E W).obj X)
        (Pi.lift (fun n : ℕ ↦ (coefficientConstantTowerProjection l E W n).app X)) δ := by
  let A := scalarReductionSource l E W
  let : HasDerivedCategory A := HasDerivedCategory.standard _
  let : IsGrothendieckAbelian.{max u (t + 1)} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (Scheme.ProEt.countableProducts_exact.{t, u, 0} W
          (completedIntegralCommRingSheafUnrestricted l E W)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Limits.Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Limits.Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  have := CountableAB4Star.of_hasExactLimitsOfShape_nat A
  let hp := integralOperationsDerivedCountableProducts l E W
  have hpDerived : HasCountableProducts (DerivedCategory A) := hp
  let := hpDerived
  refine ⟨by change HasLimit _; infer_instance, ?_⟩
  apply CategoryTheory.derivedLimitTriangle A hp
    (fun n ↦ coefficientConstantTowerProjection l E W n)
  · intro n I hI
    unfold coefficientConstantTowerProjection
    exact (coefficientConstantTowerProjection_exists l E W n).choose_spec.1 I
end WeilConjectures

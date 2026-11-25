/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryTensorHorizontal
import all WeilConjectures.AlgebraicGeometry.ProjectionTensorCore.SemilinearTensorReductionCore

/-! # Representative square for normalized tensor horizontality

Source: Stacks 07A4 and 0941; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-horizontal-representative).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b c v r w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
namespace WeilConjectures
namespace HorizontalRepresentativeProof
noncomputable section

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] coefficientFiniteQuotientExistence
  coefficientFiniteQuotientDerivedExistence coefficientFiniteQuotientModel
  coefficientFiniteQuotientExtension coefficientFiniteQuotientUnitSection
  SheafOfModules.monoidalCategory scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionExtension coefficientFiniteQuotientDerived HasDerivedCategory.standard
  CoefficientClosedStructure.tensor coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology constantSheaf coefficientSequenceEvaluation
  coefficientTotalTensor coefficientTensorGenerator

attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat

private def alpha {W : Scheme.{t}} (K : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m) :
    (coefficientFiniteQuotientDerived l E W hmn).obj
      (DerivedCategory.Q.obj (level l E K m)) ⟶ DerivedCategory.Q.obj (level l E K n) :=
  ((D.adjunction hmn).homEquiv _ _).symm
    (DerivedCategory.Q.map (transition l E K hmn) ≫
      (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors.inv.app (level l E K n))

private theorem transpose_from_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E : A ⥤ B} {U : B ⥤ A} (am : E ⊣ U)
    (I : A ⥤ C) (J : B ⥤ D) {F : C ⥤ D} {R : D ⥤ C} (ad : F ⊣ R)
    (ρ : J ⋙ R ≅ U ⋙ I) (P : A) (ε : F.obj (I.obj P) ⟶ J.obj (E.obj P))
    (hu : ad.unit.app (I.obj P) ≫ R.map ε ≫ ρ.hom.app (E.obj P) =
      I.map (am.unit.app P)) (H : B) (g : P ⟶ U.obj H) :
    (ad.homEquiv _ _).symm (I.map g ≫ ρ.inv.app H) =
      ε ≫ J.map ((am.homEquiv _ _).symm g) := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, ad.homEquiv_unit, R.map_comp, ← Category.assoc]
  have hu' : ad.unit.app (I.obj P) ≫ R.map ε =
      I.map (am.unit.app P) ≫ ρ.inv.app (E.obj P) := by
    apply (cancel_mono (ρ.hom.app (E.obj P))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact hu.trans (Category.comp_id _).symm
  rw [hu', Category.assoc]
  have hn := ρ.inv.naturality ((am.homEquiv P H).symm g)
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← I.map_comp]
  have hg : am.unit.app P ≫ U.map ((am.homEquiv P H).symm g) = g := by
    exact (am.homEquiv_unit P H ((am.homEquiv P H).symm g)).symm.trans
      ((am.homEquiv P H).apply_symm_apply g)
  rw [hg]

private theorem alpha_model {W : Scheme.{t}} (P : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) (level l E P m)) :
    alpha l E P S D hmn =
      (coefficientFiniteQuotientModel l E W hmn (level l E P m) hP).hom ≫
        DerivedCategory.Q.map (ordinaryAlpha l E P S D hmn) := by
  exact transpose_from_unit
    ((D.ordinaryAdjunction hmn).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q (D.adjunction hmn)
    (normalizedDVRModuleRes l E W hmn).mapDerivedCategoryFactors
    (level l E P m)
    (coefficientFiniteQuotientModel l E W hmn (level l E P m) hP).hom
    (D.unit_model hmn (level l E P m) hP) (level l E P n)
    (transition l E P hmn)

private theorem quotient_map_eq_Qmap {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] {P Q : CochainComplex B ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality f
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
  erw [Category.comp_id, Category.id_comp] at h
  exact h

private theorem cochain_comparison_eq {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ T ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ)
    [IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))] :
    ((T.mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
        (DerivedCategory.quotientCompQhIso _).app _).hom) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  change T.map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
  erw [T.map_id]
  erw [Category.id_comp, Category.comp_id]
  rfl

private theorem scalar_model_naturality {W : Scheme.{t}} {m n : ℕ} (hmn : n ≤ m)
    {P Q : CochainComplex (normalizedDVRModules l E W m) ℤ}
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) Q) (f : P ⟶ Q) :
    (coefficientFiniteQuotientDerived l E W hmn).map (DerivedCategory.Q.map f) ≫
        (coefficientFiniteQuotientModel l E W hmn Q hQ).hom =
      (coefficientFiniteQuotientModel l E W hmn P hP).hom ≫
        DerivedCategory.Q.map
          (((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).map f)
        := by
  have hp : (coefficientFiniteQuotientModel l E W hmn P hP).hom =
      (coefficientFiniteQuotientCounit l E W hmn).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    have := coefficientFiniteQuotientCounit_isIso l E W hmn P hP
    unfold coefficientFiniteQuotientModel
    exact cochain_comparison_eq (coefficientFiniteQuotientExtension l E W hmn)
      (coefficientFiniteQuotientDerived l E W hmn) (coefficientFiniteQuotientCounit l E W hmn) P
  have hq : (coefficientFiniteQuotientModel l E W hmn Q hQ).hom =
      (coefficientFiniteQuotientCounit l E W hmn).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) := by
    have := coefficientFiniteQuotientCounit_isIso l E W hmn Q hQ
    unfold coefficientFiniteQuotientModel
    exact cochain_comparison_eq (coefficientFiniteQuotientExtension l E W hmn)
      (coefficientFiniteQuotientDerived l E W hmn) (coefficientFiniteQuotientCounit l E W hmn) Q
  rw [hp, hq]
  have h := (coefficientFiniteQuotientCounit l E W hmn).naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map f)
  change (coefficientFiniteQuotientDerived l E W hmn).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f)) ≫ _ =
    _ ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      (((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).map f)) at h
  rw [quotient_map_eq_Qmap, quotient_map_eq_Qmap] at h
  exact h

private theorem tensor_model_naturality {W : Scheme.{t}}
    (S : CoefficientDerivedSystemTensors l E W) (n : ℕ)
    (P P' Q Q' : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) P')
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q)
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) Q') (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((finiteTensor l E W n).map (Prod.mkHom f g)) ≫
        ((S.finiteTensorModel n).iso _ _ _ P' Q' hP' hQ').hom =
      ((S.finiteTensorModel n).iso _ _ _ P Q hP hQ).hom ≫
        (S.finiteClosed n).tensor.map (Prod.mkHom (DerivedCategory.Q.map f)
          (DerivedCategory.Q.map g)) := by
  let ρ : ObjectProperty (CochainComplex (normalizedDVRModules l E W n) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
  let f' : (⟨P, hP⟩ : ρ.FullSubcategory) ⟶ ⟨P', hP'⟩ := ObjectProperty.homMk f
  let g' : (⟨Q, hQ⟩ : ρ.FullSubcategory) ⟶ ⟨Q', hQ'⟩ := ObjectProperty.homMk g
  exact (S.finiteTensorModel n).comparison.hom.naturality (Prod.mkHom f' g')

private theorem map_pair_comp {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ B) {a b c d e f : A}
    (u : a ⟶ b) (v : b ⟶ c) (x : d ⟶ e) (y : e ⟶ f) :
    T.map (Prod.mkHom (u ≫ v) (x ≫ y)) =
      T.map (Prod.mkHom u x) ≫ T.map (Prod.mkHom v y) :=
  T.map_comp (Prod.mkHom u x) (Prod.mkHom v y)

private theorem paste_tensor_comparisons {C : Type*} [Category C]
    {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ D₀ D₁ : C}
    (ev : A₀ ⟶ A₁) (tm : A₁ ⟶ A₂) (scalarTensor : A₂ ⟶ B₀)
    (scalarPair : B₀ ⟶ B₁) (factorPair : B₁ ⟶ B₂)
    (totalScalar : A₁ ⟶ C₀) (ordinaryComp : C₀ ⟶ C₁) (tensorAfter : C₁ ⟶ B₁)
    (tensorFactor : C₁ ⟶ C₂) (tensorEnd : C₂ ⟶ B₂)
    (scalarBefore : A₀ ⟶ D₀) (evalScalar : D₀ ⟶ C₀)
    (ordinaryAdj : D₀ ⟶ D₁) (evalEnd : D₁ ⟶ C₂)
    (hd : tm ≫ scalarTensor ≫ scalarPair = totalScalar ≫ ordinaryComp ≫ tensorAfter)
    (hn : tensorFactor ≫ tensorEnd = tensorAfter ≫ factorPair)
    (hs : ev ≫ totalScalar = scalarBefore ≫ evalScalar)
    (ho : evalScalar ≫ ordinaryComp ≫ tensorFactor = ordinaryAdj ≫ evalEnd) :
    (ev ≫ tm) ≫ scalarTensor ≫ scalarPair ≫ factorPair =
      (scalarBefore ≫ ordinaryAdj) ≫ evalEnd ≫ tensorEnd := by
  calc
    _ = ev ≫ totalScalar ≫ ordinaryComp ≫ tensorAfter ≫ factorPair := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ ev ≫ f ≫ factorPair) hd
    _ = ev ≫ totalScalar ≫ ordinaryComp ≫ tensorFactor ≫ tensorEnd := by rw [hn]
    _ = scalarBefore ≫ evalScalar ≫ ordinaryComp ≫ tensorFactor ≫ tensorEnd := by
      rw [← Category.assoc, hs]
      try simp only [Category.assoc]
    _ = (scalarBefore ≫ ordinaryAdj) ≫ evalEnd ≫ tensorEnd := by
      simpa only [Category.assoc] using
        congrArg (fun h ↦ scalarBefore ≫ h ≫ tensorEnd) ho

private noncomputable def comparison {W : Scheme.{t}} (P Q : Complex l E W) (n : ℕ)
    (S : CoefficientDerivedSystemTensors l E W)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) (level l E P n))
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) (level l E Q n)) :
    DerivedCategory.Q.obj (level l E (total l E P Q) n) ≅
      (S.finiteClosed n).tensor.obj
        (DerivedCategory.Q.obj (level l E P n), DerivedCategory.Q.obj (level l E Q n)) :=
  DerivedCategory.Q.mapIso (coefficientEvaluationTensorIso l E W n P Q) ≪≫
    (S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n)
      (level l E P n) (level l E Q n) hP hQ

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors CoefficientTensorModels.iso

private theorem strict_tensor {W : Scheme.{t}} (U V : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (hUm : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) (level l E U m))
    (hVm : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) (level l E V m))
    (hUn : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) (level l E U n))
    (hVn : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) (level l E V n))
    (hTot : CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W m) (level l E (total l E U V) m)) :
    (coefficientFiniteQuotientDerived l E W hmn).map
        (comparison l E U V m S hUm hVm).hom ≫
      (D.tensor hmn).hom.app
        (DerivedCategory.Q.obj (level l E U m), DerivedCategory.Q.obj (level l E V m)) ≫
      (S.finiteClosed n).tensor.map
        (Prod.mkHom (alpha l E U S D hmn) (alpha l E V S D hmn)) =
    alpha l E (total l E U V) S D hmn ≫ (comparison l E U V n S hUn hVn).hom := by
  classical
  let F := (coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)
  let T := coefficientFiniteQuotientDerived l E W hmn
  let B := (S.finiteClosed n).tensor
  let em := coefficientEvaluationTensorIso l E W m U V
  let en := coefficientEvaluationTensorIso l E W n U V
  let f := ordinaryAlpha l E U S D hmn
  let g := ordinaryAlpha l E V S D hmn
  let z := ordinaryAlpha l E (total l E U V) S D hmn
  have htm := coefficientTotalTensor_isKFlat.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W m) (level l E U m) (level l E V m) hUm hVm
  obtain ⟨e, he, hd⟩ := D.tensor_model hmn (level l E U m) (level l E V m) hUm hVm
  have ho := coefficientOrdinaryTensorHorizontal l E U V S D hmn e he
  let km := (S.finiteTensorModel m).iso _ _ _
    (level l E U m) (level l E V m) hUm hVm
  let kn := (S.finiteTensorModel n).iso _ _ _
    (level l E U n) (level l E V n) hUn hVn
  let ke := (S.finiteTensorModel n).iso _ _ _
    (F.obj (level l E U m)) (F.obj (level l E V m))
    (D.preservesKFlat hmn _ hUm) (D.preservesKFlat hmn _ hVm)
  let su := (coefficientFiniteQuotientModel l E W hmn (level l E U m) hUm).hom
  let sv := (coefficientFiniteQuotientModel l E W hmn (level l E V m) hVm).hom
  let st := (coefficientFiniteQuotientModel l E W hmn _ htm).hom
  let so := (coefficientFiniteQuotientModel l E W hmn _ hTot).hom
  let qf := DerivedCategory.Q.map f
  let qg := DerivedCategory.Q.map g
  let qt := DerivedCategory.Q.map ((finiteTensor l E W n).map (Prod.mkHom f g))
  have hn : qt ≫ kn.hom = ke.hom ≫ B.map (Prod.mkHom qf qg) :=
    tensor_model_naturality l E S n _ _ _ _
      (D.preservesKFlat hmn _ hUm) hUn
      (D.preservesKFlat hmn _ hVm) hVn f g
  have hs : T.map (DerivedCategory.Q.map em.hom) ≫ st =
      so ≫ DerivedCategory.Q.map (F.map em.hom) :=
    scalar_model_naturality l E hmn hTot htm em.hom
  change T.map ((DerivedCategory.Q.map em.hom) ≫ km.hom) ≫
      (D.tensor hmn).hom.app _ ≫
      B.map (Prod.mkHom (alpha l E U S D hmn) (alpha l E V S D hmn)) =
    alpha l E (total l E U V) S D hmn ≫ DerivedCategory.Q.map en.hom ≫ kn.hom
  rw [alpha_model l E U S D hmn hUm, alpha_model l E V S D hmn hVm,
    alpha_model l E (total l E U V) S D hmn hTot]
  change T.map ((DerivedCategory.Q.map em.hom) ≫ km.hom) ≫
      (D.tensor hmn).hom.app _ ≫ B.map (Prod.mkHom (su ≫ qf) (sv ≫ qg)) =
    (so ≫ DerivedCategory.Q.map z) ≫ DerivedCategory.Q.map en.hom ≫ kn.hom
  rw [map_pair_comp, T.map_comp]
  have hq := congrArg (fun f ↦ DerivedCategory.Q.map f) ho
  simp only [Functor.map_comp] at hq
  exact paste_tensor_comparisons (T.map (DerivedCategory.Q.map em.hom)) (T.map km.hom)
      ((D.tensor hmn).hom.app _) (B.map (Prod.mkHom su sv))
      (B.map (Prod.mkHom qf qg)) st (DerivedCategory.Q.map e.hom) ke.hom qt kn.hom
      so (DerivedCategory.Q.map (F.map em.hom))
      (DerivedCategory.Q.map z) (DerivedCategory.Q.map en.hom) hd hn hs hq

private theorem transition_factor {W : Scheme.{t}} {m n : ℕ} (h : n ≤ m)
    (P : Complex l E W) :
    (coefficientSequenceDerivedTransition l E W h).app (DerivedCategory.Q.obj P) ≫
      (normalizedDVRRes l E W h).map
        ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P) ≫
      (normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app
        (level l E P n) =
    (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map (transition l E P h) := by
  have hf := localized_transition_fac
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (normalizedDVRModuleRes l E W h) (coefficientSequenceTransition l E W h) P
  have hc : (Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceEvaluation l E W n ⋙
        normalizedDVRModuleRes l E W h)) (.up ℤ)).inv.app P = 𝟙 _ := rfl
  rw [hc] at hf
  erw [Category.comp_id] at hf
  unfold coefficientSequenceDerivedTransition normalizedDVRRes
  simp only [NatTrans.comp_app, Category.assoc]
  exact hf

private theorem adjoint_factor {W : Scheme.{t}}
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    (P : Complex l E W) :
    coefficientSequenceTransitionAdjoint l E W S D h (DerivedCategory.Q.obj P) ≫
      (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app P =
    (coefficientFiniteQuotientDerived l E W h).map
        ((coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.hom.app P) ≫
      alpha l E P S D h := by
  apply ((D.adjunction h).homEquiv _ _).injective
  rw [(D.adjunction h).homEquiv_naturality_left,
    (D.adjunction h).homEquiv_naturality_right]
  simp only [coefficientSequenceTransitionAdjoint, alpha, Functor.comp_obj,
    Equiv.apply_symm_apply]
  apply (cancel_mono
    ((normalizedDVRModuleRes l E W h).mapDerivedCategoryFactors.hom.app (level l E P n))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact transition_factor l E h P

private theorem adjoint_naturality {W : Scheme.{t}}
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (h : n ≤ m)
    {P Q : coefficientSequenceDerived l E W} (f : P ⟶ Q) :
    (coefficientFiniteQuotientDerived l E W h).map
        ((coefficientSequenceDerivedEvaluation l E W m).map f) ≫
      coefficientSequenceTransitionAdjoint l E W S D h Q =
    coefficientSequenceTransitionAdjoint l E W S D h P ≫
      (coefficientSequenceDerivedEvaluation l E W n).map f := by
  apply ((D.adjunction h).homEquiv _ _).injective
  rw [(D.adjunction h).homEquiv_naturality_left,
    (D.adjunction h).homEquiv_naturality_right]
  simp only [coefficientSequenceTransitionAdjoint, Equiv.apply_symm_apply]
  exact (coefficientSequenceDerivedTransition l E W h).naturality f

-- This diagram is independent of coefficient categories and of the chosen resolutions.
private theorem paste_horizontal {B C : Type*} [Category B] [Category C]
    (F : B ⥤ C) (Bm : B × B ⥤ B) (Bn : C × C ⥤ C)
    (γ : Bm ⋙ F ⟶ (F.prod F) ⋙ Bn)
    {a b z t p q c : B} {a' b' z' t' p' q' c' : C}
    (i : z ≅ t) (j : z' ≅ t') (em : t ⟶ Bm.obj (a, b))
    (en : t' ⟶ Bn.obj (a', b'))
    (r : F.obj t ⟶ t') (rp : F.obj a ⟶ a') (rq : F.obj b ⟶ b')
    (rz : F.obj z ⟶ z')
    (fm : a ≅ p) (gm : b ≅ q) (fn : a' ≅ p') (gn : b' ≅ q')
    (zm : z ≅ c) (zn : z' ≅ c') (cm : c ≅ Bm.obj (p, q))
    (cn : c' ≅ Bn.obj (p', q'))
    (ap : F.obj p ⟶ p') (aq : F.obj q ⟶ q') (az : F.obj c ⟶ c')
    (hem : i.hom ≫ em ≫ Bm.map (Prod.mkHom fm.hom gm.hom) = zm.hom ≫ cm.hom)
    (hen : j.hom ≫ en ≫ Bn.map (Prod.mkHom fn.hom gn.hom) = zn.hom ≫ cn.hom)
    (hp : rp ≫ fn.hom = F.map fm.hom ≫ ap)
    (hq : rq ≫ gn.hom = F.map gm.hom ≫ aq)
    (hz : rz ≫ zn.hom = F.map zm.hom ≫ az)
    (hi : F.map i.hom ≫ r = rz ≫ j.hom)
    (ht : F.map cm.hom ≫ γ.app (p, q) ≫ Bn.map (Prod.mkHom ap aq) = az ≫ cn.hom) :
    F.map em ≫ γ.app (a, b) ≫ Bn.map (Prod.mkHom rp rq) = r ≫ en := by
  have hn := γ.naturality (Prod.mkHom fm.hom gm.hom)
  change F.map (Bm.map (Prod.mkHom fm.hom gm.hom)) ≫ γ.app (p, q) =
    γ.app (a, b) ≫ Bn.map (Prod.mkHom (F.map fm.hom) (F.map gm.hom)) at hn
  apply (cancel_epi (F.map i.hom)).1
  have : IsIso (Prod.mkHom fn.hom gn.hom) := (fn.prod gn).isIso_hom
  have : IsIso (Bn.map (Prod.mkHom fn.hom gn.hom)) := Bn.map_isIso _
  apply (cancel_mono (Bn.map (Prod.mkHom fn.hom gn.hom))).1
  simp only [Category.assoc, ← Bn.map_comp, prod_comp, hp, hq]
  rw [map_pair_comp]
  rw [← reassoc_of% hn, ← F.map_comp_assoc, ← F.map_comp_assoc]
  try simp only [Category.assoc]
  rw [hem, F.map_comp]
  try simp only [Category.assoc]
  rw [ht, ← reassoc_of% hz, reassoc_of% hi]
  exact congrArg (fun f ↦ rz ≫ f) hen.symm

end
end HorizontalRepresentativeProof

open HorizontalRepresentativeProof

attribute [local irreducible] coefficientFiniteQuotientDerived HasDerivedCategory.standard
  CoefficientClosedStructure.tensor Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors coefficientTotalTensor coefficientSequenceCommRingSheaf
  coefficientSequenceEvaluation coefficientSystemTensorModelIso coefficientEvaluationTensorIso
  CoefficientTensorModels.iso

attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The horizontal tensor square after choosing simultaneous K-flat representatives.
Source: Stacks 07A4 and 0941, and Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-horizontal-representative).

Proof: evaluate the two chosen K-flat complexes at level `m`, apply the ordinary
pure-tensor quotient comparison, and use the representative normalization fields of
`hE` and `Q.tensor_model`. The two chain maps agree on every local pure tensor; the
total-complex summand equations then give the displayed localized equality. -/
theorem coefficientNormalizedTensorHorizontalRepresentative
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors)
    (P V : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hV : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) V)
    {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientDerived l E W h).map
        ((R.evaluationTensor m).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)) ≫
      (Q.tensor h).hom.app
        ((coefficientSequenceDerivedEvaluation l E W m).obj (DerivedCategory.Q.obj P),
          (coefficientSequenceDerivedEvaluation l E W m).obj (DerivedCategory.Q.obj V)) ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom
          (coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
            (DerivedCategory.Q.obj P))
          (coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
            (DerivedCategory.Q.obj V))) =
    coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
        (R.systemClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)) ≫
      (R.evaluationTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V) := by
  classical
  let S := R.toCoefficientDerivedSystemTensors
  let F := coefficientFiniteQuotientDerived l E W h
  let Em := coefficientSequenceDerivedEvaluation l E W m
  let En := coefficientSequenceDerivedEvaluation l E W n
  let Bm := (R.finiteClosed m).tensor
  let Bn := (R.finiteClosed n).tensor
  let Z := total l E P V
  let i := coefficientSystemTensorModelIso l E W S P V hP hV
  let fm := (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.app P
  let gm := (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.app V
  let fn := (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app P
  let gn := (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app V
  let zm := (coefficientSequenceEvaluation l E W m).mapDerivedCategoryFactors.app Z
  let zn := (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.app Z
  have hPm := (coefficientTensorModelPreservation l E W).2 P hP m
  have hVm := (coefficientTensorModelPreservation l E W).2 V hV m
  have hPn := (coefficientTensorModelPreservation l E W).2 P hP n
  have hVn := (coefficientTensorModelPreservation l E W).2 V hV n
  let cm := comparison l E P V m S hPm hVm
  let cn := comparison l E P V n S hPn hVn
  have hem : Em.map i.hom ≫ (R.evaluationTensor m).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V) ≫
      Bm.map (Prod.mkHom fm.hom gm.hom) = zm.hom ≫ cm.hom := by
    simpa only [CoefficientTensorComparisonSquare, comparison, Iso.trans_hom,
      Functor.mapIso_hom, coefficientFiniteTensorModelIso, S, Em, Bm, i, fm, gm, zm,
      Z, cm, Category.assoc, Iso.app_hom, Functor.comp_obj] using hE m P V hP hV
  have hen : En.map i.hom ≫ (R.evaluationTensor n).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V) ≫
      Bn.map (Prod.mkHom fn.hom gn.hom) = zn.hom ≫ cn.hom := by
    simpa only [CoefficientTensorComparisonSquare, comparison, Iso.trans_hom,
      Functor.mapIso_hom, coefficientFiniteTensorModelIso, S, En, Bn, i, fn, gn, zn,
      Z, cn, Category.assoc, Iso.app_hom, Functor.comp_obj] using hE n P V hP hV
  let red := coefficientSequenceTransitionAdjoint l E W S Q h
  have hp : red (DerivedCategory.Q.obj P) ≫ fn.hom =
      F.map fm.hom ≫ alpha l E P S Q h := adjoint_factor l E S Q h P
  have hv : red (DerivedCategory.Q.obj V) ≫ gn.hom =
      F.map gm.hom ≫ alpha l E V S Q h := adjoint_factor l E S Q h V
  have hz : red (DerivedCategory.Q.obj Z) ≫ zn.hom =
      F.map zm.hom ≫ alpha l E Z S Q h := adjoint_factor l E S Q h Z
  have hZ := coefficientTotalTensor_isKFlat.{u, t + 1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) P V hP hV
  have hZm := (coefficientTensorModelPreservation l E W).2 Z hZ m
  have hstrict := strict_tensor l E P V S Q h hPm hVm hPn hVn hZm
  exact paste_horizontal F Bm Bn (Q.tensor h).hom (Em.mapIso i) (En.mapIso i)
    ((R.evaluationTensor m).hom.app _) ((R.evaluationTensor n).hom.app _)
    (red (R.systemClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)))
    (red (DerivedCategory.Q.obj P)) (red (DerivedCategory.Q.obj V))
    (red (DerivedCategory.Q.obj Z)) fm gm fn gn zm zn cm cn
    (alpha l E P S Q h) (alpha l E V S Q h) (alpha l E Z S Q h)
    hem hen hp hv hz (adjoint_naturality l E S Q h i.hom) hstrict

end WeilConjectures

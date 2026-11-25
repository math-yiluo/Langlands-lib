/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # The normalized tower underlying a coefficient sequence

Source: Stacks Project, Tags 0940 and 0941; Bhatt--Scholze, Lemmas 3.5.4--3.5.7.
(blueprint: lem-coef-sequence-roos-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe d t u
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

private theorem idDerived_fac (K : CochainComplex D ℤ) :
    (Functor.mapDerivedCategoryIdIso D).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 D).mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryIdIso_hom_app]
  have hi : (Functor.mapHomologicalComplexIdIso D (.up ℤ)).hom.app K = 𝟙 K := by
    ext i
    simp
  erw [hi, DerivedCategory.Q.map_id, Category.comp_id]

private theorem unitDerived_fac (S : D ⥤ D) [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (e : S ≅ 𝟭 D)
    (K : CochainComplex D ℤ) :
    ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
      (DerivedCategory.Q.obj K)) =
      S.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [idDerived_fac]
  exact Functor.mapDerivedCategoryNatIso_fac e K

private theorem derivedTransition_id (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : D ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : S ≅ 𝟭 D) (τ : F ⟶ F ⋙ S)
    (hτ : ∀ M, τ.app M ≫ e.hom.app (F.obj M) = 𝟙 (F.obj M))
    (X : DerivedCategory C) :
    (derivedTransition F F S τ).app X ≫
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
        (F.mapDerivedCategory.obj X) = 𝟙 _ := by
  suffices hh : derivedTransition F F S τ ≫
      Functor.whiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom =
      (Functor.rightUnitor _).inv by
    exact congr_app hh X
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app]
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app K)).1
  have hnat := ((Functor.mapDerivedCategoryNatIso e ≪≫
    Functor.mapDerivedCategoryIdIso D).hom.naturality
      (F.mapDerivedCategoryFactors.hom.app K)).symm
  simp only [CategoryTheory.Functor.id_map] at hnat
  rw [Category.assoc]
  erw [hnat, unitDerived_fac]
  erw [derivedTransition_fac_assoc]
  rw [← DerivedCategory.Q.map_comp]
  have ht : (NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ≫
      (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := by
    ext i
    exact hτ _
  rw [ht, DerivedCategory.Q.map_id, Category.comp_id, Category.id_comp]

private theorem compDerived_inv_fac
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (S : B ⥤ E) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : B ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : S ⋙ R ≅ T) (K : CochainComplex B ℤ) :
    (Functor.mapDerivedCategoryCompNatIso e).inv.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) =
    T.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app K) := by
  have : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K)) := by
    change IsIso (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K))
    infer_instance
  apply (cancel_mono (DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K))).1
  have h := Functor.mapDerivedCategoryCompNatIso_hom_app_Q e K
  dsimp only [Functor.mapHomologicalComplexCompIsoHomOfIso] at h
  erw [Functor.mapHomologicalComplexCompIso_refl_hom_app, Category.id_comp] at h
  rw [Category.assoc, Category.assoc, ← h]
  rw [Iso.inv_hom_id_app_assoc]
  rw [Category.assoc, ← DerivedCategory.Q.map_comp]
  have hcomp : (NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app K ≫
      (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K = 𝟙 _ := by
    ext i
    exact e.inv_hom_id_app _
  erw [hcomp, DerivedCategory.Q.map_id, Category.comp_id]

private theorem derivedTransition_comp {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (H : C ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (S : B ⥤ E) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : B ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : S ⋙ R ≅ T) (τ₁ : F ⟶ G ⋙ R) (τ₂ : G ⟶ H ⋙ S) (τ₃ : F ⟶ H ⋙ T)
    (hc : ∀ M, τ₃.app M ≫ e.inv.app (H.obj M) = τ₁.app M ≫ R.map (τ₂.app M))
    (X : DerivedCategory C) :
    (derivedTransition F H T τ₃).app X ≫
        (Functor.mapDerivedCategoryCompNatIso e).inv.app (H.mapDerivedCategory.obj X) =
      (derivedTransition F G R τ₁).app X ≫
        R.mapDerivedCategory.map ((derivedTransition G H S τ₂).app X) := by
  suffices hh : derivedTransition F H T τ₃ ≫
      Functor.whiskerLeft H.mapDerivedCategory (Functor.mapDerivedCategoryCompNatIso e).inv =
      derivedTransition F G R τ₁ ≫
        Functor.whiskerRight (derivedTransition G H S τ₂) R.mapDerivedCategory by
    exact congr_app hh X
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (cancel_mono (R.mapDerivedCategory.map
    (S.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K)) ≫
    R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app
      ((H.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj
      ((H.mapHomologicalComplex (.up ℤ)).obj K)))).1
  have hn := (Functor.mapDerivedCategoryCompNatIso e).inv.naturality
    (H.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  rw [compDerived_inv_fac]
  erw [derivedTransition_fac_assoc]
  have h₂ := congrArg (fun z ↦ R.mapDerivedCategory.map z)
    (derivedTransition_fac G H S τ₂ K)
  simp only [CategoryTheory.Functor.map_comp] at h₂
  rw [reassoc_of% h₂]
  have hn₂ := R.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex τ₂ (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hn₂
  erw [hn₂, derivedTransition_fac_assoc]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 2
  ext i
  exact hc _
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
  completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  normalizedDVRResCompletedComp
private theorem restrictionTransport
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat} (f g : R ⟶ S) (h : f = g)
    (M : SheafOfModules.{u} S) (U : Cᵒᵖ) :
    ((SheafOfModules.toSheaf R).map
      ((eqToIso (congrArg (fun z ↦ SheafOfModules.restrictScalars.{u} z) h)).hom.app M)).hom.app U =
      𝟙 (M.val.presheaf.obj U) := by
  cases h
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
private abbrev unitO (n : ℕ) : normalizedDVRModuleRes l E W (Nat.le_refl n) ≅
    𝟭 (normalizedDVRModules l E W n) :=
  eqToIso (congrArg (fun f ↦ SheafOfModules.restrictScalars.{max u (t + 1)} f)
    ((integralCoefficientSheafSystem l E W).map_id (op n)))
private theorem transition_id (n : ℕ) :
    coefficientSequenceTransition l E W (Nat.le_refl n) ≫
      Functor.whiskerLeft (coefficientSequenceEvaluation l E W n) (unitO l E W n).hom =
      (Functor.rightUnitor (coefficientSequenceEvaluation l E W n)).inv := by
  apply NatTrans.ext
  funext M
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have h := (coefficientSequenceTransition_exists l E W (Nat.le_refl n)).exists.choose_spec M U
  have hId : normalizedDVRQuotient l E W (Nat.le_refl n) =
      𝟙 (integralCoefficientSheaf l E W n) :=
    (integralCoefficientSheafSystem l E W).map_id (op n)
  have hu := restrictionTransport _ _ hId
    ((coefficientSequenceEvaluation l E W n).obj M) U
  have ht : (forget₂ (ModuleCat.{max u (t+1)}
      ((integralCoefficientSheaf l E W n).obj.obj U)) AddCommGrpCat).map
      (((coefficientSequenceTransition l E W (Nat.le_refl n)).app M).val.app U) = 𝟙 _ := by
    have he : (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op =
        𝟙 (op (n, U.unop)) := rfl
    rw [he, CategoryTheory.Functor.map_id] at h
    apply (cancel_epi (eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U).symm)).1
    apply (cancel_mono (eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U))).1
    calc
      _ = eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U).symm ≫
          (forget₂ (ModuleCat.{max u (t+1)}
            ((integralCoefficientSheaf l E W n).obj.obj U)) AddCommGrpCat).map
            (((coefficientSequenceTransition_exists l E W
              (Nat.le_refl n)).exists.choose.app M).val.app U) ≫
          eqToHom (coefficientSequenceRestrictedEvaluationAb_eq l E W M (Nat.le_refl n) U) := by
        unfold coefficientSequenceTransition
        exact Category.assoc _ _ _
      _ = _ := h
      _ = _ := by
        have hc : (eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U).symm ≫
            𝟙 (((coefficientSequenceEvaluation l E W n).obj M).val.presheaf.obj U)) ≫
            eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U) =
            𝟙 (M.val.presheaf.obj (op (n, U.unop))) := by
          simp only [Category.comp_id, eqToHom_trans, eqToHom_refl]
        exact hc.symm
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app]
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have hh := congrArg (fun z ↦
    (forget₂ (ModuleCat.{max u (t+1)}
      ((integralCoefficientSheaf l E W n).obj.obj U)) AddCommGrpCat).map
        (((coefficientSequenceTransition l E W (Nat.le_refl n)).app M).val.app U) ≫ z) hu
  have hid : ((SheafOfModules.toSheaf (integralCoefficientSheaf l E W n)).map
      (𝟙 ((coefficientSequenceEvaluation l E W n).obj M))).hom.app U =
      𝟙 (((coefficientSequenceEvaluation l E W n).obj M).val.presheaf.obj U) := rfl
  exact hh.trans ((Category.comp_id _).trans (ht.trans hid.symm))

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

private theorem transitionAb_comp (M : coefficientSequenceModules l E W)
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
    (U : W.ProEtᵒᵖ) :
    transitionAb l E W M (hmn.trans hrm) U =
      transitionAb l E W M hrm U ≫ transitionAb l E W M hmn U := by
  apply (cancel_epi (eqToHom (coefficientSequenceEvaluationAb_eq l E W M r U).symm)).1
  apply (cancel_mono (eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U))).1
  have h₁ := transitionAb_fac l E W M hrm U
  have h₂ := transitionAb_fac l E W M hmn U
  have h₃ := transitionAb_fac l E W M (hmn.trans hrm) U
  have he :
      M.val.presheaf.map (Prod.mkHom (homOfLE hrm) (𝟙 U.unop)).op ≫
        M.val.presheaf.map (Prod.mkHom (homOfLE hmn) (𝟙 U.unop)).op =
      M.val.presheaf.map (Prod.mkHom (homOfLE (hmn.trans hrm)) (𝟙 U.unop)).op := by
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
  have hh := congrArg₂ (fun x y ↦ x ≫ y) h₁ h₂
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hh
  simpa only [Category.assoc] using h₃.trans (hh.trans he).symm

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

private theorem quotientComp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    normalizedDVRQuotient l E W hrm ≫ normalizedDVRQuotient l E W hmn =
      normalizedDVRQuotient l E W (hmn.trans hrm) :=
  ((integralCoefficientSheafSystem l E W).map_comp (homOfLE hrm).op (homOfLE hmn).op).symm

private abbrev compO {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    normalizedDVRModuleRes l E W hmn ⋙ normalizedDVRModuleRes l E W hrm ≅
      normalizedDVRModuleRes l E W (hmn.trans hrm) :=
  restrictCompIso (normalizedDVRQuotient l E W hrm) (normalizedDVRQuotient l E W hmn)
    (normalizedDVRQuotient l E W (hmn.trans hrm)) (quotientComp l E W hrm hmn)

private theorem restrictedMap
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat} (f : R ⟶ S)
    {M N : SheafOfModules.{u} S} (g : M ⟶ N) (U : Cᵒᵖ) :
    ((SheafOfModules.toSheaf R).map ((SheafOfModules.restrictScalars f).map g)).hom.app U =
      ((SheafOfModules.toSheaf S).map g).hom.app U := rfl

private theorem restrictionComposition_hom_eq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat} (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (he : f ≫ g = h)
    {M₀ : SheafOfModules.{u} R} {M₁ : SheafOfModules.{u} S} {M₂ : SheafOfModules.{u} T}
    (a : M₀ ⟶ (SheafOfModules.restrictScalars f).obj M₁)
    (b : M₁ ⟶ (SheafOfModules.restrictScalars g).obj M₂)
    (c : M₀ ⟶ (SheafOfModules.restrictScalars h).obj M₂)
    (hc : ∀ U, restrictedUnderlying h c U =
      restrictedUnderlying f a U ≫ restrictedUnderlying g b U) :
    c ≫ (restrictCompIso f g h he).inv.app M₂ =
      a ≫ (SheafOfModules.restrictScalars f).map b := by
  apply (SheafOfModules.toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have hh := congrArg (fun z ↦ restrictedUnderlying h c U ≫ z)
    (restrictCompIso_inv_underlying f g h he M₂ U)
  have hh' := congrArg (fun z ↦ restrictedUnderlying f a U ≫ z) (restrictedMap f b U)
  exact hh.trans ((Category.comp_id _).trans ((hc U).trans hh'.symm))

private theorem transition_comp (M : coefficientSequenceModules l E W)
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    (coefficientSequenceTransition l E W (hmn.trans hrm)).app M ≫
        (compO l E W hrm hmn).inv.app ((coefficientSequenceEvaluation l E W n).obj M) =
      (coefficientSequenceTransition l E W hrm).app M ≫
        (normalizedDVRModuleRes l E W hrm).map
          ((coefficientSequenceTransition l E W hmn).app M) := by
  exact restrictionComposition_hom_eq
    (normalizedDVRQuotient l E W hrm) (normalizedDVRQuotient l E W hmn)
    (normalizedDVRQuotient l E W (hmn.trans hrm)) (quotientComp l E W hrm hmn)
    ((coefficientSequenceTransition l E W hrm).app M)
    ((coefficientSequenceTransition l E W hmn).app M)
    ((coefficientSequenceTransition l E W (hmn.trans hrm)).app M)
    (fun U ↦ transitionAb_comp l E W M hrm hmn U)

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

private theorem completedProjectionComp {m n : ℕ} (h : n ≤ m) :
    completedIntegralCoefficientProjection l E W D hl m ≫ normalizedDVRQuotient l E W h =
      completedIntegralCoefficientProjection l E W D hl n := by
  unfold completedIntegralCoefficientProjection completedIntegralCoefficientSheaf
    completedIntegralCoefficientSheafUnrestricted
  exact limit.w (integralCoefficientSheafSystem l E W) (homOfLE h).op

private abbrev completedCompO {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E W h ⋙ completedIntegralRestrictScalars l E W D hl m ≅
      completedIntegralRestrictScalars l E W D hl n :=
  restrictCompIso (completedIntegralCoefficientProjection l E W D hl m)
    (normalizedDVRQuotient l E W h) (completedIntegralCoefficientProjection l E W D hl n)
    (completedProjectionComp l E W D hl h)

private theorem restrictedTransition (M : coefficientSequenceModules l E W)
    {m n : ℕ} (h : n ≤ m) :
    ((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app M =
      (eqToIso (coefficientSequenceRestriction_evaluation l E W m)).hom.app M ≫
        (completedIntegralRestrictScalars l E W D hl m).map
          ((coefficientSequenceTransition l E W h).app M) ≫
        (completedCompO l E W D hl h).hom.app ((coefficientSequenceEvaluation l E W n).obj M) := by
  have hU := (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  simp only [eqToIso.hom, eqToHom_app]
  apply moduleHom_eq_of_heq (hU.1 M m) (hU.1 M n)
  intro U
  have hτ := restrictionComposite_heq
    (completedIntegralCoefficientProjection l E W D hl m) (normalizedDVRQuotient l E W h)
    (completedIntegralCoefficientProjection l E W D hl n)
    (completedProjectionComp l E W D hl h)
    ((coefficientSequenceTransition l E W h).app M) U
  exact (hU.2.1 M m n h U).trans (hτ.trans (transition_heq l E W M h U)).symm

private theorem derivedTransition_eq {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedTransition l E W h =
      CategoryTheory.derivedTransition (coefficientSequenceEvaluation l E W m)
        (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
        (coefficientSequenceTransition l E W h) := by
  unfold coefficientSequenceDerivedTransition CategoryTheory.derivedTransition
  rfl

private theorem resComp_eq {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    normalizedDVRResComp l E W hrm hmn =
      Functor.mapDerivedCategoryCompNatIso (compO l E W hrm hmn) := by
  unfold normalizedDVRResComp Functor.mapDerivedCategoryCompNatIso compO restrictCompIso
  rfl

private theorem restrictedEvaluation_eq (n : ℕ) :
    coefficientRestrictedEvaluationIso l E W n = CategoryTheory.derivedEvaluationIso
      (coefficientSequenceRestriction l E W)
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
      (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) := by
  unfold coefficientRestrictedEvaluationIso CategoryTheory.derivedEvaluationIso
  rfl

private instance completedR_limits (n : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E W D hl n) :=
  (completedIntegralRestrictScalars_exact l E W D hl n).1

private instance completedR_colimits (n : ℕ) :
    PreservesFiniteColimits (completedIntegralRestrictScalars l E W D hl n) :=
  (completedIntegralRestrictScalars_exact l E W D hl n).2

private instance completedR_additive (n : ℕ) :
    (completedIntegralRestrictScalars l E W D hl n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t+1)}
    (completedIntegralCoefficientProjection l E W D hl n)).Additive

private theorem completedResComp_eq {m n : ℕ} (h : n ≤ m) :
    normalizedDVRResCompletedComp l E W D hl h =
      Functor.mapDerivedCategoryCompNatIso (completedCompO l E W D hl h) := by
  unfold normalizedDVRResCompletedComp Functor.mapDerivedCategoryCompNatIso
    completedCompO restrictCompIso
  rfl

private theorem towerTransition_eq {m n : ℕ} (h : n ≤ m) :
    normalizedDVRTowerTransition l E W D hl h = CategoryTheory.derivedMap
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op m))
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op) := by
  unfold normalizedDVRTowerTransition CategoryTheory.derivedMap
  rfl

private theorem derivedTransition_id (N : coefficientSequenceDerived l E W) (n : ℕ) :
    (coefficientSequenceDerivedTransition l E W (Nat.le_refl n)).app N ≫
      (normalizedDVRResUnit l E W n).hom.app
        ((coefficientSequenceDerivedEvaluation l E W n).obj N) = 𝟙 _ := by
  rw [derivedTransition_eq]
  exact CategoryTheory.derivedTransition_id
    (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W (Nat.le_refl n))
    (unitO l E W n) (coefficientSequenceTransition l E W (Nat.le_refl n))
    (fun M ↦ congr_app (transition_id l E W n) M) N

private theorem derivedTransition_comp (N : coefficientSequenceDerived l E W)
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    (coefficientSequenceDerivedTransition l E W (hmn.trans hrm)).app N ≫
        (normalizedDVRResComp l E W hrm hmn).inv.app
          ((coefficientSequenceDerivedEvaluation l E W n).obj N) =
      (coefficientSequenceDerivedTransition l E W hrm).app N ≫
        (normalizedDVRRes l E W hrm).map
          ((coefficientSequenceDerivedTransition l E W hmn).app N) := by
  rw [derivedTransition_eq, derivedTransition_eq, derivedTransition_eq, resComp_eq]
  exact CategoryTheory.derivedTransition_comp
    (coefficientSequenceEvaluation l E W r) (coefficientSequenceEvaluation l E W m)
    (normalizedDVRModuleRes l E W hrm) (coefficientSequenceEvaluation l E W n)
    (normalizedDVRModuleRes l E W hmn) (normalizedDVRModuleRes l E W (hmn.trans hrm))
    (compO l E W hrm hmn) (coefficientSequenceTransition l E W hrm)
    (coefficientSequenceTransition l E W hmn) (coefficientSequenceTransition l E W (hmn.trans hrm))
    (fun M ↦ transition_comp l E W M hrm hmn) N

private theorem derivedRestrictedTransition (N : coefficientSequenceDerived l E W)
    {m n : ℕ} (h : n ≤ m) :
    (normalizedDVRTowerTransition l E W D hl h).app
        ((coefficientSequenceDerivedRestriction l E W).obj N) ≫
        (coefficientRestrictedEvaluationIso l E W n).hom.app N =
      (coefficientRestrictedEvaluationIso l E W m).hom.app N ≫
        (normalizedDVRResCompleted l E W D hl m).map
          ((coefficientSequenceDerivedTransition l E W h).app N) ≫
        (normalizedDVRResCompletedComp l E W D hl h).hom.app
          ((coefficientSequenceDerivedEvaluation l E W n).obj N) := by
  rw [towerTransition_eq, restrictedEvaluation_eq, restrictedEvaluation_eq,
    derivedTransition_eq, completedResComp_eq]
  exact CategoryTheory.derivedSquare
    (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op m))
    (coefficientSequenceEvaluation l E W m) (scalarReductionRestriction l E W m)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (coefficientSequenceEvaluation l E W n) (normalizedDVRModuleRes l E W h)
    (scalarReductionRestriction l E W n)
    (eqToIso (coefficientSequenceRestriction_evaluation l E W m))
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n))
    (completedCompO l E W D hl h)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).map (homOfLE h).op)
    (coefficientSequenceTransition l E W h) (fun M ↦ restrictedTransition l E W D hl M h) N

end WeilConjectures
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace WeilConjectures

/-- A normalized coefficient sequence has a normalized DVR tower model whose Roos
projections are the specified total-limit projections, after exact scalar restriction.
This assertion constructs a model and identifies maps; it asserts no finite effectivity.

Source: Stacks Project, Tags 0940 and 0941, and the coherent-tower interpretation in
Bhatt--Scholze, Lemmas 3.5.4--3.5.7.
(blueprint: lem-coef-sequence-roos-model).

Proof: take the exact restriction of the sequence to completed-coefficient towers.
The finite objects are its actual derived evaluations, and their transition maps are
those obtained by localizing the section restrictions. The identity and composition
laws hold already on sections, hence after localization. The exact restriction and
finite-evaluation comparison identify the restricted transitions with these maps.
The given normalization condition is exactly the normalization field of the resulting
DVR tower. Resolve the restricted tower by a simultaneous K-injective complex.
Evaluation preserves K-injectives; its termwise product represents the derived product.
The ordinary limit cone gives the canonical Roos triangle. Transport this triangle
through the total-derived-limit and evaluation identifications. The characterization
of the total-limit projections on K-injective towers identifies every transported
projection with coefficientSequenceProjection. Thus the first map is the displayed
product lift, with no choice of a new counit or unrelated projection. -/
theorem coefficientSequence_roosModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    ∃ (T : NormalizedDVRTower l E W D hl)
      (e : ∀ n : ℕ, T.M n ≅ (coefficientSequenceDerivedEvaluation l E W n).obj N)
      (hp : HasProduct (fun n : ℕ ↦
        (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower)), letI := hp
      ∃ δ, IsDerivedLimitTriangle
        (fun n : ℕ ↦ (normalizedDVRTowerTransition l E W D hl n.le_succ).app T.tower)
        ((coefficientSequenceLimit l E W).obj N)
        (Pi.lift (fun n : ℕ ↦ (coefficientSequenceProjection l E W n).app N ≫
          (normalizedDVRResCompleted l E W D hl n).map (e n).inv ≫
          (T.evaluationIso n).inv)) δ := by
  let T : NormalizedDVRTower l E W D hl := {
    M := fun n ↦ (coefficientSequenceDerivedEvaluation l E W n).obj N
    tau := fun h ↦ (coefficientSequenceDerivedTransition l E W h).app N
    tau_refl := derivedTransition_id l E W N
    tau_comp := fun h₁ h₂ ↦ derivedTransition_comp l E W N h₁ h₂
    tower := (coefficientSequenceDerivedRestriction l E W).obj N
    evaluationIso := fun n ↦ (coefficientRestrictedEvaluationIso l E W n).app N
    tower_tau := fun h ↦ derivedRestrictedTransition l E W D hl N h
    normalization := hN }
  obtain ⟨hp, δ, hδ⟩ := coefficientConstantTower_roos l E W D hl T.tower
  have hpDVR : HasProduct (fun n : ℕ ↦
      (normalizedDVRTowerEvaluation l E W D hl n).obj T.tower) := hp
  let := hpDVR
  refine ⟨T, (fun n ↦ Iso.refl _), hpDVR, δ, ?_⟩
  have he : (Pi.lift (fun n : ℕ ↦ (coefficientSequenceProjection l E W n).app N ≫
        (normalizedDVRResCompleted l E W D hl n).map (Iso.refl _).inv ≫
        (T.evaluationIso n).inv)) =
      Pi.lift (fun n : ℕ ↦ (coefficientConstantTowerProjection l E W n).app T.tower) := by
    apply Pi.hom_ext
    intro n
    simp only [Pi.lift_comp_π]
    erw [Pi.lift_comp_π]
    change (coefficientSequenceProjection l E W n).app N ≫ _ ≫ _ = _
    unfold coefficientSequenceProjection
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.refl_inv]
    rw [CategoryTheory.Functor.map_id]
    change ((coefficientConstantTowerProjection l E W n).app
      ((coefficientSequenceDerivedRestriction l E W).obj N) ≫
        (coefficientRestrictedEvaluationIso l E W n).hom.app N) ≫
      𝟙 _ ≫ (coefficientRestrictedEvaluationIso l E W n).inv.app N = _
    simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [he]
  exact hδ

end WeilConjectures

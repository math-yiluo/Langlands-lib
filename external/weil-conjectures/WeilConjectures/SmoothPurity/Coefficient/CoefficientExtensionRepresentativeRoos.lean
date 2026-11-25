/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoosComparisonSupplement
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRestrictedTower
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMateIsIso

/-! # Roos comparison of strict coefficient-extension representatives

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf HasDerivedCategory.standard
  SemilinearSections.hasDerived coefficientExtensionSystem

variable (A : CoefficientExtensionSystems l E L ι W)

private theorem cofiberMap_eq_coneMap
    {B : Type*} [Category B] [Abelian B]
    {K L K' L' : CochainComplex B ℤ} (s : K ⟶ L) (s' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : s ≫ b = a ≫ s') :
    HomologicalComplex.homotopyCofiber.mapArrowHom s s'
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      CochainComplex.mappingCone.map s s' a b h := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X s (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain,
    CochainComplex.HomComplex.Cochain.comp_v, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd,
    CochainComplex.mappingCone.inr]

private theorem roosFunctor_eq_integral
    {B : Type*} [Category B] [Abelian B] [HasCountableProducts B] :
    (roosF : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex B ℤ) =
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor := by
  refine CategoryTheory.Functor.ext (F := roosF)
    (G := HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor) (fun X ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [roosF, roosConeFunctor, Functor.comp_map, integralOperationsRoosFunctor,
    integralOperationsRoosMap]
  rw [cofiberMap_eq_coneMap]
  rfl

private def complexify {B : Type*} [Category B] [HasZeroMorphisms B]
    (T : ℕᵒᵖ ⥤ CochainComplex B ℤ) : CochainComplex (ℕᵒᵖ ⥤ B) ℤ where
  X i := T ⋙ HomologicalComplex.eval B (.up ℤ) i
  d i j := Functor.whiskerLeft T (HomologicalComplex.dNatTrans B (.up ℤ) i j)
  shape i j h := by ext n; exact (T.obj n).shape i j h
  d_comp_d' i j k hij hjk := by ext n; exact (T.obj n).d_comp_d i j k

private def complexifyMap {B : Type*} [Category B] [HasZeroMorphisms B]
    {T T' : ℕᵒᵖ ⥤ CochainComplex B ℤ} (α : T ⟶ T') :
    complexify T ⟶ complexify T' where
  f i := Functor.whiskerRight α (HomologicalComplex.eval B (.up ℤ) i)
  comm' i j h := by ext n; exact (α.app n).comm i j

private theorem towerRoos_naturality
    {B : Type*} [Category B] [Abelian B] [HasCountableProducts B]
    {T T' : ℕᵒᵖ ⥤ CochainComplex B ℤ} (α : T ⟶ T') (n : ℕ) :
    integralOperationsRoosFunctor.map α ≫
        (CochainComplex.mappingCocone.fst _ ≫ Pi.π (fun k ↦ T'.obj (op k)) n) =
      (CochainComplex.mappingCocone.fst _ ≫ Pi.π (fun k ↦ T.obj (op k)) n) ≫
        α.app (op n) := by
  have h := roosEval_natural (complexifyMap α) n
  have hm : roosF.map (complexifyMap α) = integralOperationsRoosFunctor.map α := by
    dsimp only [roosF, roosConeFunctor, Functor.comp_map, integralOperationsRoosFunctor,
      integralOperationsRoosMap]
    rw [cofiberMap_eq_coneMap]
    rfl
  rw [hm] at h
  exact h

private def towerRoosComparison
    {S B D : Type*} [Category S] [Category B] [Category D]
    [Abelian B] [HasCountableProducts B]
    (Q : CochainComplex B ℤ ⥤ D)
    (H : S ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (T : S ⥤ (ℕᵒᵖ ⥤ CochainComplex B ℤ))
    (τ : H ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ T) :
    H ⋙ roosF ⋙ Q ≅ T ⋙ integralOperationsRoosFunctor ⋙ Q :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft H (eqToIso roosFunctor_eq_integral)) Q ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight τ integralOperationsRoosFunctor) Q

private theorem roos_iso_projection
    {S B D : Type*} [Category S] [Category B] [Category D]
    [Abelian B] [HasCountableProducts B]
    (Q : CochainComplex B ℤ ⥤ D)
    (H : S ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (T : S ⥤ (ℕᵒᵖ ⥤ CochainComplex B ℤ))
    (τ : H ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ T)
    (P : S) (n : ℕ) :
    (towerRoosComparison Q H T τ).hom.app P ≫
        Q.map (CochainComplex.mappingCocone.fst _ ≫
          Pi.π (fun k ↦ (T.obj P).obj (op k)) n) =
      Q.map (roosEval (H.obj P) n) ≫ Q.map ((τ.hom.app P).app (op n)) := by
  dsimp only [towerRoosComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_refl]
  erw [Q.map_id, Category.id_comp]
  simp only [← Q.map_comp]
  apply congrArg Q.map
  exact towerRoos_naturality (τ.hom.app P) n

attribute [local irreducible] towerRoosComparison

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derivedEvaluationFactors
    {C B D T : Type*} [Category C] [Category B] [Category D] [Category T]
    [Abelian C] [Abelian B] [Abelian D] [Abelian T]
    [HasDerivedCategory C] [HasDerivedCategory B] [HasDerivedCategory D]
    [HasDerivedCategory T]
    (U : C ⥤ B) (V : B ⥤ T) (F : C ⥤ D) (R : D ⥤ T)
    [U.Additive] [V.Additive] [F.Additive] [R.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : U ⋙ V ≅ F ⋙ R) (X : CochainComplex C ℤ) :
    V.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app X) ≫
        V.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ V)) (.up ℤ) ≪≫
            NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).symm).hom.app X) =
      (Functor.mapDerivedCategoryCompIso U V ≪≫
          Functor.mapDerivedCategoryNatIso a ≪≫
          (Functor.mapDerivedCategoryCompIso F R).symm).hom.app (DerivedCategory.Q.obj X) ≫
        R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) := by
  have h := Functor.mapDerivedCategoryNatIso_fac a X
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  erw [Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U V).inv.app
    (DerivedCategory.Q.obj X))).1
  erw [Iso.inv_hom_id_app_assoc]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  have hi : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).inv.app X =
      𝟙 _ := by
    apply (cancel_epi
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).hom.app X)).1
    erw [Iso.hom_inv_id_app]
  erw [Functor.mapHomologicalComplexCompIso_refl_hom_app, Category.id_comp, hi,
    Category.comp_id]
  exact h.symm

private theorem restrictedEvaluation_factors
    (X : CochainComplex (coefficientSequenceModules l L W) ℤ) (n : ℕ) :
    (coefficientConstantTowerEvaluation l L W n).map
          ((coefficientSequenceRestriction l L W).mapDerivedCategoryFactors.hom.app X) ≫
        (coefficientConstantTowerEvaluationFactors l L W n).hom.app
          (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj X) ≫
        DerivedCategory.Q.map
          ((coefficientRestrictedComplexEvaluation l L W n).hom.app X) =
      (coefficientRestrictedEvaluationIso l L W n).hom.app (DerivedCategory.Q.obj X) ≫
        (coefficientFiniteDerivedRestriction l L W n).map
          ((coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app X) ≫
        (scalarReductionRestriction l L W n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj X) := by
  simp only [coefficientRestrictedEvaluationIso,
    coefficientRestrictedComplexEvaluation, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapHomologicalComplexCompIso_refl_hom_app, Category.id_comp]
  exact (Functor.mapDerivedCategorySquareIso_hom_app_Q_obj
      (eqToIso (coefficientSequenceRestriction_evaluation l L W n)) X).symm

private theorem projection_naturality
    {S T V U : Type*} [Category S] [Category T] [Category V] [Category U]
    (F : S ⥤ T) (G : S ⥤ V) (R : V ⥤ T) (Q : U ⥤ V) (H : U ⥤ T)
    (π : F ⟶ G ⋙ R) (b : Q ⋙ R ⟶ H)
    {M X : S} (f : M ⟶ X) {Z Z' : U} (a : G.obj X ⟶ Q.obj Z) (g : Z ⟶ Z')
    {Y : T} (p : F.obj X ⟶ Y) (q : Y ⟶ R.obj (G.obj X))
    (hp : π.app X = p ≫ q) :
    F.map f ≫ p ≫ q ≫ R.map a ≫ b.app Z ≫ H.map g =
      π.app M ≫ R.map (G.map f ≫ a ≫ Q.map g) ≫ b.app Z' := by
  have hn := π.naturality f
  dsimp only [Functor.comp_map] at hn
  have h : F.map f ≫ π.app X ≫ R.map a ≫ b.app Z ≫ H.map g =
      π.app M ≫ R.map (G.map f ≫ a ≫ Q.map g) ≫ b.app Z' := by
    rw [reassoc_of% hn]
    have hg := b.naturality g
    dsimp only [Functor.comp_map] at hg
    rw [← hg]
    simp only [Functor.map_comp, Category.assoc]
  rw [hp] at h
  simpa only [Category.assoc] using h

private def scalarRoosComparison :
    integralScalarTowerFunctor l E L ι W ⋙ integralOperationsRoosFunctor ⋙ DerivedCategory.Q ≅
      integralScalarComplexFunctor l E L ι W ⋙ DerivedCategory.Q :=
  Iso.refl _

private theorem scalarRoosComparison_projection
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (scalarRoosComparison l E L ι W).hom.app P ≫
        DerivedCategory.Q.map (coefficientExtensionRoosProjection l E L ι W P n) =
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _ ≫
        Pi.π (fun k ↦ ((integralScalarTowerFunctor l E L ι W).obj P).obj (op k)) n) := by
  dsimp only [scalarRoosComparison, Iso.refl_hom, NatTrans.id_app]
  rw [Category.id_comp]
  unfold coefficientExtensionRoosProjection
  rfl

attribute [local irreducible] scalarRoosComparison integralScalarComplexFunctor

attribute [local irreducible] coefficientSequenceProjection
  coefficientRestrictedEvaluationIso coefficientConstantTowerProjection
  coefficientConstantTowerLimit coefficientSequenceRestriction

/-- The strict quotient representative has the specified Roos completion on good complexes.
Source: integral operations; Stacks 0940, 0941 and 0H9L
(blueprint: stage3-pur-extension-representative-roos).
Proof: apply exact restriction to the strict system representative. Its evaluated
complexes identify with the published finite scalar complexes. The prescribed
transition equation makes these comparisons an isomorphism of strict completed
coefficient towers, natural in each good complex. Compute the total inverse limit
by resolving this strict tower with injective towers. Countable products of the
completed-coefficient module sheaves are exact, so the product resolution is a
quasi-isomorphism. Apply the diagonal maps to the shifted mapping cones of 1 minus
shift. This gives a natural isomorphism from the completed representative to the
fixed Roos complex. Its maps to the nth term are the actual product projections,
since every comparison comes from a strict tower map. Compose with the given
representative comparison. This gives the displayed isomorphism and its equation;
no uniqueness of arbitrary distinguished-triangle fillers is used. -/
theorem coefficientExtensionRepresentativeRoos_exists
    (SE : CoefficientDerivedSystemCalculus l E W)
    (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ)
    (directEvaluation : ∀ n : ℕ,
      direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
    (htransition : IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation)
    (model : integralOperationsGoodLocalization l E W ⋙
      coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q) :
    ∃ e : integralOperationsGoodLocalization l E W ⋙
        (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W) ≅
          integralScalarOnGood l E L ι W,
      ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
        e.inv.app P ≫
            (coefficientSequenceProjection l L W n).app
              ((coefficientExtensionSystem l E L ι W SE A).obj
                (DerivedCategory.Q.obj P.obj)) ≫
            (coefficientFiniteDerivedRestriction l L W n).map
              ((coefficientSequenceDerivedEvaluation l L W n).map (model.hom.app P) ≫
                (coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
                  (direct.obj P) ≫ DerivedCategory.Q.map ((directEvaluation n).hom.app P)) ≫
            (scalarReductionRestriction l L W n).mapDerivedCategoryFactors.hom.app
              ((integralScalarFiniteComplex l E L ι W n).obj P.obj) =
          DerivedCategory.Q.map (coefficientExtensionRoosProjection l E L ι W P.obj n) := by
  classical
  obtain ⟨τ, hτ⟩ := coefficientExtensionRestrictedTower_exists l E L ι W
    direct directEvaluation htransition
  obtain ⟨β, hβ⟩ := coefficientConstantTowerRoosComparison l L W
  let U := coefficientSequenceRestriction l L W
  let H := direct ⋙ U.mapHomologicalComplex (.up ℤ)
  let μ : integralOperationsGoodLocalization l E W ⋙
      (coefficientExtensionSystem l E L ι W SE A ⋙ coefficientSequenceLimit l L W) ≅
        H ⋙ DerivedCategory.Q ⋙ coefficientConstantTowerLimit l L W :=
    Functor.isoWhiskerRight model (coefficientSequenceLimit l L W) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft direct U.mapDerivedCategoryFactors)
          (coefficientConstantTowerLimit l L W)
  let γ₀ := towerRoosComparison DerivedCategory.Q H
    ((integralOperationsGoodComplex l E W).ι ⋙ integralScalarTowerFunctor l E L ι W) τ
  let γ := γ₀ ≪≫ Functor.isoWhiskerLeft
    (integralOperationsGoodComplex l E W).ι (scalarRoosComparison l E L ι W)
  let e := μ ≪≫ Functor.isoWhiskerLeft H β ≪≫ γ
  refine ⟨e, ?_⟩
  intro P n
  have hγ : γ.hom.app P ≫
      DerivedCategory.Q.map (coefficientExtensionRoosProjection l E L ι W P.obj n) =
      DerivedCategory.Q.map (roosEval (H.obj P) n) ≫
        DerivedCategory.Q.map
          ((coefficientRestrictedComplexEvaluation l L W n).hom.app (direct.obj P)) ≫
        DerivedCategory.Q.map
          (((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ)).map
            ((directEvaluation n).hom.app P)) := by
    dsimp only [γ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.comp_obj, ObjectProperty.ι_obj]
    rw [Category.assoc, scalarRoosComparison_projection]
    have h := roos_iso_projection DerivedCategory.Q H
      ((integralOperationsGoodComplex l E W).ι ⋙ integralScalarTowerFunctor l E L ι W)
      τ P n
    rw [hτ P n] at h
    simpa only [γ₀, Functor.comp_obj, ObjectProperty.ι_obj, DerivedCategory.Q.map_comp,
      Category.assoc] using h
  have hβ' : β.hom.app (H.obj P) ≫ DerivedCategory.Q.map (roosEval (H.obj P) n) =
      (coefficientConstantTowerProjection l L W n).app (DerivedCategory.Q.obj (H.obj P)) ≫
        (coefficientConstantTowerEvaluationFactors l L W n).hom.app (H.obj P) := by
    rw [← hβ (H.obj P) n]
    simp only [Iso.hom_inv_id_app_assoc]
  apply (cancel_epi (e.hom.app P)).1
  simp only [Iso.hom_inv_id_app_assoc]
  dsimp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [hγ]
  erw [reassoc_of% hβ']
  dsimp only [μ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  erw [reassoc_of% (coefficientConstantTowerProjection l L W n).naturality
    (U.mapDerivedCategoryFactors.hom.app (direct.obj P))]
  have hf := restrictedEvaluation_factors l L W (direct.obj P) n
  erw [reassoc_of% hf]
  have hn := projection_naturality
    (coefficientSequenceLimit l L W) (coefficientSequenceDerivedEvaluation l L W n)
    (coefficientFiniteDerivedRestriction l L W n) DerivedCategory.Q
    ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (coefficientSequenceProjection l L W n)
    (scalarReductionRestriction l L W n).mapDerivedCategoryFactors.hom
    (M := (coefficientExtensionSystem l E L ι W SE A).obj
      (DerivedCategory.Q.obj P.obj)) (X := DerivedCategory.Q.obj (direct.obj P))
    (Z := ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj
      (direct.obj P)) (Z' := (integralScalarFiniteComplex l E L ι W n).obj P.obj)
    (model.hom.app P)
    ((coefficientSequenceEvaluation l L W n).mapDerivedCategoryFactors.hom.app
      (direct.obj P)) ((directEvaluation n).hom.app P)
    ((coefficientConstantTowerProjection l L W n).app
      (U.mapDerivedCategory.obj (DerivedCategory.Q.obj (direct.obj P))))
    ((coefficientRestrictedEvaluationIso l L W n).hom.app
      (DerivedCategory.Q.obj (direct.obj P))) (by
        unfold coefficientSequenceProjection
        rfl)
  exact hn.symm

end WeilConjectures

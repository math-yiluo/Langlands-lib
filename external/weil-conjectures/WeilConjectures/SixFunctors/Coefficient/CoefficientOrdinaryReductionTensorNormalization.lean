/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Strict presentations of reduction through the ordinary quotient system

Source: Stacks 06YY, 07A4, 07A6 and 0941.

A strict reduction presentation `e : reduction (Q P) ≅ Q C` whose adjunct is the
localization of a strict map `z : P ⟶ lim C` is the localization of the ordinary
transpose `g : quotient P ⟶ C` of `z`, composed with the universal comparison `ε`.
The finite evaluations of `g` are the normalized evaluation isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- A map out of the ordinary quotient system whose transpose has the finite scalar
units as projections evaluates to the normalized evaluation isomorphism.
Source: Stacks 03D7, 0941. -/
theorem evaluation_map_of_transpose (M : OrdinaryModel l E W)
    {X : scalarReductionSource l E W} {Y : coefficientSequenceModules l E W}
    (g : M.tensor.obj X ⟶ Y) (n : ℕ)
    (k : (coefficientSequenceEvaluation l E W n).obj Y ⟶ (scalarReductionExtension l E W n).obj X)
    (hg : M.adjunction.unit.app X ≫ (ordinaryLimit l E W).map g ≫
        limit.π ((coefficientSequenceRestriction l E W).obj Y) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app Y ≫
        (scalarReductionRestriction l E W n).map k =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app X)
    (h0 : M.adjunction.unit.app X ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (M.tensor.obj X) ≫
        (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app X) =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app X) :
    (coefficientSequenceEvaluation l E W n).map g ≫ k = (M.evaluation n).hom.app X := by
  let a := (scalarReductionExtension_adjunction l E W n).choose
  let ρ := eqToIso (coefficientSequenceRestriction_evaluation l E W n)
  have hnat : limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
      ρ.hom.app (M.tensor.obj X) ≫ (scalarReductionRestriction l E W n).map
        ((coefficientSequenceEvaluation l E W n).map g) =
      (ordinaryLimit l E W).map g ≫ limit.π ((coefficientSequenceRestriction l E W).obj Y) (op n) ≫
        ρ.hom.app Y := by
    have h1 := ρ.hom.naturality g
    dsimp only [Functor.comp_map] at h1
    erw [← h1, Functor.comp_map, lim_map, limMap_π_assoc]
    rfl
  have key : M.adjunction.unit.app X ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
      ρ.hom.app (M.tensor.obj X) ≫ (scalarReductionRestriction l E W n).map
        ((coefficientSequenceEvaluation l E W n).map g ≫ k) = a.unit.app X := by
    rw [← hg, Functor.map_comp, reassoc_of% hnat]
    rfl
  rw [← cancel_epi ((M.evaluation n).inv.app X), Iso.inv_hom_id_app]
  apply (a.homEquiv X _).injective
  rw [a.homEquiv_unit, a.homEquiv_unit]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  conv_lhs => rw [← h0]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc]
  exact key

/-- The ordinary adjunction unit followed by a finite projection is the finite scalar unit.
Source: Stacks 03D7, 0941. -/
theorem OrdinaryModel.unit_projection (M : OrdinaryModel l E W)
    (X : scalarReductionSource l E W) (n : ℕ) :
    M.adjunction.unit.app X ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj X)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (M.tensor.obj X) ≫
        (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app X) =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app X := by
  have hu := (scalarReductionExtension_adjunction l E W n).choose_spec X
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  exact (M.unit_tensor X n V x).trans (by
    dsimp only [unrestrictedIntegralTensorSection, unrestrictedIntegralReductionFunctor,
      unrestrictedIntegralReductionExistence, scalarReductionExistence] at hu ⊢
    exact (hu V x).symm)

/-- The ordinary transpose of a strict unit presentation evaluates, at every finite level,
to the normalized evaluation isomorphism of the quotient system.
Source: Stacks 03D7, 06YY, 0941. -/
theorem evaluation_mapHomologicalComplex_transpose (M : OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (z : P ⟶ ((ordinaryLimit l E W).mapHomologicalComplex (.up ℤ)).obj C) (n : ℕ)
    (k : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ⟶
      ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (hz : z ≫ (NatTrans.mapHomologicalComplex
        (Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)))
          (.up ℤ)).app C ≫
        (NatIso.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)).hom.app C ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map k =
      ((scalarReductionExtension_adjunction l E W n).choose.mapHomologicalComplex
        (.up ℤ)).unit.app P) :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        (((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C).symm z) ≫ k =
      (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P := by
  obtain ⟨g, rfl⟩ : ∃ g, z = (M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C g :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  rw [Equiv.symm_apply_apply]
  apply HomologicalComplex.hom_ext
  intro p
  have hp := congrArg (fun f ↦ f.f p) hz
  simp only [HomologicalComplex.comp_f] at hp
  rw [HomologicalComplex.comp_f]
  have hg : M.adjunction.unit.app (P.X p) ≫ (ordinaryLimit l E W).map (g.f p) ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (C.X p)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app (C.X p) ≫
      (scalarReductionRestriction l E W n).map (k.f p) =
      (scalarReductionExtension_adjunction l E W n).choose.unit.app (P.X p) := by
    exact hp
  exact evaluation_map_of_transpose l E W M (g.f p) n (k.f p) hg
    (M.unit_projection l E W (P.X p) n)

/-- The structural limit comparison of the ordinary model is the canonical composite
comparison. Source: Stacks 0941. -/
theorem OrdinaryModel.limitComparison_termwise (M : OrdinaryModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    M.limitComparison.hom.app C ≫ (termwiseLimitComparison l E W).inv.app ((tower l E W).obj C) =
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (coefficientSequenceRestriction l E W ⋙
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
        (.up ℤ)).inv.app C := by
  rw [← cancel_mono ((termwiseLimitComparison l E W).hom.app ((tower l E W).obj C)),
    Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  apply limit.hom_ext
  intro n
  apply HomologicalComplex.hom_ext
  intro p
  refine (M.limitComparison_projection C n.unop p).trans ?_
  rw [Category.assoc, HomologicalComplex.comp_f]
  erw [termwiseLimitComparison_projection l E W ((tower l E W).obj C) n.unop p]
  exact (Category.id_comp _).symm

/-- The system limit unit is the canonical right-derived unit of inverse limit after
exact restriction, as displayed in strict reduction presentations.
Source: Stacks 0941, 07A6. -/
theorem OrdinaryModel.systemLimitUnit_app (M : OrdinaryModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (systemLimitUnit l E W M (constantLimitUnit l E W)).app C =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (coefficientSequenceRestriction l E W ⋙
              (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
            (.up ℤ)).inv.app C) ≫
        (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app
          (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
              scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W
          ).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ scalarReductionSource l E W)).hom.app
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C) := by
  rw [← M.limitComparison_termwise l E W C, Functor.map_comp, Category.assoc]
  have hqA : (DerivedCategory.quotientCompQhIso
      (ℕᵒᵖ ⥤ scalarReductionSource l E W)).hom.app ((tower l E W).obj C) = 𝟙 _ := rfl
  have hqiB (K : CochainComplex (scalarReductionSource l E W) ℤ) :
      (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app K = 𝟙 _ := rfl
  have hf : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((tower l E W).obj C) = 𝟙 _ := rfl
  dsimp only [systemLimitUnit, constantLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom]
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  erw [hqA, hqiB, hf]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp, Category.id_comp]

/-- A strict unit presentation of a left adjoint of the total limit is the universal
comparison followed by the localized ordinary transpose of its unit map, whose finite
evaluations are the normalized evaluation isomorphisms.
Source: Stacks 03D7, 06YY, 07A6, 0941. -/
theorem exists_transpose_of_unitPresentation (M : OrdinaryModel l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hhom : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (f : (M.quotient l E W).obj Q ⟶ I),
      adj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          (systemLimitUnit l E W M (constantLimitUnit l E W)).app I)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : L.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (h : CoefficientStrictReductionUnitPresentation l E W L adj P C e κ) :
    ∃ g : (M.quotient l E W).obj P ⟶ C,
      e.hom = ε.app P ≫ DerivedCategory.Q.map g ∧
      ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map g ≫
          (κ n).hom = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P := by
  unfold CoefficientStrictReductionUnitPresentation at h
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C).symm z, ?_, fun n ↦
    evaluation_mapHomologicalComplex_transpose l E W M P C z n (κ n).hom (h2 n)⟩
  apply (adj.homEquiv _ _).injective
  have hunit :
      (systemLimitUnit l E W M (constantLimitUnit l E W)).app C =
        DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (Iso.refl (coefficientSequenceRestriction l E W ⋙
                (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)))
              (.up ℤ)).inv.app C) ≫
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W
            ).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj
                (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) ≫
          (coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C) := by
    rw [← M.limitComparison_termwise l E W C, Functor.map_comp, Category.assoc]
    have hqA : (DerivedCategory.quotientCompQhIso
        (ℕᵒᵖ ⥤ scalarReductionSource l E W)).hom.app ((tower l E W).obj C) = 𝟙 _ := rfl
    have hqiB (K : CochainComplex (scalarReductionSource l E W) ℤ) :
        (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app K = 𝟙 _ := rfl
    have hf : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomotopyCategoryFactors (.up ℤ)).inv.app
          ((tower l E W).obj C) = 𝟙 _ := rfl
    dsimp only [systemLimitUnit, constantLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.trans_hom, Iso.symm_hom]
    simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.assoc]
    erw [hqA, hqiB, hf]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.id_comp, Category.id_comp]
  rw [h1, hhom, Equiv.apply_symm_apply, hunit]
  rfl

end WeilConjectures.OrdinaryQuotient

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Chain maps of strict coefficient systems agree once all their finite evaluations agree.
Source: Stacks 0941. -/
theorem coefficientSequenceComplex_hom_ext
    {X Y : CochainComplex (coefficientSequenceModules l E W) ℤ} {f g : X ⟶ Y}
    (h : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map f =
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map g) :
    f = g := by
  apply HomologicalComplex.hom_ext
  intro p
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrArg (fun φ ↦ ((φ.f p).val.app (op U.unop.2)) x) (h U.unop.1)

private theorem eqToHom_surjective {A B : AddCommGrpCat.{w}} (h : A = B) :
    Function.Surjective (eqToHom h) := by
  subst B
  exact fun x ↦ ⟨x, rfl⟩

/-- Every evaluated section is the transport of a section of the system.
Source: Stacks 0941. -/
theorem coefficientEvaluationSection_surjective
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective (coefficientEvaluationSection l E W M n U) :=
  eqToHom_surjective (coefficientSequenceEvaluationAb_eq l E W M n U).symm

/-- Evaluation of a map acts on transported sections by the map at that level.
Source: Stacks 0941. -/
theorem coefficientEvaluationSection_map
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceEvaluation l E W n).map f).val.app U)
      (coefficientEvaluationSection l E W M n U x) =
    coefficientEvaluationSection l E W N n U (f.val.app (op (n, U.unop)) x) := rfl

private theorem cochainIso_inv_section
    {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {P Q : CochainComplex (SheafOfModules.{w} R) ℤ} (e : P ≅ Q) (k : ℤ) (U : Cᵒᵖ)
    (x : (P.X k).val.obj U) (y : (Q.X k).val.obj U)
    (h : (e.hom.f k).val.app U x = y) : (e.inv.f k).val.app U y = x :=
  (congrArg (fun z ↦ (e.inv.f k).val.app U z) h).symm.trans
    (congrArg (fun z : P ⟶ P ↦ (z.f k).val.app U x) e.hom_inv_id)

/-- The generator formula of the evaluation tensor comparison.
Source: Stacks 03EK, 0941. -/
theorem coefficientEvaluationTensorIso_hom_generator (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop)))
    (y : (Q.X q).val.obj (op (n, U.unop))) :
    ((coefficientEvaluationTensorIso l E W n P Q).hom.f k).val.app U
      (coefficientEvaluationSection l E W _ n U
        (coefficientTensorGenerator.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q k h (op (n, U.unop)) x y)) =
    coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
      p q k h U
        (coefficientEvaluationSection l E W (P.X p) n U x)
        (coefficientEvaluationSection l E W (Q.X q) n U y) :=
  (coefficientEvaluationTensorIso_exists l E W n P Q).choose_spec.1 p q k h U x y

/-- The inverse evaluation tensor comparison on generators.
Source: Stacks 03EK, 0941. -/
theorem coefficientEvaluationTensorIso_inv_generator (n : ℕ)
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop)))
    (y : (Q.X q).val.obj (op (n, U.unop))) :
    ((coefficientEvaluationTensorIso l E W n P Q).inv.f k).val.app U
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P)
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
        p q k h U
          (coefficientEvaluationSection l E W (P.X p) n U x)
          (coefficientEvaluationSection l E W (Q.X q) n U y)) =
    coefficientEvaluationSection l E W _ n U
        (coefficientTensorGenerator.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q k h (op (n, U.unop)) x y) :=
  cochainIso_inv_section _ k U _ _
    (coefficientEvaluationTensorIso_hom_generator l E W n P Q p q k h U x y)


attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

attribute [local irreducible] coefficientEvaluationTensorIso
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology SheafOfModules.monoidalCategory in
/-- The prescribed evaluation tensor isomorphisms are natural in both complexes.
Source: Stacks 07A4, 03EK. -/
theorem coefficientEvaluationTensorIso_naturality (n : ℕ)
    {P P' Q Q' : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        ((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b)) ≫
        (coefficientEvaluationTensorIso l E W n P' Q').hom =
      (coefficientEvaluationTensorIso l E W n P Q).hom ≫
        (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
          (Prod.mkHom
            (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a)
            (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map b)) := by
  let e := coefficientEvaluationTensorIso l E W n P Q
  let e' := coefficientEvaluationTensorIso l E W n P' Q'
  apply e.inv_comp_eq.mp
  apply HomologicalComplex.hom_ext
  intro k
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{t + 1, t, u}
    (J := Scheme.ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W n)
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Q) k _
  intro p q hpq U
  -- Lift sections without substituting through the tensor constructions.
  refine (coefficientEvaluationSection_surjective l E W (P.X p) n U).forall.2 ?_
  intro x0
  refine (coefficientEvaluationSection_surjective l E W (Q.X q) n U).forall.2 ?_
  intro y0
  have hi := coefficientEvaluationTensorIso_inv_generator l E W n P Q p q k hpq U x0 y0
  change (e'.hom.f k).val.app U
      (((coefficientSequenceEvaluation l E W n).map
        (((coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b)).f k)).val.app U
        ((e.inv.f k).val.app U _)) = _
  let t := (coefficientTotalTensor.{u, t + 1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom a b)
  have hs := CategoryTheory.ScalarHomTensor.tensor_generator_map.{t + 1, t, u}
    a b p q k hpq (op (n, U.unop)) x0 y0
  have hm := coefficientEvaluationSection_map l E W (t.f k) n U
    (coefficientTensorGenerator.{u, t + 1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) P Q p q k hpq (op (n, U.unop)) x0 y0)
  have ht := CategoryTheory.ScalarHomTensor.tensor_generator_map.{t + 1, t, u}
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a)
    (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map b)
    p q k hpq U
    (coefficientEvaluationSection l E W (P.X p) n U x0)
    (coefficientEvaluationSection l E W (Q.X q) n U y0)
  have ha := coefficientEvaluationSection_map l E W (a.f p) n U x0
  have hb := coefficientEvaluationSection_map l E W (b.f q) n U y0
  -- Compose the generator formulas without rewriting the surrounding large types.
  exact (congrArg (fun z ↦ (e'.hom.f k).val.app U
      (((coefficientSequenceEvaluation l E W n).map (t.f k)).val.app U z)) hi).trans
    ((congrArg (fun z ↦ (e'.hom.f k).val.app U z)
      (hm.trans (congrArg (coefficientEvaluationSection l E W _ n U) hs))).trans
      ((coefficientEvaluationTensorIso_hom_generator l E W n P' Q' p q k hpq U
        ((a.f p).val.app (op (n, U.unop)) x0)
        ((b.f q).val.app (op (n, U.unop)) y0)).trans
        ((congrArg₂ (fun x y ↦ coefficientTensorGenerator.{u, t + 1, t}
          (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj P')
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Q')
          p q k hpq U x y) ha hb).symm.trans ht.symm)))

/-- Composition of product morphisms under a bifunctor.
Source: Stacks 0011. -/
theorem bifunctor_map_mkHom_comp {A B : Type*} [Category* A] [Category* B] (T : A × A ⥤ B)
    {X X' X'' Y Y' Y'' : A} (a : X ⟶ X') (a' : X' ⟶ X'') (c : Y ⟶ Y') (c' : Y' ⟶ Y'') :
    T.map (Prod.mkHom a c) ≫ T.map (Prod.mkHom a' c') = T.map (Prod.mkHom (a ≫ a') (c ≫ c')) := by
  rw [← T.map_comp]
  rfl

namespace OrdinaryQuotient

/-- The ordinary tensor comparison of the quotient system evaluates at every finite level
to the normalized scalar tensor comparison.
Source: Stacks 03EK, 07A4, 0941. -/
def OrdinaryModel.TensorEvaluation (M : OrdinaryModel l E W)
    (b : coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)) : Prop :=
  ∀ (n : ℕ) (P Q : CochainComplex (scalarReductionSource l E W) ℤ),
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map (b.hom.app (P, Q)) ≫
      (coefficientEvaluationTensorIso l E W n ((M.quotient l E W).obj P)
        ((M.quotient l E W).obj Q)).hom ≫
      (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P)
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q)) =
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
      (coefficientScalarTensorIso l E W n P Q).hom

/-- Strict comparison of tensor presentations: maps out of the quotient system whose finite
evaluations are the normalized evaluation isomorphisms intertwine the ordinary tensor
comparison with any strict tensor map having the scalar tensor evaluations.
Source: Stacks 07A4, 0941. -/
theorem OrdinaryModel.tensor_comp_map_eq (M : OrdinaryModel l E W)
    (b : coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W))
    (hb : M.TensorEvaluation l E W b)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    {C D Z : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
    (κZ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj Z ⟶
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
          ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)))
    (gC : (M.quotient l E W).obj P ⟶ C) (gD : (M.quotient l E W).obj Q ⟶ D)
    (gZ : (M.quotient l E W).obj ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ⟶ Z)
    (hC : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map gC ≫
      (κC n).hom = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P)
    (hD : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map gD ≫
      (κD n).hom = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q)
    (hZ : ∀ n : ℕ, ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map gZ ≫
      κZ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app _)
    (ψ : Z ⟶ (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (C, D))
    (hψ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map ψ ≫
        (coefficientEvaluationTensorIso l E W n C D).hom ≫
        (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map (Prod.mkHom (κC n).hom (κD n).hom) =
      κZ n ≫ (coefficientScalarTensorIso l E W n P Q).hom) :
    b.hom.app (P, Q) ≫ (coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom gC gD) = gZ ≫ ψ := by
  apply coefficientSequenceComplex_hom_ext
  intro n
  let T := coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  have : IsIso (T.map (Prod.mkHom (κC n).hom (κD n).hom)) := by
    have hi : T.map (Prod.mkHom (κC n).hom (κD n).hom) ≫ T.map (Prod.mkHom (κC n).inv (κD n).inv)
        = 𝟙 _ := by
      rw [bifunctor_map_mkHom_comp, Iso.hom_inv_id, Iso.hom_inv_id, ← T.map_id]
      rfl
    have hi' : T.map (Prod.mkHom (κC n).inv (κD n).inv) ≫ T.map (Prod.mkHom (κC n).hom (κD n).hom)
        = 𝟙 _ := by
      rw [bifunctor_map_mkHom_comp, Iso.inv_hom_id, Iso.inv_hom_id, ← T.map_id]
      rfl
    exact ⟨_, hi, hi'⟩
  rw [← cancel_mono ((coefficientEvaluationTensorIso l E W n C D).hom ≫
    T.map (Prod.mkHom (κC n).hom (κD n).hom))]
  simp only [Functor.map_comp, Category.assoc]
  rw [hψ, reassoc_of% (hZ n),
    reassoc_of% (coefficientEvaluationTensorIso_naturality l E W n gC gD),
    bifunctor_map_mkHom_comp]
  simp only [hC, hD]
  exact hb n P Q

end OrdinaryQuotient

/-- A bifunctor sends a pair of isomorphisms to an isomorphism.
Source: Stacks 0011. -/
theorem isIso_bifunctor_map_mkHom {A B : Type*} [Category* A] [Category* B] (T : A × A ⥤ B)
    {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y') [IsIso f] [IsIso g] :
    IsIso (T.map (Prod.mkHom f g)) :=
  ⟨T.map (Prod.mkHom (inv f) (inv g)), by
    rw [bifunctor_map_mkHom_comp, IsIso.hom_inv_id, IsIso.hom_inv_id, ← T.map_id]
    rfl, by
    rw [bifunctor_map_mkHom_comp, IsIso.inv_hom_id, IsIso.inv_hom_id, ← T.map_id]
    rfl⟩

namespace OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The system K-flat tensor model comparison is natural in both inputs.
Source: Stacks 06YU. -/
theorem coefficientSystemTensorModelIso_naturality (S : CoefficientDerivedSystemTensors l E W)
    {P Q P' Q' : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P')
    (hQ' : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).map (Prod.mkHom f g)) ≫
        (coefficientSystemTensorModelIso l E W S P' Q' hP' hQ').hom =
      (coefficientSystemTensorModelIso l E W S P Q hP hQ).hom ≫
        S.systemClosed.tensor.map
          (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) := by
  have h := S.systemTensorModel.comparison.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨P', hP'⟩) f)
      (ObjectProperty.homMk (X := ⟨Q, hQ⟩) (Y := ⟨Q', hQ'⟩) g))
  unfold coefficientSystemTensorModelIso CoefficientTensorModels.iso
  dsimp only [coefficientKFlatInclusion, Iso.app_hom,
    Functor.comp_map, Functor.prod_map, Prod.mkHom, ObjectProperty.ι,
    inducedFunctor, ObjectProperty.homMk] at h ⊢
  exact h
/-- Transport of a reduction tensor square along strict presentations: if each presentation
is the comparison `ε` followed by a localized strict map, and the strict maps intertwine the
strict tensor maps, the square for the presentations gives the square for `ε`.
Source: Stacks 07A4. -/
theorem tensorComparisonSquare_transport {A B K : Type*} [Category* A] [Category* B]
    [Category* K] (T : A × A ⥤ A) (T' : B × B ⥤ B) (F : A ⥤ B) (Q : K ⥤ B)
    {X Y Z : A} {XP XQ XZ C D Zc N N' : K}
    (s : Z ⟶ T.obj (X, Y)) (μ : T ⋙ F ⟶ F.prod F ⋙ T')
    (εP : F.obj X ⟶ Q.obj XP) (εQ : F.obj Y ⟶ Q.obj XQ) (εZ : F.obj Z ⟶ Q.obj XZ)
    [IsIso εP] [IsIso εQ]
    (eC : F.obj X ≅ Q.obj C) (eD : F.obj Y ≅ Q.obj D) (eZ : F.obj Z ≅ Q.obj Zc)
    (gC : XP ⟶ C) (gD : XQ ⟶ D) (gZ : XZ ⟶ Zc)
    (heC : eC.hom = εP ≫ Q.map gC) (heD : eD.hom = εQ ≫ Q.map gD)
    (heZ : eZ.hom = εZ ≫ Q.map gZ)
    (ψ : Zc ⟶ N') (b : XZ ⟶ N) (m : N ⟶ N') (hS : b ≫ m = gZ ≫ ψ)
    (I : Q.obj N ⟶ T'.obj (Q.obj XP, Q.obj XQ)) (I' : Q.obj N' ⟶ T'.obj (Q.obj C, Q.obj D))
    (hn : Q.map m ≫ I' = I ≫ T'.map (Prod.mkHom (Q.map gC) (Q.map gD)))
    (hsq : CoefficientTensorComparisonSquare T T' F Q s μ eC.hom eD.hom eZ.hom ψ I') :
    CoefficientTensorComparisonSquare T T' F Q s μ εP εQ εZ b I := by
  have : IsIso (Q.map gC) := by
    have : IsIso (εP ≫ Q.map gC) := by
      rw [← heC]
      infer_instance
    exact IsIso.of_isIso_comp_left εP _
  have : IsIso (Q.map gD) := by
    have : IsIso (εQ ≫ Q.map gD) := by
      rw [← heD]
      infer_instance
    exact IsIso.of_isIso_comp_left εQ _
  have := isIso_bifunctor_map_mkHom T' (Q.map gC) (Q.map gD)
  unfold CoefficientTensorComparisonSquare at hsq ⊢
  rw [← cancel_mono (T'.map (Prod.mkHom (Q.map gC) (Q.map gD)))]
  simp only [Category.assoc]
  rw [bifunctor_map_mkHom_comp, ← heC, ← heD, hsq, heZ, ← hn, Category.assoc,
    ← Q.map_comp_assoc, ← Q.map_comp_assoc, hS]

/-- The universal comparison of the ordinary quotient system realizes the binary tensor
normalization of a derived reduction: on flat-term K-flat inputs, the ordinary tensor
comparison `b` and the comparison `ε` fit into the normalized reduction tensor square.
Source: Stacks 07A4, 0941.
Proof: each presentation of `hR` is `ε` followed by the localized ordinary transpose of its
strict unit map, whose finite evaluations are the normalized evaluation isomorphisms. These
transposes intertwine `b` with the strict tensor map of `hR` before localization, and the
square of `hR` transports along them. -/
theorem OrdinaryModel.reductionTensor_normalization (M : OrdinaryModel l E W)
    (R : CoefficientDerivedSystemReduction l E W)
    (hR : CoefficientReductionTensorNormalization l E W R)
    (ε : DerivedCategory.Q ⋙ R.reduction ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hcomp : ∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
      P.IsKFlatIndependentCoefficients → (∀ p : ℤ, (P.X p).IsFlatOnSite) → IsIso (ε.app P))
    (hhom : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (f : (M.quotient l E W).obj Q ⟶ I),
      R.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          (systemLimitUnit l E W M (constantLimitUnit l E W)).app I)
    (b : coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙ M.quotient l E W ≅
      (M.quotient l E W).prod (M.quotient l E W) ⋙
        coefficientTotalTensor.{u, t + 1, t} (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W))
    (hb : M.TensorEvaluation l E W b)
    (hpres : ∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) →
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) ((M.quotient l E W).obj P))
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (fP : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i))
    (fQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
      (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)) :
    CoefficientTensorComparisonSquare R.integralClosed.tensor R.systemClosed.tensor
      R.reduction DerivedCategory.Q
      (coefficientIntegralTensorModelIso l E W R.toCoefficientDerivedSystemTensors
        P Q hP hQ).hom R.reductionTensor.hom
      (ε.app P) (ε.app Q) (ε.app _)
      (b.hom.app (P, Q))
      (coefficientSystemTensorModelIso l E W R.toCoefficientDerivedSystemTensors
        ((M.quotient l E W).obj P) ((M.quotient l E W).obj Q)
        (hpres P hP fP) (hpres Q hQ fQ)).hom := by
  obtain ⟨C, D, Z, hC, hD, eC, eD, eZ, κC, κD, κZ, ψ, pC, pD, pZ, hψ, hsq⟩ :=
    hR P Q hP hQ fP fQ
  obtain ⟨gC, heC, hgC⟩ := exists_transpose_of_unitPresentation l E W M R.reduction
    R.adjunction ε hhom P C eC κC pC.adjunction
  obtain ⟨gD, heD, hgD⟩ := exists_transpose_of_unitPresentation l E W M R.reduction
    R.adjunction ε hhom Q D eD κD pD.adjunction
  obtain ⟨gZ, heZ, hgZ⟩ := exists_transpose_of_unitPresentation l E W M R.reduction
    R.adjunction ε hhom _ Z eZ κZ pZ.adjunction
  have hS := M.tensor_comp_map_eq l E W b hb P Q κC κD (fun n ↦ (κZ n).hom) gC gD gZ hgC hgD hgZ
    ψ hψ
  have hn := coefficientSystemTensorModelIso_naturality l E W R.toCoefficientDerivedSystemTensors
    (hpres P hP fP) (hpres Q hQ fQ) hC hD gC gD
  have := hcomp P hP fP
  have := hcomp Q hQ fQ
  exact tensorComparisonSquare_transport _ _ _ _ _ _ _ _ _ _ _ _ gC gD gZ heC heD heZ ψ _ _ hS _ _
    hn hsq

end OrdinaryQuotient

end WeilConjectures

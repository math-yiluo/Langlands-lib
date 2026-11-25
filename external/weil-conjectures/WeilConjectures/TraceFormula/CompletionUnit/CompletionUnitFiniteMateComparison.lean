/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Finite evaluation of the normalized tensor unit

Source: Stacks 0941, 0D6E, 07A6 and 09T5.
(blueprint: lem-trf-completion-unit-finite-mate-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

/-- Localization factors for the canonical square of exact functors. -/
private theorem square_factors
    {A B B' D : Type*} [Category* A] [Category* B] [Category* B'] [Category* D]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory D]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ B') (G₂ : B' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (I : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app I) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj I) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app I) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj I) =
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
  apply (cancel_epi (F₂.mapDerivedCategoryFactors.inv.app
    ((F₁.mapHomologicalComplex (.up ℤ)).obj I))).mp
  rw [Iso.inv_hom_id_app_assoc]
  have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ I
  have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors G₁ G₂ I
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hG, Functor.mapDerivedCategoryNatIso_fac]
  rw [← hF]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [F₂.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]

/-- Localization of a termwise adjunction unit agrees in the two quotient coordinates. -/
private theorem localized_unit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F : A ⥤ B} {R : B ⥤ A} [F.Additive] [R.Additive] (a : F ⊣ R)
    (Q : CochainComplex A ℤ) :
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  rfl

/-- The finite scalar unit on a K-flat complex in the cochain localization coordinates. -/
private theorem finiteModel_unit
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          (coefficientFiniteReductionModel l E W Q hQ n).hom ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) := by
  have h := (derivedScalarExtensionRestrictionAdjunction l E W n).choose_spec Q hQ
  have hfac := (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh_hom_app
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
  have hfac' : (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) := by
    erw [hfac]
    change (scalarReductionDerivedRestriction l E W n).map (𝟙 _) ≫ _ ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [(scalarReductionRestriction l E W n).mapDerivedCategory.map_id,
      DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]
  have hunit : DerivedCategory.Qh.map
      ((((scalarReductionExtension_adjunction l E W n).choose).mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) :=
    localized_unit (scalarReductionExtension_adjunction l E W n).choose Q
  have hmodel : (coefficientFiniteReductionModel l E W Q hQ n).hom =
      (scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) := by
    dsimp only [coefficientFiniteReductionModel, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app, asIso_hom]
    change (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
    erw [(coefficientFiniteDerivedExtension l E W n).map_id, Category.id_comp]
    rfl
  refine (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (coefficientFiniteDerivedRestriction l E W n).map f ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))
          hmodel).trans ?_
  exact (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (scalarReductionDerivedRestriction l E W n).map
        ((scalarReductionCounit l E W n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) ≫ f) hfac'.symm).trans
      (h.trans hunit)

/-- Extend the defining K-injective normalization to the projection at any tower. -/
private theorem limitUnit_projection
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    η.app Z ≫ (coefficientConstantTowerProjection l E W n).app
        (DerivedCategory.Q.obj Z) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app Z =
      DerivedCategory.Q.map (c.inv.app Z ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app Z) := by
  let ev := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)
  let τ := NatTrans.mapHomologicalComplex
    (lim.π (op n) : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ _) ⟶ ev) (.up ℤ)
  let α := η ≫ Functor.whiskerLeft DerivedCategory.Q
    (coefficientConstantTowerProjection l E W n) ≫
      (coefficientConstantTowerEvaluationFactors l E W n).hom
  let β := Functor.whiskerRight (c.inv ≫ τ) DerivedCategory.Q
  have hJ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective] : α.app J = β.app J := by
    change η.app J ≫ ((coefficientConstantTowerProjection l E W n).app
      (DerivedCategory.Q.obj J) ≫ _) = _
    erw [(coefficientConstantTowerProjection_exists l E W n).choose_spec.1 J]
    rw [← Category.assoc, hηnorm, ← DerivedCategory.Q.map_comp]
    rfl
  obtain ⟨J, hJ', j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective Z
  let : J.IsKInjective := hJ'
  let : QuasiIso j := hj
  have : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map j) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology j ev
  apply (cancel_mono (DerivedCategory.Q.map
    ((ev.mapHomologicalComplex (.up ℤ)).map j))).mp
  change α.app Z ≫ (ev.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map j =
    β.app Z ≫ (ev.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map j
  rw [← α.naturality, ← β.naturality, hJ J]

/-- The specified ordinary tensor unit agrees with the chosen scalar unit. -/
private theorem ordinary_unit (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
    ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        M.limitComparison.hom.app ((M.quotient l E W).obj Q) ≫
        limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor (op n) ≫
        (NatTrans.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app
            ((M.quotient l E W).obj Q) ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
      (((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
        (.up ℤ)).unit.app Q := by
  apply HomologicalComplex.hom_ext
  intro p
  have hp := M.limitComparison_projection ((M.quotient l E W).obj Q) n p
  have hunit := M.unit_tensor (Q.X p) n
  have hu := (scalarReductionExtension_adjunction l E W n).choose_spec (Q.X p)
  change M.adjunction.unit.app (Q.X p) ≫
    (M.limitComparison.hom.app ((M.quotient l E W).obj Q) ≫
      limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor (op n)).f p ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (M.tensor.obj (Q.X p)) ≫
    (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app (Q.X p)) =
      ((scalarReductionExtension_adjunction l E W n).choose).unit.app (Q.X p)
  refine (congrArg (fun f ↦ M.adjunction.unit.app (Q.X p) ≫ f ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (M.tensor.obj (Q.X p)) ≫
    (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app (Q.X p))) hp).trans ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  exact (hunit V x).trans (by
    dsimp only [unrestrictedIntegralTensorSection, unrestrictedIntegralReductionFunctor,
      unrestrictedIntegralReductionExistence, scalarReductionExistence] at hu ⊢
    exact (hu V x).symm)

/-- Project the comparison with total limit in the exact finite restriction coordinates. -/
private theorem system_projection
    (M : OrdinaryModel l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (hc : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (n : ℕ) (p : ℤ),
      (c.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p = limit.π (Z.X p) (op n))
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (DerivedCategory.Q.map (M.limitComparison.hom.app I) ≫
        η.app ((tower l E W).obj I) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I)) ≫
        (coefficientSequenceProjection l E W n).app (DerivedCategory.Q.obj I) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app I) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj I) =
      DerivedCategory.Q.map (M.limitComparison.hom.app I ≫
        limit.π ((tower l E W).obj I).asFunctor (op n) ≫
        (NatTrans.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app I) := by
  let U := coefficientSequenceRestriction l E W
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)
  let F := coefficientSequenceEvaluation l E W n
  let R := scalarReductionRestriction l E W n
  let e := eqToIso (coefficientSequenceRestriction_evaluation l E W n)
  have hsq := square_factors U V F R e I
  have hπ := limitUnit_projection l E W c η hηnorm ((tower l E W).obj I) n
  have hcπ : c.inv.app ((tower l E W).obj I) ≫
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
        ((tower l E W).obj I) = limit.π ((tower l E W).obj I).asFunctor (op n) := by
    apply (cancel_epi (c.hom.app ((tower l E W).obj I))).mp
    rw [Iso.hom_inv_id_app_assoc]
    apply HomologicalComplex.hom_ext
    intro p
    exact (hc _ n p).symm
  rw [hcπ] at hπ
  dsimp only [coefficientSequenceProjection, NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  erw [(coefficientConstantTowerProjection l E W n).naturality_assoc
    (U.mapDerivedCategoryFactors.inv.app I)]
  have hsq' : (coefficientConstantTowerEvaluation l E W n).map
      (U.mapDerivedCategoryFactors.inv.app I) ≫
      (coefficientRestrictedEvaluationIso l E W n).hom.app (DerivedCategory.Q.obj I) ≫
      R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app I) ≫
      R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) =
    V.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
    exact hsq
  erw [hsq']
  erw [reassoc_of% hπ]
  simp only [← DerivedCategory.Q.map_comp]
  rfl

/-- A comparison with the normalized ordinary tensor unit has the fixed finite values.
This is solely the finite adjunction-mate calculation: it constructs no derived
functor, comparison, adjunction or system unit.

Source: Stacks 07A6 and 0941, the finite-mate calculation in step 3 of
lem-trf-completion-unit-derived-adjunction-comparison, and the coefficient scalar
adjunction normalization from 06YY and 09T5.
(blueprint: lem-trf-completion-unit-finite-mate-comparison).

Proof: First compute eta followed by the actual nth total-limit projection on a
K-injective tower, using hηnorm and the defining normalization of that projection.
The result is the localization of c inverse followed by the ordinary degreewise
projection. Naturality and a K-injective resolution extend this identity to every
tower; exact evaluation sends that resolution to a quasi-isomorphism, so its
localized map can be cancelled. Transport through the exact-restriction evaluation
factors. The identities hc and M.limitComparison_projection identify the resulting
projection of the displayed composite with the ordinary limit projection.
Now project hunit to level n. S.unit_projection and naturality of the projection
identify its left side with the finite scalar adjunction transpose of the evaluated
comparison, conjugated by S.reductionEvaluation. The ordinary unit on its right side
is x mapped to 1 tensor x by M.unit_tensor and M.evaluation. The normalized finite
scalar derived unit on a K-flat representative has exactly this value, after
coefficientFiniteReductionModel and the exact scalar-restriction factors.
The finite Hom equivalence is injective; cancelling its common invertible factors
gives the displayed equality. This uses equality of adjunction mates, never joint
faithfulness of derived evaluations. The argument includes n = 0, the zero complex,
and unbounded complexes; flat terms are only used for the stated K-flat model. -/
theorem finiteComparison_of_unit
    (S : CoefficientDerivedSystemCalculus l E W) (M : OrdinaryModel l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (hc : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (n : ℕ) (p : ℤ),
      (c.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p = limit.π (Z.X p) (op n))
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (ε : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hunit : ∀ Q : CochainComplex (scalarReductionSource l E W) ℤ,
      S.adjunction.homEquiv (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj ((M.quotient l E W).obj Q)) (ε.app Q) =
        DerivedCategory.Q.map
          ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
      (DerivedCategory.Q.map (M.limitComparison.hom.app ((M.quotient l E W).obj Q)) ≫
        η.app ((tower l E W).obj ((M.quotient l E W).obj Q)) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app
            ((M.quotient l E W).obj Q)))) :
    ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hQ : Q.IsKFlatIndependentCoefficients)
        (_hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E W n).map (ε.app Q) ≫
            (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
              ((M.quotient l E W).obj Q) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
          (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj Q) ≫
            (coefficientFiniteReductionModel l E W Q hQ n).hom := by
  intro Q hQ _hflat n
  let P := DerivedCategory.Q.obj Q
  let I := (M.quotient l E W).obj Q
  let R := scalarReductionRestriction l E W n
  let e := (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q
  apply (cancel_epi ((S.reductionEvaluation n).inv.app P)).mp
  erw [Iso.inv_hom_id_app_assoc]
  apply ((coefficientFiniteAdjunction l E W n).homEquiv P _).injective
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))).mp
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (S.unit_projection P n)]
  erw [← (coefficientSequenceProjection l E W n).naturality_assoc (ε.app Q)]
  rw [← reassoc_of% (S.adjunction.homEquiv_unit P (DerivedCategory.Q.obj I) (ε.app Q)), hunit Q]
  erw [R.mapDerivedCategoryFactors.hom.naturality e]
  have hp := system_projection l E W M c hc η hηnorm I n
  have hu := ordinary_unit l E W M Q n
  simp only [Category.assoc] at hp ⊢
  erw [reassoc_of% hp]
  simp only [Functor.comp_map, ← Functor.map_comp, Category.assoc]
  erw [hu]
  exact (finiteModel_unit l E W Q hQ n).symm

end WeilConjectures.CompletionUnit

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Coherent strict presentations of primitive reduction

Source: Stacks, Tags 06YY, 07A6 and 0941; the canonical strict quotient construction.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.defeqAttrib.useBackward true in
private theorem exact_const_unit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (I : CochainComplex B ℤ) :
    F.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ I) ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app I) := by
  let J := (HomotopyCategory.quotient B (.up ℤ)).obj I
  have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso B (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit J
  let d := adj.mapDerivedCategoryRightDerivedAdjunction
  let e := (DerivedCategory.quotientCompQhIso B).app I
  have ht :
      F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app J) ≫
        e.hom =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app I) := by
    have hf := F.mapDerivedCategoryFactorsh_hom_app
      ((G.mapHomologicalComplex (.up ℤ)).obj I)
    change F.mapDerivedCategoryFactorsh.hom.app
      ((G.mapHomotopyCategory (.up ℤ)).obj J) = _ at hf
    rw [hf]
    dsimp [J]
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      Category.assoc]
    erw [DerivedCategory.quotientCompQhIso_hom_naturality]
    dsimp only [Functor.comp_obj]
    erw [CategoryTheory.Functor.map_id]
    erw [CategoryTheory.Functor.map_id DerivedCategory.Qh]
    repeat' erw [Category.id_comp]
    rfl
  calc
    _ = F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        (F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app J) ≫
          d.counit.app (DerivedCategory.Qh.obj J)) ≫ e.hom := by
      dsimp only [Functor.rightDerivedFunctorUnitQ]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      erw [d.counit.naturality e.hom]
      rfl
    _ = F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        (F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app J)) ≫
        e.hom := by erw [hfac]
    _ = _ := by
      rw [Category.assoc, ht]
      simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp,
        Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem derived_transpose_ordinary
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (a : P ⟶ (G.mapHomologicalComplex (.up ℤ)).obj I) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map a ≫ G.rightDerivedFunctorUnitQ I) ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        (((adj.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm a) := by
  have hc : (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app I =
      (adj.mapHomologicalComplex (.up ℤ)).counit.app I := by
    apply HomologicalComplex.hom_ext
    intro i
    exact (Adjunction.mapHomologicalComplex_counit_app_f (.up ℤ) adj I i).symm
  rw [CategoryTheory.Functor.map_comp, Category.assoc, exact_const_unit adj I]
  rw [F.mapDerivedCategoryFactors_hom_naturality_assoc a]
  rw [Adjunction.homEquiv_counit, hc, CategoryTheory.Functor.map_comp]

end WeilConjectures

namespace WeilConjectures
open CompletionUnit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

-- Keep large coefficient-functor elaboration local to this proof.
private theorem normalized_comparison (Y : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E Y) (M : OrdinaryModel l E Y) :
    ∃ ε : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E Y ⋙ DerivedCategory.Q,
      (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory, IsIso (ε.app P.obj)) ∧
      (∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Y n).map (ε.app P.obj) ≫
          (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app
            ((M.quotient l E Y).obj P.obj) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P.obj) =
        (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientFiniteReductionModel l E Y P.obj P.property.1 n).hom) ∧
      (∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
        S.adjunction.homEquiv (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj ((M.quotient l E Y).obj P)) (ε.app P) =
          DerivedCategory.Q.map ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
            (systemLimitUnit l E Y M (constantLimitUnit l E Y)).app
              ((M.quotient l E Y).obj P)) := by
  classical
  let c := termwiseLimitComparison l E Y
  let η := constantLimitUnit l E Y
  have hsys := systemLimitUnit_isIso l E Y M c η (constantLimitUnit_normalization l E Y)
  have hδ : (coefficientSequenceLimit l E Y).IsRightDerivedFunctor
      (systemLimitUnit l E Y M η)
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E Y) (.up ℤ)) := by
    apply (CategoryTheory.derives (ordinaryLimit l E Y)).isRightDerivedFunctor_of_isIso
      (systemLimitUnit l E Y M η)
    intro I
    exact hsys I.obj I.property
  obtain ⟨A, ε, a, _, hflat, hhom⟩ :=
    tensor_derived_exists l E Y S M (systemLimitUnit l E Y M η) hδ
  let d := S.adjunction.leftAdjointUniq a
  let ε' : DerivedCategory.Q ⋙ S.reduction ⟶ M.quotient l E Y ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q d.hom ≫ ε
  have hu (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
      S.adjunction.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj ((M.quotient l E Y).obj P)) (ε'.app P) =
        DerivedCategory.Q.map ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          (systemLimitUnit l E Y M η).app ((M.quotient l E Y).obj P) := by
    have h := hhom P ((M.quotient l E Y).obj P) (𝟙 _)
    have hid : ε.app P ≫ DerivedCategory.Q.map
        (𝟙 ((M.quotient l E Y).obj P)) = ε.app P := by
      rw [(DerivedCategory.Q (C := coefficientSequenceModules l E Y)).map_id]
      exact Category.comp_id _
    have hh := (congrArg (a.homEquiv (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj ((M.quotient l E Y).obj P))) hid).symm.trans h
    simp only [Adjunction.homEquiv_id] at hh
    rw [← hh]
    change S.adjunction.homEquiv _ _ (d.hom.app _ ≫ ε.app P) = _
    rw [S.adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [S.adjunction.unit_leftAdjointUniq_hom_app a]
    exact (a.homEquiv_unit _ _ _).symm
  refine ⟨ε', ?_, ?_, hu⟩
  · intro P
    have := hflat P.obj P.property.1 P.property.2
    dsimp only [ε', NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  · intro P n
    exact finiteComparison_of_unit l E Y S M c (termwiseLimitComparison_projection l E Y)
      η (constantLimitUnit_normalization l E Y) ε' hu P.obj P.property.1 P.property.2 n

end WeilConjectures

namespace WeilConjectures
open CompletionUnit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf SheafOfModules.monoidalCategory scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceRestriction coefficientSequenceEvaluation

private theorem moduleEqToHom_heq
    {D : Type*} [Category D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {A B : SheafOfModules.{u} R}
    (h : A = B) (U : Dᵒᵖ) (x : A.val.obj U) :
    HEq (((eqToHom h).val.app U) x) x := by
  subst B
  rfl

private theorem abEqToHom_heq {A B : AddCommGrpCat.{u}} (h : A = B) (x : A) :
    HEq ((eqToHom h : A ⟶ B) x) x := by
  subst B
  rfl

private theorem restricted_section_cancel (Y : Scheme.{t})
    (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (y : ((coefficientSequenceEvaluation l E Y n).obj M).val.obj U) :
    ((eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom.app M).val.app U
      (integralComparisonRestrictedSection l E Y M n U
        (integralComparisonSequenceSection l E Y M n U y)) = y := by
  simp only [eqToIso.hom, eqToHom_app]
  have hleft := moduleEqToHom_heq
    (Functor.congr_obj (coefficientSequenceRestriction_evaluation l E Y n) M) U
    (integralComparisonRestrictedSection l E Y M n U
      (integralComparisonSequenceSection l E Y M n U y))
  have hcast : HEq (integralComparisonRestrictedSection l E Y M n U
      (integralComparisonSequenceSection l E Y M n U y))
      (integralComparisonSequenceSection l E Y M n U y) := cast_heq _ _
  have hright : HEq (integralComparisonSequenceSection l E Y M n U y) y :=
    abEqToHom_heq (coefficientSequenceEvaluationAb_eq l E Y M n U) y
  exact eq_of_heq (hleft.trans (hcast.trans hright))

-- Keep large coefficient-functor elaboration local to this proof.
private theorem ordinary_unit_section (Y : Scheme.{t})
    (M : OrdinaryModel l E Y) (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (n : ℕ) (i : ℤ) (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
    let C := (M.quotient l E Y).obj P
    let I := (tower l E Y).obj C
    let a : P ⟶ ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
        scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ)).obj I :=
      (M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P
    let b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ)).obj P ⟶ I :=
      (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Y)).mapHomologicalComplex
        (.up ℤ)).homEquiv P I).symm a
    (((b.f i).app (op n)).val.app U) x =
      integralComparisonRestrictedSection l E Y (C.X i) n U
        (integralComparisonSequenceSection l E Y (C.X i) n U
          ((((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).inv.app P).f i).val.app U
            (unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x))) := by
  dsimp only
  let C := (M.quotient l E Y).obj P
  let T := (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).app (C.X i) ≪≫
    (scalarReductionRestriction l E Y n).mapIso ((M.evaluation n).app (P.X i))
  have hinj : Function.Injective (fun z ↦ T.hom.val.app U z) := by
    intro y z h
    have hi (w) : T.inv.val.app U (T.hom.val.app U w) = w :=
      congrArg (fun k ↦ k.val.app U w) T.hom_inv_id
    exact (hi y).symm.trans ((congrArg (fun w ↦ T.inv.val.app U w) h).trans (hi z))
  apply hinj
  have hunit := M.unit_tensor (P.X i) n U x
  change T.hom.val.app U _ = _ at hunit
  refine hunit.trans ?_
  dsimp only [T, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    restricted_section_cancel l E Y (C.X i) n U]
  change unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x =
    ((M.evaluation n).hom.app (P.X i)).val.app U
      (((M.evaluation n).inv.app (P.X i)).val.app U
        (unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x))
  exact (congrArg (fun f ↦ f.val.app U
    (unrestrictedIntegralTensorSection l E Y n (P.X i) U 1 x))
      ((M.evaluation n).app (P.X i)).inv_hom_id).symm

end WeilConjectures

namespace WeilConjectures
open CompletionUnit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem constantUnit_eq (Y : Scheme.{t})
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ℤ) :
    (constantLimitUnit l E Y).app I =
      DerivedCategory.Q.map ((termwiseLimitComparison l E Y).inv.app I) ≫
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
          scalarReductionSource l E Y).rightDerivedFunctorUnitQ I := by
  simp [constantLimitUnit, Functor.rightDerivedFunctorUnitQ,
    Functor.mapHomotopyCategoryFactors]

-- Coefficient adjunctions involve large, independently chosen comparison functors.
/-- Every good complex admits a strict quotient presentation whose comparison is
the actual adjunction transpose of the strict tensor-unit map.

Source: Stacks, sites-cohomology.tex, Tags 06YY, 07A6 and 0941; the first step of
lem-trf-primitive-quotient-realizations-unique after the whole-system coherence repair.
(blueprint: lem-trf-coherent-primitive-reduction-presentation).

Proof: construct the ordinary quotient-system tensor functor, with transitions induced
by the quotient maps, and its adjunction to coefficient restriction followed by limit.
Its unit sends a section x to the compatible family of sections 1 tensor x. Apply this
functor termwise to P to obtain C. Its evaluation identifications give kappa and their
horizontal compatibility. Derive the ordinary adjunction using flat-term K-flat
resolutions and simultaneous K-injective systems. Exact coefficient restriction and
derived composition identify the right adjoint with coefficientSequenceLimit. Compare
the resulting left adjoint with S.reduction by the unique isomorphism of left adjoints
whose right mate is the identity. The derived comparison on P is invertible because P
is flat-term K-flat, giving e. Transposing its finite evaluations and using
S.counit_projection identifies them with the normalized finite tensor comparisons;
this proves CoefficientReductionPresentation. The derived Hom formula identifies the
transpose of e with the localization of the ordinary tensor-unit tower map b. Its
section formula is exactly the displayed formula in IsIntegralComparisonPresentationCoherent:
the finite evaluation identifications and their inverses cancel. Transposing through
the constant-tower/limit adjunction yields the required entire-tower equation for b,
not merely its finite evaluations. These arguments are unbounded, work for arbitrary
S by uniqueness of adjoints, and include zero complexes and exponent one. -/
theorem coherentPrimitiveReductionPresentation {Y : Scheme.{t}}
    (S : CoefficientDerivedSystemCalculus l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    ∃ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
          (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj),
      CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
        P.obj P.property.1 C e κ ∧
      IsIntegralComparisonPresentationCoherent l E Y S P.obj C e κ := by
  classical
  obtain ⟨M⟩ := ordinaryModel_exists l E Y
  obtain ⟨ε, hiso, heval, hu⟩ := normalized_comparison l E Y S M
  have := hiso P
  let C := (M.quotient l E Y).obj P.obj
  let I := (tower l E Y).obj C
  let e := asIso (ε.app P.obj)
  let κ (n : ℕ) := (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P.obj
  have hC : CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ := by
    constructor
    · intro n
      exact heval P n
    · intro m n h
      apply HomologicalComplex.hom_ext
      intro i
      exact M.transition (P.obj.X i) h
  refine ⟨C, e, κ, hC, ?_⟩
  unfold IsIntegralComparisonPresentationCoherent
  let a : P.obj ⟶ ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
      scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ)).obj I :=
    (M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P.obj
  let b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤
      ℕᵒᵖ ⥤ scalarReductionSource l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj ⟶ I :=
    (((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Y)).mapHomologicalComplex
      (.up ℤ)).homEquiv P.obj I).symm a
  refine ⟨b, ?_, ?_⟩
  · intro n i U x
    exact ordinary_unit_section l E Y M P.obj n i U x
  · have hlim : M.limitComparison.hom.app C =
        (termwiseLimitComparison l E Y).hom.app I := by
      apply limit.hom_ext
      intro n
      apply HomologicalComplex.hom_ext
      intro i
      exact (M.limitComparison_projection C n.unop i).trans
        (termwiseLimitComparison_projection l E Y I n.unop i).symm
    let T : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ scalarReductionSource l E Y := lim
    have hd : (systemLimitUnit l E Y M (constantLimitUnit l E Y)).app C =
        T.rightDerivedFunctorUnitQ I ≫ (coefficientConstantTowerLimit l E Y).map
          ((coefficientSequenceRestriction l E Y).mapDerivedCategoryFactors.inv.app C) := by
      dsimp only [systemLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app]
      rw [hlim, constantUnit_eq l E Y I]
      simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
      erw [(DerivedCategory.Q (C := scalarReductionSource l E Y)).map_id]
      erw [Category.id_comp]
    change (integralComparisonConstantTower l E Y).map
      (S.adjunction.homEquiv _ _ (ε.app P.obj)) ≫ _ = _
    erw [hu P.obj, hd]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    have hn := (integralComparisonConstantAdjunction l E Y).counit.naturality
      ((coefficientSequenceRestriction l E Y).mapDerivedCategoryFactors.inv.app C)
    erw [hn]
    simp only [CategoryTheory.Functor.id_map]
    have ht := derived_transpose_ordinary
      (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Y)) P.obj I a
    simp only [CategoryTheory.Functor.map_comp, Category.assoc] at ht
    erw [reassoc_of% ht]

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PrimitiveCounit.PrimitiveTensorReductionRepresentatives
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTransitionSquare
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationTensorChain
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Functorial strict quotient representatives

Source: Stacks Project, Tags 06YY, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived

universe t u v c d r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PrimitiveCounit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local implicit_reducible] CategoryTheory.uniformProd
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  coefficientEvaluationTensorIso coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingSheafUnrestricted HasDerivedCategory.standard
  SheafOfModules.monoidalCategory
  Scheme.residueField Functor.leftAdjoint Functor.mapDerivedCategory
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology constantSheaf
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem finite_unit_step
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (k : ℤ) :
    (coefficientOrdinaryScalarAdjunction l E W (n + 1)).unit.app (P.X k) ≫
      ((unrestrictedIntegralTransition l E W n).app P).f k =
        (coefficientOrdinaryScalarAdjunction l E W n).unit.app (P.X k) := by
  ext U x
  have hm := (scalarReductionExtension_adjunction l E W (n + 1)).choose_spec (P.X k) U x
  have hn := (scalarReductionExtension_adjunction l E W n).choose_spec (P.X k) U x
  change (((unrestrictedIntegralTransition l E W n).app P).f k).val.app U
    (((coefficientOrdinaryScalarAdjunction l E W (n + 1)).unit.app (P.X k)).val.app U x) = _
  change ((coefficientOrdinaryScalarAdjunction l E W (n + 1)).unit.app (P.X k)).val.app U x =
    unrestrictedIntegralTensorSection l E W (n + 1) (P.X k) U 1 x at hm
  change ((coefficientOrdinaryScalarAdjunction l E W n).unit.app (P.X k)).val.app U x =
    unrestrictedIntegralTensorSection l E W n (P.X k) U 1 x at hn
  erw [hm, hn]
  have ht := (unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec
    P k U 1 x
  change (((unrestrictedIntegralTransition l E W n).app P).f k).val.app U
    (unrestrictedIntegralTensorSection l E W (n + 1) (P.X k) U 1 x) =
      unrestrictedIntegralTensorSection l E W n (P.X k) U
        ((integralCoefficientSheafTransition l E W n).hom.app U 1) x at ht
  have h1 : (integralCoefficientSheafTransition l E W n).hom.app U 1 = 1 :=
    (RingCat.Hom.hom ((integralCoefficientSheafTransition l E W n).hom.app U)).map_one
  erw [h1] at ht
  exact ht

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem unit_square {A : Type*} [Category A]
    {X L Bm Bn Fm Fn : A} (u : X ⟶ L) (πm : L ⟶ Bm) (πn : L ⟶ Bn)
    (a : Bm ≅ Fm) (b : Bn ≅ Fn) (um : X ⟶ Fm) (un : X ⟶ Fn)
    (s : Bm ⟶ Bn) (t : Fm ⟶ Fn)
    (hm : u ≫ πm ≫ a.hom = um) (hn : u ≫ πn ≫ b.hom = un)
    (ht : um ≫ t = un) (hc : πm ≫ s = πn) :
    um ≫ t = um ≫ (a.inv ≫ s ≫ b.hom) := by
  rw [ht, ← hm]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc πm s, hc]
  exact hn.symm

-- Normalize the coefficient functor and complex instances within this declaration.
private def tensorLevel
    (S : CoefficientDerivedSystemReduction l E W)
    (M : ReductionRepresentatives l E W S)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) :
    ((restrictComplex l E W).obj
      ((coefficientTotalTensor.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
          (M.complexes.obj P, M.complexes.obj Q))).asFunctor.obj (op n) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)).obj (op n) :=
  restrictEvaluation l E W _ n ≪≫
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
      (coefficientEvaluationTensorIso l E W n (M.complexes.obj P) (M.complexes.obj Q) ≪≫
        (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).mapIso
          (((M.evaluation n).app P).prod ((M.evaluation n).app Q))) ≪≫
    finiteTensorBridge l E W n P.obj Q.obj

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem nat_eqToIso_section_heq
    {A : Type*} [Category A] {B : Type*} [Category B]
    {J : GrothendieckTopology B} {R : Sheaf J RingCat}
    {F G : A ⥤ SheafOfModules R} (h : F = G)
    (M : A) (V : Bᵒᵖ) (x : (F.obj M).val.obj V) :
    HEq (((eqToIso h).hom.app M).val.app V x) x := by
  cases h
  rfl

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem ab_eqToHom_section_heq {A B : AddCommGrpCat.{v}} (h : A = B)
    (x : A) : HEq ((eqToHom h) x) x := by
  cases h
  rfl

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem restrictionEvaluation_section (W : Scheme.{t})
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    (((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app M).val.app U)
      (integralComparisonRestrictedSection l E W M n U x) =
        coefficientEvaluationSection l E W M n U x := by
  have h := nat_eqToIso_section_heq
    (coefficientSequenceRestriction_evaluation l E W n) M U
    (integralComparisonRestrictedSection l E W M n U x)
  have hx : HEq (integralComparisonRestrictedSection l E W M n U x) x :=
    cast_heq _ _
  have hy := ab_eqToHom_section_heq
    (coefficientSequenceEvaluationAb_eq l E W M n U).symm x
  exact eq_of_heq (h.trans (hx.trans hy.symm))

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem module_map_presheaf_heq {B : Type c} [Category.{d} B]
    {R : Bᵒᵖ ⥤ RingCat.{r}} (M : PresheafOfModules.{r} R)
    {V U : Bᵒᵖ} (f : V ⟶ U) :
    HEq (fun x : M.obj V ↦ M.map f x)
      (fun x : M.presheaf.obj V ↦ M.presheaf.map f x) := by
  rfl

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem presheaf_map_apply {B : Type c} [Category.{d} B]
    {R : Bᵒᵖ ⥤ RingCat.{r}} (M : PresheafOfModules.{r} R)
    {V U : Bᵒᵖ} (f : V ⟶ U) (x : M.obj V) :
    M.presheaf.map f x = M.map f x := rfl

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem generator_presheaf_restrict {B : Type c} [Category.{d} B]
    (J : GrothendieckTopology B) [HasSheafify J AddCommGrpCat.{max c d r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d r}]
    (S : Sheaf J CommRingCat.{max c d r})
    (P Q : CochainComplex (SheafOfModules.{max c d r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ)
    (p q k : ℤ) (h : p + q = k) {V U : Bᵒᵖ} (f : V ⟶ U)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((coefficientTotalTensor.{r, c, d} J S).obj (P, Q)).X k).val.presheaf.map f
      (coefficientTensorGenerator.{r, c, d} J S P Q p q k h V x y) =
    coefficientTensorGenerator.{r, c, d} J S P Q p q k h U
      ((P.X p).val.presheaf.map f x) ((Q.X q).val.presheaf.map f y) := by
  simp only [presheaf_map_apply]
  exact CategoryTheory.ringedSiteTensorGenerator_restrict.{c, d, r} J S P Q p q k h f x y

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem function_heq_apply {A A' : Type v} {B B' : Type r}
    (ha : A = A') (hb : B = B') {f : A → B} {g : A' → B'} (hf : HEq f g)
    {x : A} {y : A'} (hx : HEq x y) : HEq (f x) (g y) := by
  subst A'
  subst B'
  cases hf
  cases hx
  rfl

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem restricted_transition_section (W : Scheme.{t})
    (M : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m) (U : W.ProEtᵒᵖ)
    (x : M.val.obj (op (m, U.unop))) :
    (((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op).val.app U
      (integralComparisonRestrictedSection l E W M m U x) =
    integralComparisonRestrictedSection l E W M n U
      (M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  have hf : HEq
      (fun z : (((coefficientSequenceRestriction l E W).obj M).obj (op m)).val.obj U ↦
        (((coefficientSequenceRestriction l E W).obj M).map (homOfLE h).op).val.app U z)
      (fun z : M.val.obj (op (m, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op z) := by
    delta coefficientSequenceRestriction
    exact (coefficientSequenceRestriction_exists l E W).exists.choose_spec.2.1 M m n h U
  have hf' := hf.trans (module_map_presheaf_heq M.val
    (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
  have hx : HEq (integralComparisonRestrictedSection l E W M m U x) x := cast_heq _ _
  have hy : HEq (integralComparisonRestrictedSection l E W M n U
      (M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x))
      (M.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := cast_heq _ _
  exact eq_of_heq ((function_heq_apply
    (integralComparisonRestrictedSectionType l E W M m U)
    (integralComparisonRestrictedSectionType l E W M n U) hf' hx).trans hy.symm)

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem reduction_step
    (S : CoefficientDerivedSystemReduction l E W)
    (M : ReductionRepresentatives l E W S)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) :
    let C := M.complexes.obj P
    let a (j : ℕ) := restrictEvaluation l E W C j ≪≫
      ((scalarReductionRestriction l E W j).mapHomologicalComplex (.up ℤ)).mapIso
        ((M.evaluation j).app P)
    ((restrictComplex l E W).obj C).asFunctor.map (homOfLE (Nat.le_succ n)).op ≫
      (a n).hom = (a (n + 1)).hom ≫ (unrestrictedIntegralTransition l E W n).app P.obj := by
  dsimp only
  let C := M.complexes.obj P
  let a (j : ℕ) := restrictEvaluation l E W C j ≪≫
    ((scalarReductionRestriction l E W j).mapHomologicalComplex (.up ℤ)).mapIso
      ((M.evaluation j).app P)
  symm
  apply (a (n + 1)).eq_inv_comp.mp
  apply HomologicalComplex.hom_ext
  intro i
  let πm := (integralOperationsForgetSheaf.{max u (t+1)} (Scheme.ProEt.topology W)).map
    (completedIntegralCommRingProjectionUnrestricted l E W (n + 1))
  let πn := (integralOperationsForgetSheaf.{max u (t+1)} (Scheme.ProEt.topology W)).map
    (completedIntegralCommRingProjectionUnrestricted l E W n)
  let τ := integralCoefficientSheafTransition l E W n
  have hπ : πm ≫ τ = πn := integralProjection_step l E W n
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology W) πm.hom :=
    completedProjection_locallySurjective l E W (n + 1)
  apply WeilConjectures.restricted_extension_hom_ext πm πn τ hπ
    (coefficientOrdinaryScalarAdjunction l E W (n + 1)) (P.obj.X i)
    ((scalarReductionExtension l E W n).obj (P.obj.X i))
  let e (j : ℕ) := (HomologicalComplex.eval _ _ i).mapIso (a j)
  let I := (coefficientSequenceRestriction l E W).obj (C.X i)
  have ha (j : ℕ) : M.unit P i ≫ limit.π I (op j) ≫ (e j).hom =
      (coefficientOrdinaryScalarAdjunction l E W j).unit.app (P.obj.X i) := by
    exact M.unit_evaluation P j i
  change (coefficientOrdinaryScalarAdjunction l E W (n+1)).unit.app (P.obj.X i) ≫
      (((unrestrictedIntegralTransition l E W n).app P.obj).f i) =
    (coefficientOrdinaryScalarAdjunction l E W (n+1)).unit.app (P.obj.X i) ≫
      ((e (n+1)).inv ≫ I.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom)
  exact unit_square (M.unit P i) (limit.π I (op (n+1))) (limit.π I (op n))
    (e (n+1)) (e n) _ _ _ _ (ha (n+1)) (ha n) (finite_unit_step l E W P.obj n i)
    (limit.w I (homOfLE (Nat.le_succ n)).op)

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem reduction_section_step
    (S : CoefficientDerivedSystemReduction l E W)
    (M : ReductionRepresentatives l E W S)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) (k : ℤ)
    (U : W.ProEtᵒᵖ)
    (x : ((M.complexes.obj P).X k).val.obj (op (n + 1, U.unop))) :
    (((M.evaluation n).hom.app P).f k).val.app U
      (coefficientEvaluationSection l E W ((M.complexes.obj P).X k) n U
        (((M.complexes.obj P).X k).val.presheaf.map
          (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)) =
    (((unrestrictedIntegralTransition l E W n).app P.obj).f k).val.app U
      ((((M.evaluation (n+1)).hom.app P).f k).val.app U
        (coefficientEvaluationSection l E W ((M.complexes.obj P).X k) (n+1) U x)) := by
  let C := M.complexes.obj P
  have hh := congrArg (fun z ↦ (z.f k).val.app U
    (integralComparisonRestrictedSection l E W (C.X k) (n+1) U x))
      (reduction_step l E W S M P n)
  have hs := restricted_transition_section l E W (C.X k)
    (Nat.le_succ n) U x
  have hem := restrictionEvaluation_section l E W (C.X k) (n+1) U x
  have hen := restrictionEvaluation_section l E W (C.X k) n U
    ((C.X k).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)
  change (((M.evaluation n).hom.app P).f k).val.app U
      ((((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (C.X k)).val.app U)
        (((((coefficientSequenceRestriction l E W).obj (C.X k)).map
          (homOfLE (Nat.le_succ n)).op).val.app U)
          (integralComparisonRestrictedSection l E W (C.X k) (n+1) U x))) =
    (((unrestrictedIntegralTransition l E W n).app P.obj).f k).val.app U
      ((((M.evaluation (n+1)).hom.app P).f k).val.app U
        ((((eqToIso (coefficientSequenceRestriction_evaluation l E W (n+1))).hom.app
          (C.X k)).val.app U)
          (integralComparisonRestrictedSection l E W (C.X k) (n+1) U x))) at hh
  -- Compose section equalities without rewriting inside the full complex comparison.
  have hleft := congrArg (fun z ↦ (((M.evaluation n).hom.app P).f k).val.app U z) hen
  have hstep := congrArg (fun z ↦ (((M.evaluation n).hom.app P).f k).val.app U
    ((((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (C.X k)).val.app U) z)) hs
  have hright := congrArg (fun z ↦
    (((unrestrictedIntegralTransition l E W n).app P.obj).f k).val.app U
      ((((M.evaluation (n+1)).hom.app P).f k).val.app U z)) hem
  exact hleft.symm.trans (hstep.symm.trans (hh.trans hright))

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem ab_eqToHom_surjective {A B : AddCommGrpCat.{v}} (h : A = B) :
    Function.Surjective (eqToHom h) := by
  subst B
  exact fun x ↦ ⟨x, rfl⟩

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem evaluationSection_surjective
    (C : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective (coefficientEvaluationSection l E W C n U) :=
  ab_eqToHom_surjective (coefficientSequenceEvaluationAb_eq l E W C n U).symm

attribute [local semireducible] coefficientTotalTensor

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem module_unit_section
    {B : Type c} [Category.{d} B] {J : GrothendieckTopology B}
    [HasWeakSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J RingCat.{r}) (M : PresheafOfModules.{r} R.obj)
    (U : Bᵒᵖ) (x : M.obj U) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M).app U) x =
      (toSheafify J M.presheaf).app U x := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app (𝟙 R.obj) M) U) x

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem finite_coefficient_generator (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ)
    (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :
    coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P)
      ((unrestrictedIntegralFiniteComplex l E W n).obj Q) p q (p + q) rfl U x y =
    integralOperationsTotalTensorSection l E W n P Q p q U x y := by
  unfold coefficientTensorGenerator integralOperationsTotalTensorSection
    integralOperationsTensorSection
  erw [PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  erw [module_unit_section]
  rfl

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem finiteTensorBridge_hom
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (finiteTensorBridge l E W n P Q).hom = 𝟙 _ := by
  unfold finiteTensorBridge
  change ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
    ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).map (𝟙 _)) = 𝟙 _
  simp only [CategoryTheory.Functor.map_id]

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem tensorLevel_generator
    (S : CoefficientDerivedSystemReduction l E W)
    (M : ReductionRepresentatives l E W S)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ)
    (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
    (x : ((M.complexes.obj P).X p).val.obj (op (n, U.unop)))
    (y : ((M.complexes.obj Q).X q).val.obj (op (n, U.unop))) :
    let C := M.complexes.obj P
    let D := M.complexes.obj Q
    ((tensorLevel l E W S M P Q n).hom.f k).val.app U
      (integralComparisonRestrictedSection l E W
        (((coefficientTotalTensor.{u, t+1, t} (coefficientSequenceTopology
          (Scheme.ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)).obj
          (C,D)).X k) n U
        (coefficientTensorGenerator.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) C D p q k h
          (op (n, U.unop)) x y)) =
      coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        ((unrestrictedIntegralFiniteComplex l E W n).obj P.obj)
        ((unrestrictedIntegralFiniteComplex l E W n).obj Q.obj) p q k h U
        ((((M.evaluation n).hom.app P).f p).val.app U
          (coefficientEvaluationSection l E W (C.X p) n U x))
        ((((M.evaluation n).hom.app Q).f q).val.app U
          (coefficientEvaluationSection l E W (D.X q) n U y)) := by
  dsimp only
  let C := M.complexes.obj P
  let D := M.complexes.obj Q
  let B := coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let f := B.map (Prod.mkHom ((M.evaluation n).hom.app P) ((M.evaluation n).hom.app Q))
  have hr := restrictionEvaluation_section l E W
    (((coefficientTotalTensor.{u, t+1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (C,D)).X k) n U
    (coefficientTensorGenerator.{u, t+1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) C D p q k h (op (n, U.unop)) x y)
  have hk := (coefficientEvaluationTensorIso_exists l E W n C D).choose_spec.1
    p q k h U x y
  have ht := CategoryTheory.ScalarHomTensor.tensor_generator_map.{t+1, t, u}
    ((M.evaluation n).hom.app P) ((M.evaluation n).hom.app Q) p q k h U
    (coefficientEvaluationSection l E W (C.X p) n U x)
    (coefficientEvaluationSection l E W (D.X q) n U y)
  unfold tensorLevel
  simp only [Iso.trans_hom, finiteTensorBridge_hom,
    Functor.mapIso_hom, Functor.map_comp]
  change (f.f k).val.app U
    (((coefficientEvaluationTensorIso l E W n C D).hom.f k).val.app U
      ((((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        _).val.app U) _)) = _
  have hr' := congrArg (fun z ↦ (f.f k).val.app U
    ((((coefficientEvaluationTensorIso_exists l E W n C D).choose).hom.f k).val.app U z)) hr
  have hh := hr'.trans ((congrArg (fun z ↦ (f.f k).val.app U z) hk).trans ht)
  simp only [C, D, coefficientEvaluationTensorIso, coefficientUniqueComparisonChoice,
    unrestrictedIntegralFiniteComplex,
    unrestrictedIntegralReductionFunctor, scalarReductionExtension,
    integralCoefficientCommRingSheaf, Functor.comp_obj, ObjectProperty.ι_obj] at hh ⊢
  convert hh using 1

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem tensorLevel_naturality
    (S : CoefficientDerivedSystemReduction l E W)
    (M : ReductionRepresentatives l E W S) (n : ℕ)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory ×
      (integralOperationsGoodComplex l E W).FullSubcategory) (f : P ⟶ Q) :
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((restrictComplex l E W).map
        ((coefficientTotalTensor.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).map
            ((M.complexes.prod M.complexes).map f)))).app (op n) ≫
      (tensorLevel l E W S M Q.1 Q.2 n).hom =
    (tensorLevel l E W S M P.1 P.2 n).hom ≫
      ((integralOperationsTensorTowerFunctor l E W).map
        (Prod.mkHom f.1.hom f.2.hom)).app (op n) := by
  obtain ⟨b, hb⟩ := coefficientNormalizedEvaluationTensorChain l E W n
  let G := integralOperationsGoodComplex l E W
  let T := coefficientTotalTensor.{u, t+1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
  let V := coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let R := (scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)
  let a := NatIso.mapHomologicalComplex
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)
  have hu : unrestrictedIntegralReductionFunctor l E W n =
      scalarReductionExtension l E W n := by
    unfold unrestrictedIntegralReductionFunctor
    rfl
  let e := NatIso.mapHomologicalComplex (eqToIso hu) (.up ℤ)
  let d := Functor.isoWhiskerRight (Functor.isoWhiskerRight
    (NatIso.prod e.symm e.symm) V) R
  let c₁ := Functor.isoWhiskerLeft (M.complexes.prod M.complexes ⋙ T) a
  let c₂ := Functor.isoWhiskerLeft (M.complexes.prod M.complexes)
    (Functor.isoWhiskerRight b R)
  let c₃ := Functor.isoWhiskerRight (Functor.isoWhiskerRight
    (NatIso.prod (M.evaluation n) (M.evaluation n)) V) R
  let c₄ := Functor.isoWhiskerLeft (G.ι.prod G.ι) d
  let c := c₁ ≪≫ c₂ ≪≫ c₃ ≪≫ c₄
  have hc (X : G.FullSubcategory × G.FullSubcategory) :
      c.hom.app X = (tensorLevel l E W S M X.1 X.2 n).hom := by
    have h₁ : c₁.app X = restrictEvaluation l E W
        (T.obj (M.complexes.obj X.1, M.complexes.obj X.2)) n := by
      rfl
    have h₂ : c₂.app X = R.mapIso
        (coefficientEvaluationTensorIso l E W n
          (M.complexes.obj X.1) (M.complexes.obj X.2)) := by
      change R.mapIso (b.app (M.complexes.obj X.1, M.complexes.obj X.2)) = _
      rw [hb]
    have h₃ : c₃.app X = R.mapIso (V.mapIso
        (((M.evaluation n).app X.1).prod ((M.evaluation n).app X.2))) := by
      rfl
    have h₄ : c₄.app X = finiteTensorBridge l E W n X.1.obj X.2.obj := by
      rfl
    have hcx : c.app X = tensorLevel l E W S M X.1 X.2 n := by
      change c₁.app X ≪≫ c₂.app X ≪≫ c₃.app X ≪≫ c₄.app X = _
      rw [h₁, h₂, h₃, h₄]
      simp only [tensorLevel, CategoryTheory.Functor.mapIso_trans, Iso.trans_assoc]
      rfl
    exact congrArg Iso.hom hcx
  have hh := c.hom.naturality f
  rw [hc P, hc Q] at hh
  exact hh

private theorem cochainIso_inv_section
    {A : Type c} [Category.{d} A] {J : GrothendieckTopology A} {R : Sheaf J RingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r} R) ℤ} (e : P ≅ Q) (k : ℤ) (U : Aᵒᵖ)
    (x : (P.X k).val.obj U) (y : (Q.X k).val.obj U)
    (h : (e.hom.f k).val.app U x = y) : (e.inv.f k).val.app U y = x :=
  (congrArg (fun z ↦ (e.inv.f k).val.app U z) h).symm.trans
    (congrArg (fun z : P ⟶ P ↦ (z.f k).val.app U x) e.hom_inv_id)

-- Normalize the coefficient functor and complex instances within this declaration.
private theorem tensorLevel_transition
    (S : CoefficientDerivedSystemReduction l E W)
    (M : ReductionRepresentatives l E W S)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ) :
    ((restrictComplex l E W).obj
      ((coefficientTotalTensor.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
          (M.complexes.obj P, M.complexes.obj Q))).asFunctor.map
            (homOfLE (Nat.le_succ n)).op ≫ (tensorLevel l E W S M P Q n).hom =
      (tensorLevel l E W S M P Q (n + 1)).hom ≫
        ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)).map
          (homOfLE (Nat.le_succ n)).op := by
  let C := M.complexes.obj P
  let D := M.complexes.obj Q
  let T := (coefficientTotalTensor.{u, t+1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (C, D)
  let e (j : ℕ) := tensorLevel l E W S M P Q j
  let πm := (integralOperationsForgetSheaf.{max u (t+1)} (Scheme.ProEt.topology W)).map
    (completedIntegralCommRingProjectionUnrestricted l E W (n + 1))
  let πn := (integralOperationsForgetSheaf.{max u (t+1)} (Scheme.ProEt.topology W)).map
    (completedIntegralCommRingProjectionUnrestricted l E W n)
  let τ := integralCoefficientSheafTransition l E W n
  have hπ : πm ≫ τ = πn := integralProjection_step l E W n
  have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology W) πm.hom :=
    completedProjection_locallySurjective l E W (n + 1)
  have ht : ((integralOperationsTensorTowerFunctor l E W).obj (P.obj,Q.obj)).map
      (homOfLE (Nat.le_succ n)).op =
      (integralOperationsTensorTransition l E W n).app (P.obj,Q.obj) := by
    change ((Functor.ofOpSequence (integralOperationsTensorTransition l E W)).map
      (homOfLE (Nat.le_succ n)).op).app (P.obj,Q.obj) = _
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  symm
  rw [ht]
  apply (e (n + 1)).eq_inv_comp.mp
  apply HomologicalComplex.hom_ext
  intro k
  apply WeilConjectures.restricted_coefficient_total_hom_ext.{t+1, t, u}
    (integralCoefficientCommRingSheaf l E W (n + 1))
    (integralCoefficientCommRingSheaf l E W n) πm πn τ hπ
    ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P.obj)
    ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q.obj)
    (((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).obj
        ((unrestrictedIntegralFiniteComplex l E W n).obj P.obj,
          (unrestrictedIntegralFiniteComplex l E W n).obj Q.obj)).X k) k
  intro p q hpq U x y
  subst k
  obtain ⟨x0, hx0⟩ := evaluationSection_surjective l E W (C.X p) (n + 1) U
    ((((M.evaluation (n+1)).inv.app P).f p).val.app U x)
  obtain ⟨y0, hy0⟩ := evaluationSection_surjective l E W (D.X q) (n + 1) U
    ((((M.evaluation (n+1)).inv.app Q).f q).val.app U y)
  have hx := cochainIso_inv_section
    ((M.evaluation (n+1)).app P).symm p U x _ hx0.symm
  have hy := cochainIso_inv_section
    ((M.evaluation (n+1)).app Q).symm q U y _ hy0.symm
  have hg := tensorLevel_generator l E W S M P Q (n + 1) p q (p + q) rfl U x0 y0
  dsimp only at hg
  erw [hx, hy] at hg
  have hi := cochainIso_inv_section (e (n + 1)) (p + q) U _ _ hg
  have hs :
      ((((((restrictComplex l E W).obj T).asFunctor).map
        (homOfLE (Nat.le_succ n)).op).f (p + q)).val.app U)
        (integralComparisonRestrictedSection l E W (T.X (p + q)) (n + 1) U
          (coefficientTensorGenerator.{u, t+1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) C D p q (p + q) rfl
            (op (n + 1, U.unop)) x0 y0)) =
      integralComparisonRestrictedSection l E W (T.X (p + q)) n U
        (coefficientTensorGenerator.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) C D p q (p + q) rfl
          (op (n, U.unop))
          ((C.X p).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x0)
          ((D.X q).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op y0)) := by
    change (((coefficientSequenceRestriction l E W).obj (T.X (p + q))).map
      (homOfLE (Nat.le_succ n)).op).val.app U _ = _
    have hs0 := restricted_transition_section l E W (T.X (p + q)) (Nat.le_succ n) U
      (coefficientTensorGenerator.{u, t+1, t}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) C D p q (p + q) rfl
        (op (n + 1, U.unop)) x0 y0)
    have hsg := generator_presheaf_restrict.{t+1, t, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) C D p q (p + q) rfl
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x0 y0
    exact hs0.trans (congrArg (fun z ↦
      integralComparisonRestrictedSection l E W (T.X (p + q)) n U z) hsg)
  change (((integralOperationsTensorTransition l E W n).app (P.obj,Q.obj)).f (p + q)).val.app U
      (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W (n + 1))
        ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P.obj)
        ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q.obj)
        p q (p + q) rfl U x y) =
    (((e n).hom.f (p + q)).val.app U)
      (((((((restrictComplex l E W).obj T).asFunctor).map
        (homOfLE (Nat.le_succ n)).op).f (p + q)).val.app U)
          ((((e (n + 1)).inv.f (p + q)).val.app U)
            (coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
              (integralCoefficientCommRingSheaf l E W (n + 1))
              ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P.obj)
              ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q.obj)
              p q (p + q) rfl U x y)))
  have htrans := (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec
    P.obj Q.obj p q U x y
  have hm := finite_coefficient_generator l E W P.obj Q.obj (n + 1) p q U x y
  have hn := finite_coefficient_generator l E W P.obj Q.obj n p q U
    ((((unrestrictedIntegralTransition l E W n).app P.obj).f p).val.app U x)
    ((((unrestrictedIntegralTransition l E W n).app Q.obj).f q).val.app U y)
  have htensor := (congrArg (fun z ↦
    (((integralOperationsTensorTransition l E W n).app (P.obj,Q.obj)).f (p + q)).val.app U z)
    hm).trans (htrans.trans hn.symm)
  have hlevel := tensorLevel_generator l E W S M P Q n p q (p + q) rfl U
    ((C.X p).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x0)
    ((D.X q).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op y0)
  dsimp only at hlevel
  have hix := (reduction_section_step l E W S M P n p U x0).trans
    (congrArg (fun z ↦ (((unrestrictedIntegralTransition l E W n).app P.obj).f p).val.app U z) hx)
  have hiy := (reduction_section_step l E W S M Q n q U y0).trans
    (congrArg (fun z ↦ (((unrestrictedIntegralTransition l E W n).app Q.obj).f q).val.app U z) hy)
  have hxy := congrArg₂ (fun x' y' ↦
    coefficientTensorGenerator.{u, t+1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P.obj)
      ((unrestrictedIntegralFiniteComplex l E W n).obj Q.obj) p q (p + q) rfl U x' y') hix hiy
  have hsource := (congrArg (fun z ↦
    ((e n).hom.f (p + q)).val.app U
      ((((((restrictComplex l E W).obj T).asFunctor).map
        (homOfLE (Nat.le_succ n)).op).f (p + q)).val.app U z)) hi).trans
    ((congrArg (fun z ↦ ((e n).hom.f (p + q)).val.app U z) hs).trans
      (hlevel.trans hxy))
  exact htensor.trans hsource.symm

-- Normalize the coefficient functor and complex instances within this declaration.
/-- Strict tensor evaluation assembles to an isomorphism of whole towers, naturally
on the product of good categories.
Source: Stacks 07A4 and 0941; finite tensor construction in step 1 of
lem-pur-primitive-counit-tensor-realization.
(blueprint: stage3-v3-primitive-tensor-strict-tower-comparison).

Proof: at level n compose restriction/evaluation, the ordinary total tensor
evaluation isomorphism, the tensor of the two evaluation comparisons, and the
finiteTensorBridge. These are all isomorphisms. The normalized ordinary units,
their limit-cone equation and the finite scalar-unit formula identify both routes
around each quotient transition square.
On a homogeneous tensor they both apply the coefficient quotient and the two
quotient maps to its factors. The ordinary tensor balancing relation, sheafification
and total-summand universal properties give equality of chain maps. Thus the level
isomorphisms assemble by NatIso.ofComponents to a strict tower isomorphism.
Naturality of all four factors gives its naturality for pairs of good chain maps.
The differential uses the same total tensor signs on both routes. Identity
transitions, level zero, zero inputs and the empty site obey the same calculation.
No derived evaluation faithfulness or Roos normalization is used. -/
theorem tensorStrictTowerComparison
    (S : CoefficientDerivedSystemReduction l E W)
    (M : ReductionRepresentatives l E W S) :
    ∃ z : M.complexes.prod M.complexes ⋙
        coefficientTotalTensor.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) ⋙
        restrictComplex l E W ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      ((integralOperationsGoodComplex l E W).ι.prod
        (integralOperationsGoodComplex l E W).ι) ⋙
          integralOperationsTensorTowerFunctor l E W,
      ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (n : ℕ),
        (z.hom.app (P, Q)).app (op n) =
          (restrictEvaluation l E W _ n).hom ≫
            ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
              ((coefficientEvaluationTensorIso l E W n
                (M.complexes.obj P) (M.complexes.obj Q)).hom ≫
                (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
                  (integralCoefficientCommRingSheaf l E W n)).map
                    (Prod.mkHom ((M.evaluation n).hom.app P)
                      ((M.evaluation n).hom.app Q))) ≫
            (finiteTensorBridge l E W n P.obj Q.obj).hom := by
  classical
  let G := integralOperationsGoodComplex l E W
  let B := M.complexes.prod M.complexes ⋙
    coefficientTotalTensor.{u, t+1, t}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) ⋙ restrictComplex l E W
  let T := G.ι.prod G.ι ⋙ integralOperationsTensorTowerFunctor l E W
  let h (P : G.FullSubcategory × G.FullSubcategory) : (B.obj P).asFunctor ⟶ T.obj P :=
    NatTrans.ofOpSequence (fun n ↦ (tensorLevel l E W S M P.1 P.2 n).hom)
      (fun n ↦ tensorLevel_transition l E W S M P.1 P.2 n)
  let z (P : G.FullSubcategory × G.FullSubcategory) : (B.obj P).asFunctor ≅ T.obj P :=
    NatIso.ofComponents (fun n ↦ tensorLevel l E W S M P.1 P.2 n.unop)
      (fun f ↦ (h P).naturality f)
  have hz (P Q : G.FullSubcategory × G.FullSubcategory) (f : P ⟶ Q) :
      (B ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex).map f ≫ (z Q).hom =
        (z P).hom ≫ T.map f := by
    apply NatTrans.ext
    funext n
    exact tensorLevel_naturality l E W S M n.unop P Q f
  refine ⟨NatIso.ofComponents z (fun f ↦ hz _ _ f), ?_⟩
  intro P Q n
  change (tensorLevel l E W S M P Q n).hom = _
  simp only [tensorLevel, Iso.trans_hom]
  rfl

end WeilConjectures.PrimitiveCounit

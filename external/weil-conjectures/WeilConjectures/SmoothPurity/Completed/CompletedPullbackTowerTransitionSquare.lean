/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTensorLevel
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality
import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! The adjacent transition square for the normalized coherent tensor tower.

Source: Stacks 0941 and 07A4 (blueprint: lem-pur-completed-pullback-tower-level-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v c d r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.leftAdjoint Functor.mapDerivedCategory coefficientSequenceRestriction
  coefficientSequenceEvaluation coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceTopology coefficientTotalTensor coefficientTensorGenerator
  coefficientEvaluationTensorIso SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted scalarReductionExtension

private theorem nat_eqToIso_section_heq
    {A : Type*} [Category A] {B : Type*} [Category B]
    {J : GrothendieckTopology B} {R : Sheaf J RingCat}
    {F G : A ⥤ SheafOfModules R} (h : F = G)
    (M : A) (V : Bᵒᵖ) (x : (F.obj M).val.obj V) :
    HEq (((eqToIso h).hom.app M).val.app V x) x := by
  cases h
  rfl

private theorem ab_eqToHom_section_heq {A B : AddCommGrpCat.{v}} (h : A = B)
    (x : A) : HEq ((eqToHom h) x) x := by
  cases h
  rfl

private theorem restrictionEvaluation_section (W : Scheme.{u})
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
  exact eq_of_heq (h.trans (hx.trans (ab_eqToHom_section_heq
    (coefficientSequenceEvaluationAb_eq l E W M n U).symm x).symm))

private theorem restricted_extension_hom_ext
    {B : Type c} [Category.{d} B] {J : GrothendieckTopology B}
    {R S T : Sheaf J RingCat.{r}} (φ : R ⟶ S) (ψ : R ⟶ T) (τ : S ⟶ T)
    (hπ : φ ≫ τ = ψ) [Presheaf.IsLocallySurjective J φ.hom]
    {F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S}
    (adj : F ⊣ SheafOfModules.restrictScalars φ)
    (M : SheafOfModules.{r} R) (N : SheafOfModules.{r} T)
    (f g : (SheafOfModules.restrictScalars φ).obj (F.obj M) ⟶
      (SheafOfModules.restrictScalars ψ).obj N)
    (h : adj.unit.app M ≫ f = adj.unit.app M ≫ g) : f = g := by
  let f' := SheafOfModules.IntegralScalarProof.liftMap φ ψ τ hπ _ N f
  let g' := SheafOfModules.IntegralScalarProof.liftMap φ ψ τ hπ _ N g
  have hh : f' = g' := by
    apply (adj.homEquiv M _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext U x
    exact congrArg (fun z ↦ z.val.app U x) h
  ext U x
  exact congrArg (fun z ↦ z.val.app U x) hh

private theorem finite_unit_transition (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (k : ℤ) :
    (pullbackTensorFiniteAdjunction l E W (n + 1)).unit.app (P.X k) ≫
      ((unrestrictedIntegralTransition l E W n).app P).f k =
        (pullbackTensorFiniteAdjunction l E W n).unit.app (P.X k) := by
  ext U x
  have hm := (scalarReductionExtension_adjunction l E W (n + 1)).choose_spec (P.X k) U x
  have hn := (scalarReductionExtension_adjunction l E W n).choose_spec (P.X k) U x
  change (((unrestrictedIntegralTransition l E W n).app P).f k).val.app U
    (((pullbackTensorFiniteAdjunction l E W (n + 1)).unit.app (P.X k)).val.app U x) = _
  change ((pullbackTensorFiniteAdjunction l E W (n + 1)).unit.app (P.X k)).val.app U x =
    unrestrictedIntegralTensorSection l E W (n + 1) (P.X k) U 1 x at hm
  change ((pullbackTensorFiniteAdjunction l E W n).unit.app (P.X k)).val.app U x =
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

private theorem cone_unit_square {A : Type*} [Category A]
    {M L Bm Bn Em En Fm Fn : A}
    (η : M ⟶ L) (πm : L ⟶ Bm) (πn : L ⟶ Bn)
    (em : Bm ≅ Em) (en : Bn ≅ En) (am : Fm ⟶ Em) (an : Fn ⟶ En)
    (um : M ⟶ Fm) (un : M ⟶ Fn) (s : Bm ⟶ Bn) (t : Fm ⟶ Fn)
    (ha : um ≫ am = η ≫ πm ≫ em.hom) (hb : un ≫ an = η ≫ πn ≫ en.hom)
    (hu : um ≫ t = un) (hw : πm ≫ s = πn) :
    um ≫ (am ≫ em.inv ≫ s ≫ en.hom) = um ≫ (t ≫ an) := by
  calc
    _ = (um ≫ am) ≫ em.inv ≫ s ≫ en.hom := by simp only [Category.assoc]
    _ = η ≫ πn ≫ en.hom := by
      rw [ha]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ← hw]
    _ = um ≫ (t ≫ an) := by rw [← hb, ← hu, Category.assoc]

private theorem iso_transition_inverse {A : Type*} [Category A]
    {X Y X' Y' : A} (a : X ≅ Y) (b : X' ≅ Y') (s : Y ⟶ Y') (t : X ⟶ X')
    (h : a.hom ≫ s = t ≫ b.hom) : s ≫ b.inv = a.inv ≫ t := by
  calc
    _ = a.inv ≫ (a.hom ≫ s) ≫ b.inv := by simp
    _ = a.inv ≫ (t ≫ b.hom) ≫ b.inv := by rw [h]
    _ = a.inv ≫ t := by simp

private theorem reductionEvaluation_transition (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let C := ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P
    let a (j : ℕ) := ((scalarReductionRestriction l E W j).mapHomologicalComplex (.up ℤ)).mapIso
      ((pullbackTensorReductionEvaluationComplex l E W j).app P)
    (a (n + 1)).hom ≫ (pullbackTensorRestrictedLevel l E W C (n + 1)).inv ≫
      (pullbackTensorRestrictedTower l E W C).map (homOfLE (Nat.le_succ n)).op ≫
      (pullbackTensorRestrictedLevel l E W C n).hom =
    (unrestrictedIntegralTransition l E W n).app P ≫ (a n).hom := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro k
  let πm := (integralOperationsForgetSheaf.{u + 1} (ProEt.topology W)).map
    (completedIntegralCommRingProjectionUnrestricted l E W (n + 1))
  let πn := (integralOperationsForgetSheaf.{u + 1} (ProEt.topology W)).map
    (completedIntegralCommRingProjectionUnrestricted l E W n)
  let τ := integralCoefficientSheafTransition l E W n
  have hπ : πm ≫ τ = πn := integralProjection_step l E W n
  have : Presheaf.IsLocallySurjective (ProEt.topology W) πm.hom :=
    completedProjection_locallySurjective l E W (n + 1)
  apply restricted_extension_hom_ext πm πn τ hπ
    (pullbackTensorFiniteAdjunction l E W (n + 1)) (P.X k)
    ((coefficientSequenceEvaluation l E W n).obj
      ((pullbackTensorOrdinaryReduction l E W).obj (P.X k)))
  have ha (j : ℕ) :=
    (pullbackTensorReductionEvaluation_existsUnique l E W j).exists.choose_spec (P.X k)
  have ha' (j : ℕ) :
      (pullbackTensorFiniteAdjunction l E W j).unit.app (P.X k) ≫
        (scalarReductionRestriction l E W j).map
          ((pullbackTensorReductionEvaluation l E W j).hom.app (P.X k)) =
      (pullbackTensorOrdinaryAdjunction l E W).unit.app (P.X k) ≫
        limit.π ((coefficientSequenceRestriction l E W).obj
          ((pullbackTensorOrdinaryReduction l E W).obj (P.X k))) (op j) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W j)).hom.app
          ((pullbackTensorOrdinaryReduction l E W).obj (P.X k)) := by
    exact ((pullbackTensorFiniteAdjunction l E W j).homEquiv_unit _ _ _).symm.trans (ha j)
  change _ ≫ ((scalarReductionRestriction l E W (n + 1)).map
      ((pullbackTensorReductionEvaluation l E W (n + 1)).hom.app (P.X k)) ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E W (n + 1))).inv.app _ ≫
    (((coefficientSequenceRestriction l E W).obj
      ((pullbackTensorOrdinaryReduction l E W).obj (P.X k))).map
        (homOfLE (Nat.le_succ n)).op) ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app _) =
    _ ≫ (((unrestrictedIntegralTransition l E W n).app P).f k ≫
      (scalarReductionRestriction l E W n).map
        ((pullbackTensorReductionEvaluation l E W n).hom.app (P.X k)))
  exact cone_unit_square
    ((pullbackTensorOrdinaryAdjunction l E W).unit.app (P.X k))
    (limit.π _ (op (n + 1))) (limit.π _ (op n))
    ((eqToIso (coefficientSequenceRestriction_evaluation l E W (n + 1))).app _)
    ((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).app _)
    ((scalarReductionRestriction l E W (n + 1)).map
      ((pullbackTensorReductionEvaluation l E W (n + 1)).hom.app (P.X k)))
    ((scalarReductionRestriction l E W n).map
      ((pullbackTensorReductionEvaluation l E W n).hom.app (P.X k)))
    ((pullbackTensorFiniteAdjunction l E W (n + 1)).unit.app (P.X k))
    ((pullbackTensorFiniteAdjunction l E W n).unit.app (P.X k)) _ _
    (ha' (n + 1)) (ha' n) (finite_unit_transition l E W P n k) (limit.w _ _)

private theorem module_map_presheaf_heq {B : Type c} [Category.{d} B]
    {R : Bᵒᵖ ⥤ RingCat.{r}} (M : PresheafOfModules.{r} R)
    {V U : Bᵒᵖ} (f : V ⟶ U) :
    HEq (fun x : M.obj V ↦ M.map f x)
      (fun x : M.presheaf.obj V ↦ M.presheaf.map f x) := by
  rfl

private theorem presheaf_map_apply {B : Type c} [Category.{d} B]
    {R : Bᵒᵖ ⥤ RingCat.{r}} (M : PresheafOfModules.{r} R)
    {V U : Bᵒᵖ} (f : V ⟶ U) (x : M.obj V) :
    M.presheaf.map f x = M.map f x := rfl

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

private theorem function_heq_apply {A A' : Type v} {B B' : Type r}
    (ha : A = A') (hb : B = B') {f : A → B} {g : A' → B'} (hf : HEq f g)
    {x : A} {y : A'} (hx : HEq x y) : HEq (f x) (g y) := by
  subst A'
  subst B'
  cases hf
  cases hx
  rfl

private theorem restricted_transition_section (W : Scheme.{u})
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

attribute [local semireducible] coefficientTotalTensor

private theorem restricted_coefficient_total_hom_ext
    {B : Type c} [Category.{d} B] {J : GrothendieckTopology B}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c d r} RingCat.{max c d r})]
    [HasSheafify J AddCommGrpCat.{max c d r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d r}]
    {R₀ : Sheaf J RingCat.{max c d r}} (S T : Sheaf J CommRingCat.{max c d r})
    (φ : R₀ ⟶ (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    (ψ : R₀ ⟶ (sheafCompose J (forget₂ CommRingCat RingCat)).obj T)
    (τ : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
      (sheafCompose J (forget₂ CommRingCat RingCat)).obj T)
    (hπ : φ ≫ τ = ψ) [Presheaf.IsLocallySurjective J φ.hom]
    (P Q : CochainComplex (SheafOfModules.{max c d r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ)
    (Z : SheafOfModules.{max c d r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T)) (k : ℤ)
    (a b : (SheafOfModules.restrictScalars φ).obj
        (((coefficientTotalTensor.{r, c, d} J S).obj (P, Q)).X k) ⟶
      (SheafOfModules.restrictScalars ψ).obj Z)
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (U : Bᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      a.val.app U (coefficientTensorGenerator.{r, c, d} J S P Q p q k hpq U x y) =
        b.val.app U (coefficientTensorGenerator.{r, c, d} J S P Q p q k hpq U x y)) :
    a = b := by
  let lift := SheafOfModules.IntegralScalarProof.liftMap φ ψ τ hπ
    (((coefficientTotalTensor.{r, c, d} J S).obj (P, Q)).X k) Z
  have hh : lift a = lift b := by
    apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{c, d, r} P Q k _
    intro p q hpq U x y
    exact h p q hpq U x y
  ext U x
  exact congrArg (fun z ↦ z.val.app U x) hh

section GeneratorNormalization
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
open MonoidalCategory
open scoped TensorProduct

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

private theorem finite_coefficient_generator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ)
    (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P)
      ((unrestrictedIntegralFiniteComplex l E W n).obj Q) p q (p + q) rfl U x y =
    integralOperationsTotalTensorSection l E W n P Q p q U x y := by
  unfold coefficientTensorGenerator integralOperationsTotalTensorSection
    integralOperationsTensorSection
  erw [PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  erw [module_unit_section]
  rfl

end GeneratorNormalization

private theorem tensorLevel_generator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ)
    (p q k : ℤ) (h : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (((pullbackTensorOrdinaryReduction l E W).obj (P.X p)).val.obj
      (op (n, U.unop))))
    (y : (((pullbackTensorOrdinaryReduction l E W).obj (Q.X q)).val.obj
      (op (n, U.unop)))) :
    let C := ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P
    let D := ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q
    ((pullbackTensorTensorTowerLevel l E W P Q n).hom.f k).val.app U
      (integralComparisonRestrictedSection l E W
        (((coefficientTotalTensor.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (C, D)).X k) n U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) C D p q k h (op (n, U.unop)) x y)) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        ((unrestrictedIntegralFiniteComplex l E W n).obj P)
        ((unrestrictedIntegralFiniteComplex l E W n).obj Q) p q k h U
          ((((pullbackTensorReductionEvaluationComplex l E W n).inv.app P).f p).val.app U
            (coefficientEvaluationSection l E W (C.X p) n U x))
          ((((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q).f q).val.app U
            (coefficientEvaluationSection l E W (D.X q) n U y)) := by
  dsimp only
  let C := ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P
  let D := ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q
  let B := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let f := B.map (Prod.mkHom
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q))
  have hr := restrictionEvaluation_section l E W
    (((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (C, D)).X k) n U
    (coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) C D p q k h (op (n, U.unop)) x y)
  have hk := pullbackTensorEvaluationTensor_generator_cast l E W n C D p q k h U x y
  have ht := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q) p q k h U
    (coefficientEvaluationSection l E W (C.X p) n U x)
    (coefficientEvaluationSection l E W (D.X q) n U y)
  unfold pullbackTensorTensorTowerLevel
  change (f.f k).val.app U
    (((coefficientEvaluationTensorIso l E W n C D).hom.f k).val.app U
      ((((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        _).val.app U) _)) = _
  exact (congrArg (fun z ↦ (f.f k).val.app U
    (((coefficientEvaluationTensorIso l E W n C D).hom.f k).val.app U z)) hr).trans
    ((congrArg (fun z ↦ (f.f k).val.app U z) hk).trans ht)

private theorem reductionInverse_transition_section (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (k : ℤ)
    (U : W.ProEtᵒᵖ)
    (x : ((pullbackTensorOrdinaryReduction l E W).obj (P.X k)).val.obj
      (op (n + 1, U.unop))) :
    let C := ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P
    (((pullbackTensorReductionEvaluationComplex l E W n).inv.app P).f k).val.app U
      (coefficientEvaluationSection l E W (C.X k) n U
        ((C.X k).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)) =
    (((unrestrictedIntegralTransition l E W n).app P).f k).val.app U
      ((((pullbackTensorReductionEvaluationComplex l E W (n + 1)).inv.app P).f k).val.app U
        (coefficientEvaluationSection l E W (C.X k) (n + 1) U x)) := by
  let C := ((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P
  let a (j : ℕ) := ((scalarReductionRestriction l E W j).mapHomologicalComplex (.up ℤ)).mapIso
    ((pullbackTensorReductionEvaluationComplex l E W j).app P)
  have h := iso_transition_inverse (a (n + 1)) (a n) _ _
    (reductionEvaluation_transition l E W P n)
  have hh := congrArg (fun z ↦ (z.f k).val.app U
    (coefficientEvaluationSection l E W (C.X k) (n + 1) U x)) h
  have hi := cochainIso_inv_section (pullbackTensorRestrictedLevel l E W C (n + 1)) k U _ _
    (restrictionEvaluation_section l E W (C.X k) (n + 1) U x)
  have hs := restricted_transition_section l E W (C.X k) (Nat.le_succ n) U x
  have he := restrictionEvaluation_section l E W (C.X k) n U
    ((C.X k).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x)
  have hc := (congrArg (fun z ↦
    (((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (C.X k)).val.app U)
      (((((coefficientSequenceRestriction l E W).obj (C.X k)).map
        (homOfLE (Nat.le_succ n)).op).val.app U) z)) hi).trans
    ((congrArg (fun z ↦
      (((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (C.X k)).val.app U) z) hs).trans he)
  change (((a n).inv.f k).val.app U)
      ((((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (C.X k)).val.app U)
        (((((coefficientSequenceRestriction l E W).obj (C.X k)).map
          (homOfLE (Nat.le_succ n)).op).val.app U)
            ((((pullbackTensorRestrictedLevel l E W C (n + 1)).inv.f k).val.app U) _))) =
    (((unrestrictedIntegralTransition l E W n).app P).f k).val.app U
      ((((a (n + 1)).inv.f k).val.app U) _) at hh
  exact (congrArg (fun z ↦ (((a n).inv.f k).val.app U) z) hc).symm.trans hh

/-- Consecutive components of the normalized tensor tower comparison commute with the
actual quotient transitions `n + 1 → n`.
Source: Stacks 0941 and 07A4 (blueprint: lem-pur-completed-pullback-tower-level-transition).
Proof: first compare reduction evaluation with the quotient transition. The finite
scalar-extension unit sends x to 1 tensor x, so its consecutive transition is the
next unit. Local surjectivity of the completion projection lets us regard each
completed-linear map between finite modules as a finite-linear map. The scalar
adjunction therefore detects equality on the unit. The specified transpose of
reduction evaluation and the limit-cone identity prove the required square,
degreewise; composing with the inverse isomorphisms proves the inverse square.

Next evaluate the three defining factors of the level comparison on homogeneous
pure tensors. The restriction/evaluation isomorphism identifies the section types,
the normalized tensor-evaluation comparison evaluates each factor, and the total
tensor map applies inverse reduction evaluation to each factor. Naturality of the
sheafification unit and of the direct-sum inclusions shows that a horizontal
restriction of a tensor generator restricts its two factors.

Finally precompose by the inverse level comparison at n+1. Local surjectivity of
the completion projection reduces equality to finite homogeneous tensor generators.
Every evaluated section has a sequence-section preimage. On their generators the
source transition restricts the two sequence sections; the inverse reduction
square identifies these with their finite quotient transitions. The prescribed
target tensor transition applies exactly these two transitions, proving equality
on every summand and degree, hence equality of cochain maps. -/
theorem pullbackTensorTensorTowerLevel_transition
    (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (pullbackTensorTensorTowerLevel l E W P Q (n + 1)).hom ≫
        ((integralOperationsTensorTowerFunctor l E W).obj (P,Q)).map
          (homOfLE (Nat.le_succ n)).op =
      (pullbackTensorRestrictedTower l E W
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj
          ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)))
        ).map (homOfLE (Nat.le_succ n)).op ≫
      (pullbackTensorTensorTowerLevel l E W P Q n).hom := by
  let R := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let C := R.obj P
  let D := R.obj Q
  let T := (coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)).obj (C, D)
  let e (j : ℕ) := pullbackTensorTensorTowerLevel l E W P Q j
  let πm := (integralOperationsForgetSheaf.{u + 1} (ProEt.topology W)).map
    (completedIntegralCommRingProjectionUnrestricted l E W (n + 1))
  let πn := (integralOperationsForgetSheaf.{u + 1} (ProEt.topology W)).map
    (completedIntegralCommRingProjectionUnrestricted l E W n)
  let τ := integralCoefficientSheafTransition l E W n
  have hπ : πm ≫ τ = πn := integralProjection_step l E W n
  have : Presheaf.IsLocallySurjective (ProEt.topology W) πm.hom :=
    completedProjection_locallySurjective l E W (n + 1)
  have ht : ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).map
      (homOfLE (Nat.le_succ n)).op =
      (integralOperationsTensorTransition l E W n).app (P, Q) := by
    change ((Functor.ofOpSequence (integralOperationsTensorTransition l E W)).map
      (homOfLE (Nat.le_succ n)).op).app (P, Q) = _
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  rw [ht]
  apply (e (n + 1)).eq_inv_comp.mp
  apply HomologicalComplex.hom_ext
  intro k
  apply restricted_coefficient_total_hom_ext.{u + 1, u, u}
    (integralCoefficientCommRingSheaf l E W (n + 1))
    (integralCoefficientCommRingSheaf l E W n) πm πn τ hπ
    ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P)
    ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q)
    (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).obj
        ((unrestrictedIntegralFiniteComplex l E W n).obj P,
          (unrestrictedIntegralFiniteComplex l E W n).obj Q)).X k) k
  intro p q hpq U x y
  subst k
  obtain ⟨x0, hx0⟩ := evaluationSection_surjective l E W (C.X p) (n + 1) U
    ((((pullbackTensorReductionEvaluationComplex l E W (n + 1)).hom.app P).f p).val.app U x)
  obtain ⟨y0, hy0⟩ := evaluationSection_surjective l E W (D.X q) (n + 1) U
    ((((pullbackTensorReductionEvaluationComplex l E W (n + 1)).hom.app Q).f q).val.app U y)
  have hx := cochainIso_inv_section
    ((pullbackTensorReductionEvaluationComplex l E W (n + 1)).app P) p U x _ hx0.symm
  have hy := cochainIso_inv_section
    ((pullbackTensorReductionEvaluationComplex l E W (n + 1)).app Q) q U y _ hy0.symm
  have hg := tensorLevel_generator l E W P Q (n + 1) p q (p + q) rfl U x0 y0
  dsimp only at hg
  erw [hx, hy] at hg
  have hi := cochainIso_inv_section (e (n + 1)) (p + q) U _ _ hg
  have hs :
      ((((pullbackTensorRestrictedTower l E W T).map
        (homOfLE (Nat.le_succ n)).op).f (p + q)).val.app U)
        (integralComparisonRestrictedSection l E W (T.X (p + q)) (n + 1) U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) C D p q (p + q) rfl
            (op (n + 1, U.unop)) x0 y0)) =
      integralComparisonRestrictedSection l E W (T.X (p + q)) n U
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) C D p q (p + q) rfl
          (op (n, U.unop))
          ((C.X p).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x0)
          ((D.X q).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op y0)) := by
    change (((coefficientSequenceRestriction l E W).obj (T.X (p + q))).map
      (homOfLE (Nat.le_succ n)).op).val.app U _ = _
    have hs0 := restricted_transition_section l E W (T.X (p + q)) (Nat.le_succ n) U
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) C D p q (p + q) rfl
        (op (n + 1, U.unop)) x0 y0)
    have hsg := generator_presheaf_restrict.{u + 1, u, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) C D p q (p + q) rfl
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x0 y0
    exact hs0.trans (congrArg (fun z ↦
      integralComparisonRestrictedSection l E W (T.X (p + q)) n U z) hsg)
  change (((integralOperationsTensorTransition l E W n).app (P, Q)).f (p + q)).val.app U
      (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W (n + 1))
        ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P)
        ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q)
        p q (p + q) rfl U x y) =
    (((e n).hom.f (p + q)).val.app U)
      (((((pullbackTensorRestrictedTower l E W T).map
        (homOfLE (Nat.le_succ n)).op).f (p + q)).val.app U)
          ((((e (n + 1)).inv.f (p + q)).val.app U)
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
              (integralCoefficientCommRingSheaf l E W (n + 1))
              ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj P)
              ((unrestrictedIntegralFiniteComplex l E W (n + 1)).obj Q)
              p q (p + q) rfl U x y)))
  have htrans := (integralOperationsTensorTransition_existsUnique l E W n).exists.choose_spec
    P Q p q U x y
  have hm := finite_coefficient_generator l E W P Q (n + 1) p q U x y
  have hn := finite_coefficient_generator l E W P Q n p q U
    ((((unrestrictedIntegralTransition l E W n).app P).f p).val.app U x)
    ((((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U y)
  have htensor := (congrArg (fun z ↦
    (((integralOperationsTensorTransition l E W n).app (P, Q)).f (p + q)).val.app U z)
    hm).trans (htrans.trans hn.symm)
  have hlevel := tensorLevel_generator l E W P Q n p q (p + q) rfl U
    ((C.X p).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op x0)
    ((D.X q).val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op y0)
  dsimp only at hlevel
  have hix := (reductionInverse_transition_section l E W P n p U x0).trans
    (congrArg (fun z ↦ (((unrestrictedIntegralTransition l E W n).app P).f p).val.app U z) hx)
  have hiy := (reductionInverse_transition_section l E W Q n q U y0).trans
    (congrArg (fun z ↦ (((unrestrictedIntegralTransition l E W n).app Q).f q).val.app U z) hy)
  have hxy := congrArg₂ (fun x' y' ↦
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P)
      ((unrestrictedIntegralFiniteComplex l E W n).obj Q) p q (p + q) rfl U x' y') hix hiy
  have hsource := (congrArg (fun z ↦
    ((e n).hom.f (p + q)).val.app U
      ((((pullbackTensorRestrictedTower l E W T).map
        (homOfLE (Nat.le_succ n)).op).f (p + q)).val.app U z)) hi).trans
    ((congrArg (fun z ↦ ((e n).hom.f (p + q)).val.app U z) hs).trans
      (hlevel.trans hxy))
  exact htensor.trans hsource.symm

end WeilConjectures

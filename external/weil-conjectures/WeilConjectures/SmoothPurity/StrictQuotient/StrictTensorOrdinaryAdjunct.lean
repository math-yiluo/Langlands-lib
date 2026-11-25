/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # Ordinary tensor factorization for strict quotient adjuncts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.moduleAbelian

universe t u c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

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

private theorem presheaf_map_apply {C : Type c} [Category.{v} C]
    {R : Cᵒᵖ ⥤ RingCat.{r}} (M : PresheafOfModules.{r} R)
    {A B : Cᵒᵖ} (f : A ⟶ B) (x : M.obj A) :
    M.presheaf.map f x = M.map f x := rfl

private theorem generator_presheaf_restrict {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P Q : CochainComplex (CategoryTheory.RingedTensorModules.{c, v, r} J R) ℤ)
    (p q k : ℤ) (h : p + q = k) {A B : Cᵒᵖ} (f : A ⟶ B)
    (x : (P.X p).val.obj A) (y : (Q.X q).val.obj A) :
    (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X k).val.presheaf.map f
      (coefficientTensorGenerator.{r, c, v} J R P Q p q k h A x y) =
    coefficientTensorGenerator.{r, c, v} J R P Q p q k h B
      ((P.X p).val.presheaf.map f x) ((Q.X q).val.presheaf.map f y) := by
  simp only [presheaf_map_apply]
  exact CategoryTheory.ringedSiteTensorGenerator_restrict.{c, v, r} J R P Q p q k h f x y

private theorem tensorTransitions {W : Scheme.{t}} (P Q : Complex l E W) :
    TensorTransitions l E P Q := by
  intro m n hmn p q k hpq U x y
  exact generator_presheaf_restrict.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) P Q p q k hpq
    (Prod.mkHom (homOfLE hmn) (𝟙 U)).op x y

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator

private theorem evaluation_generator {W : Scheme.{t}} (P Q : Complex l E W)
    (n : ℕ) (p q k : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop)))
    (y : (Q.X q).val.obj (op (n, U.unop))) :
    ((coefficientEvaluationTensorIso l E W n P Q).hom.f k).val.app U
      (coefficientEvaluationSection l E W _ n U
        (coefficientTensorGenerator.{u, t + 1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) P Q p q k hpq
          (op (n, U.unop)) x y)) =
      coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (level l E P n) (level l E Q n) p q k hpq U
        (coefficientEvaluationSection l E W _ n U x)
        (coefficientEvaluationSection l E W _ n U y) :=
  (coefficientEvaluationTensorIso_exists l E W n P Q).choose_spec.1 p q k hpq U x y

private theorem transport_square {A B A' B' : AddCommGrpCat.{r}}
    (hA : A' = A) (hB : B' = B) {f : A' ⟶ B'} {g : A ⟶ B}
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g) (x : A) :
    f (eqToHom hA.symm x) = eqToHom hB.symm (g x) := by
  subst A
  subst B
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id,
    ConcreteCategory.id_apply] using
    congrArg (fun f ↦ f x) h

private theorem eqToHom_surjective {A B : AddCommGrpCat.{r}} (h : A = B) :
    Function.Surjective (eqToHom h) := by
  subst B
  exact fun x ↦ ⟨x, rfl⟩

private theorem iso_inv_section {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {P Q : CochainComplex (SheafOfModules.{r} R) ℤ} (e : P ≅ Q)
    (k : ℤ) (U : Cᵒᵖ) (x : (P.X k).val.obj U) :
    (e.inv.f k).val.app U ((e.hom.f k).val.app U x) = x :=
  congrArg (fun (f : P ⟶ P) ↦ (f.f k).val.app U x) e.hom_inv_id

private theorem evaluation_section_surjective {W : Scheme.{t}}
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Surjective (coefficientEvaluationSection l E W M n U) :=
  eqToHom_surjective (coefficientSequenceEvaluationAb_eq l E W M n U).symm

private theorem mapped_transition_section {A : Type*} [Category A] [Preadditive A]
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    (Fm : A ⥤ SheafOfModules.{r} R) (Fn : A ⥤ SheafOfModules.{r} S)
    [Fm.Additive] [Fn.Additive] (τ : Fm ⟶ Fn ⋙ SheafOfModules.restrictScalars φ)
    (P : CochainComplex A ℤ) (k : ℤ) (U : Cᵒᵖ)
    {G H : AddCommGrpCat.{r}}
    (ha : (Fm.obj (P.X k)).val.presheaf.obj U = G)
    (hb : (Fn.obj (P.X k)).val.presheaf.obj U = H)
    (g : G ⟶ H)
    (h : eqToHom ha.symm ≫
      (forget₂ (ModuleCat.{r} (R.obj.obj U)) AddCommGrpCat.{r}).map
        ((τ.app (P.X k)).val.app U) ≫ eqToHom hb = g) (x : G) :
    coefficientRestrictionSection φ (Fn.obj (P.X k)) U
      (((((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P).f k).val.app U)
        (eqToHom ha.symm x)) = eqToHom hb.symm (g x) := by
  exact transport_square ha hb h x

private theorem transition_section {W : Scheme.{t}} (P : Complex l E W)
    {m n : ℕ} (hmn : n ≤ m) (k : ℤ) (U : W.ProEtᵒᵖ)
    (x : (P.X k).val.obj (op (m, U.unop))) :
    coefficientRestrictionSection (normalizedDVRQuotient l E W hmn)
      ((level l E P n).X k) U
      ((((transition l E P hmn).f k).val.app U)
        (coefficientEvaluationSection l E W _ m U x)) =
        coefficientEvaluationSection l E W _ n U
          (horizontal l E (P.X k) hmn U.unop x) := by
  have h := (coefficientSequenceTransition_exists l E W hmn).exists.choose_spec (P.X k) U
  exact mapped_transition_section (normalizedDVRQuotient l E W hmn)
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (coefficientSequenceTransition l E W hmn) P k U
    (coefficientSequenceEvaluationAb_eq l E W (P.X k) m U)
    (coefficientSequenceEvaluationAb_eq l E W (P.X k) n U) _ h x

private theorem cochain_adjunct_f {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] {F : A ⥤ B} {R : B ⥤ A}
    [F.Additive] [R.Additive] (a : F ⊣ R)
    {P : CochainComplex A ℤ} {Q : CochainComplex B ℤ}
    (t : P ⟶ (R.mapHomologicalComplex (.up ℤ)).obj Q) (k : ℤ) :
    (((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm t).f k =
      (a.homEquiv _ _).symm (t.f k) := rfl

private theorem scalar_adjunct_on_unit {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    (F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S)
    (a : F ⊣ SheafOfModules.restrictScalars φ)
    {M : SheafOfModules.{r} R} {N : SheafOfModules.{r} S}
    (t : M ⟶ (SheafOfModules.restrictScalars φ).obj N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((a.homEquiv _ _).symm t).val.app U ((a.unit.app M).val.app U x) =
      t.val.app U x := by
  have h := a.homEquiv_unit _ _ ((a.homEquiv _ _).symm t)
  have hh : a.unit.app M ≫ (SheafOfModules.restrictScalars φ).map
      ((a.homEquiv _ _).symm t) = t :=
    h.symm.trans (Equiv.apply_symm_apply _ _)
  exact congrArg (fun f ↦ f.val.app U x) hh

private theorem complex_adjunct_on_unit {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    (F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S) [F.Additive]
    (a : F ⊣ SheafOfModules.restrictScalars φ)
    (j : ∀ (M : SheafOfModules.{r} R) (U : Cᵒᵖ), M.val.obj U → (F.obj M).val.obj U)
    (hj : ∀ M U x, coefficientRestrictionSection φ (F.obj M) U
      ((a.unit.app M).val.app U x) = j M U x)
    {P : CochainComplex (SheafOfModules.{r} R) ℤ}
    {Q : CochainComplex (SheafOfModules.{r} S) ℤ}
    (t : P ⟶ ((SheafOfModules.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj Q)
    (k : ℤ) (U : Cᵒᵖ) (x : (P.X k).val.obj U) :
    ((((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm t).f k).val.app U
      (j (P.X k) U x) =
        coefficientRestrictionSection φ (Q.X k) U ((t.f k).val.app U x) := by
  rw [cochain_adjunct_f]
  exact (congrArg (((a.homEquiv _ _).symm (t.f k)).val.app U)
    (hj (P.X k) U x).symm).trans (scalar_adjunct_on_unit φ F a (t.f k) U x)

private theorem restriction_section_injective {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r}}
    (φ : R ⟶ S) (N : SheafOfModules.{r} S) (U : Cᵒᵖ) :
    Function.Injective (coefficientRestrictionSection φ N U) := fun _ _ h ↦ h

private theorem ordinary_on_unit {W : Scheme.{t}} (P : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (k : ℤ) (U : W.ProEtᵒᵖ) (x : ((level l E P m).X k).val.obj U) :
    ((ordinaryAlpha l E P S D hmn).f k).val.app U
      (coefficientFiniteQuotientUnitSection l E W hmn _ U x) =
        coefficientRestrictionSection (normalizedDVRQuotient l E W hmn)
          ((level l E P n).X k) U (((transition l E P hmn).f k).val.app U x) := by
  exact complex_adjunct_on_unit (normalizedDVRQuotient l E W hmn)
    (coefficientFiniteQuotientExtension l E W hmn) (D.ordinaryAdjunction hmn)
    (coefficientFiniteQuotientUnitSection l E W hmn)
    (D.ordinary_unit hmn) (transition l E P hmn) k U x

private abbrev finiteTensor (W : Scheme.{t}) (n : ℕ) :=
  coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)

private theorem tensor_generators_on_unit {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : (sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R ⟶
      (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)
    (F : CategoryTheory.RingedTensorModules.{c, v, r} J R ⥤
      CategoryTheory.RingedTensorModules.{c, v, r} J S) [F.Additive]
    (a : F ⊣ SheafOfModules.restrictScalars φ)
    (j : ∀ (M : CategoryTheory.RingedTensorModules.{c, v, r} J R) (U : Cᵒᵖ),
      M.val.obj U → (F.obj M).val.obj U)
    (hj : ∀ M U x, coefficientRestrictionSection φ (F.obj M) U
      ((a.unit.app M).val.app U x) = j M U x)
    (P Q : CochainComplex (CategoryTheory.RingedTensorModules.{c, v, r} J R) ℤ)
    (e : (F.mapHomologicalComplex (.up ℤ)).obj ((coefficientTotalTensor.{r, c, v} J R).obj
        (P, Q)) ≅ (coefficientTotalTensor.{r, c, v} J S).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P, (F.mapHomologicalComplex (.up ℤ)).obj Q))
    (he : CoefficientScalarTensorGenerators.{r, c, v} J R S F j P Q e)
    (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (e.hom.f k).val.app U
      (coefficientRestrictionSection φ _ U ((a.unit.app _).val.app U
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq U x y))) =
      coefficientTensorGenerator.{r, c, v} J S
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ((F.mapHomologicalComplex (.up ℤ)).obj Q)
        p q k hpq U (j (P.X p) U x) (j (Q.X q) U y) := by
  exact (congrArg ((e.hom.f k).val.app U)
    (hj (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X k) U
      (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq U x y))).trans
    (he p q k hpq U x y)

private theorem recover_from_inverse {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {P Q : A} {R S T : B} (em : P ≅ Q)
    (e : F.obj Q ≅ R) (en : S ≅ T) (f : R ⟶ T) (z : F.obj P ⟶ S)
    (h : e.hom ≫ f = F.map em.inv ≫ z ≫ en.hom) :
    F.map em.hom ≫ e.hom ≫ f = z ≫ en.hom := by
  rw [h]
  exact (F.mapIso em).hom_inv_id_assoc _

private theorem ordinary_tensor {W : Scheme.{t}} (P Q : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (e : ((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).obj
        ((finiteTensor l E W m).obj (level l E P m, level l E Q m)) ≅
      (finiteTensor l E W n).obj
        (((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).obj
          (level l E P m),
         ((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).obj
          (level l E Q m)))
    (he : CoefficientScalarTensorGenerators.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W m) (integralCoefficientCommRingSheaf l E W n)
      (coefficientFiniteQuotientExtension l E W hmn)
      (hF := coefficientFiniteQuotientExtensionAdditive l E W hmn)
      (coefficientFiniteQuotientUnitSection l E W hmn) (level l E P m) (level l E Q m) e) :
    ((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).map
        (coefficientEvaluationTensorIso l E W m P Q).hom ≫ e.hom ≫
        (finiteTensor l E W n).map
          (Prod.mkHom (ordinaryAlpha l E P S D hmn) (ordinaryAlpha l E Q S D hmn)) =
      ordinaryAlpha l E (total l E P Q) S D hmn ≫
        (coefficientEvaluationTensorIso l E W n P Q).hom := by
  let : (coefficientFiniteQuotientExtension l E W hmn).Additive :=
    coefficientFiniteQuotientExtensionAdditive l E W hmn
  let F := (coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)
  let R := (normalizedDVRModuleRes l E W hmn).mapHomologicalComplex (.up ℤ)
  let a := (D.ordinaryAdjunction hmn).mapHomologicalComplex (.up ℤ)
  let em := coefficientEvaluationTensorIso l E W m P Q
  let en := coefficientEvaluationTensorIso l E W n P Q
  let f := ordinaryAlpha l E P S D hmn
  let g := ordinaryAlpha l E Q S D hmn
  let z := ordinaryAlpha l E (total l E P Q) S D hmn
  have hz : a.homEquiv _ _ z = transition l E (total l E P Q) hmn :=
    (a.homEquiv _ _).apply_symm_apply _
  have hh : e.hom ≫ (finiteTensor l E W n).map (Prod.mkHom f g) =
      F.map em.inv ≫ z ≫ en.hom := by
    apply (a.homEquiv _ _).injective
    conv_rhs =>
      rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right, hz]
    change a.homEquiv _ _ _ = em.inv ≫ transition l E (total l E P Q) hmn ≫ R.map en.hom
    rw [a.homEquiv_unit]
    apply HomologicalComplex.Hom.ext
    funext k
    apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{t + 1, t, u}
      (R := integralCoefficientCommRingSheaf l E W m)
    intro p q hpq U x y
    -- Compare sections after the explicit scalar-restriction transport.
    apply restriction_section_injective (normalizedDVRQuotient l E W hmn)
      (((finiteTensor l E W n).obj (level l E P n, level l E Q n)).X k) U
    revert x y
    refine (evaluation_section_surjective l E (P.X p) m U).forall.mpr ?_
    intro x0
    refine (evaluation_section_surjective l E (Q.X q) m U).forall.mpr ?_
    intro y0
    let x := coefficientEvaluationSection l E W (P.X p) m U x0
    let y := coefficientEvaluationSection l E W (Q.X q) m U y0
    change (((finiteTensor l E W n).map (Prod.mkHom f g)).f k).val.app U
      ((e.hom.f k).val.app U
        (coefficientRestrictionSection (normalizedDVRQuotient l E W hmn) _ U
          (((D.ordinaryAdjunction hmn).unit.app _).val.app U
          (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
            (integralCoefficientCommRingSheaf l E W m)
            (level l E P m) (level l E Q m) p q k hpq U x y)))) = _
    refine (congrArg ((((finiteTensor l E W n).map (Prod.mkHom f g)).f k).val.app U)
      (tensor_generators_on_unit.{t + 1, t, u}
        (R := integralCoefficientCommRingSheaf l E W m)
        (S := integralCoefficientCommRingSheaf l E W n) (normalizedDVRQuotient l E W hmn)
        (coefficientFiniteQuotientExtension l E W hmn) (D.ordinaryAdjunction hmn)
        (coefficientFiniteQuotientUnitSection l E W hmn) (D.ordinary_unit hmn)
        (level l E P m) (level l E Q m) e he p q k hpq U x y)).trans ?_
    refine (CategoryTheory.ScalarHomTensor.tensor_generator_map.{t + 1, t, u}
      (R := integralCoefficientCommRingSheaf l E W n) f g p q k hpq U _ _).trans ?_
    refine (congrArg₂
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (level l E P n) (level l E Q n) p q k hpq U)
      (ordinary_on_unit l E P S D hmn p U x)
      (ordinary_on_unit l E Q S D hmn q U y)).trans ?_
    have hem := evaluation_generator l E P Q m p q k hpq U x0 y0
    have hei : (em.inv.f k).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W m)
          (level l E P m) (level l E Q m) p q k hpq U x y) =
        coefficientEvaluationSection l E W _ m U
          (coefficientTensorGenerator.{u, t + 1, t}
            (coefficientSequenceTopology (Scheme.ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) P Q p q k hpq
            (op (m, U.unop)) x0 y0) := by
      exact (congrArg ((em.inv.f k).val.app U) hem.symm).trans
        (iso_inv_section em k U _)
    change _ = (en.hom.f k).val.app U
      (coefficientRestrictionSection (normalizedDVRQuotient l E W hmn)
        ((level l E (total l E P Q) n).X k) U
        (((transition l E (total l E P Q) hmn).f k).val.app U
          ((em.inv.f k).val.app U _)))
    symm
    refine (congrArg (fun v ↦ (en.hom.f k).val.app U
      (coefficientRestrictionSection (normalizedDVRQuotient l E W hmn)
        ((level l E (total l E P Q) n).X k) U
        (((transition l E (total l E P Q) hmn).f k).val.app U v))) hei).trans ?_
    refine (congrArg ((en.hom.f k).val.app U)
      (transition_section l E (total l E P Q) hmn k U _)).trans ?_
    refine (congrArg (fun v ↦ (en.hom.f k).val.app U
      (coefficientEvaluationSection l E W _ n U v))
      (tensorTransitions l E P Q hmn p q k hpq U.unop x0 y0)).trans ?_
    refine (evaluation_generator l E P Q n p q k hpq U _ _).trans ?_
    exact congrArg₂
      (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)
        (level l E P n) (level l E Q n) p q k hpq U)
      (transition_section l E P hmn p U x0).symm
      (transition_section l E Q hmn q U y0).symm
  exact recover_from_inverse F em e en
    ((finiteTensor l E W n).map (Prod.mkHom f g)) z hh

/-- The ordinary tensor adjunct factors through the normalized scalar tensor comparison.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 07A6.
(blueprint: lem-pur-strict-tensor-ordinary-adjunct).

Proof: transpose under the ordinary cochain adjunction and test in each degree on
pure tensor generators. The scalar-unit generator equation and tensor-map
naturality reduce the left side to the two horizontal factor transitions. The
evaluation tensor generator equation and horizontal restriction naturality give
the same sections on the right. Explicit restriction-of-scalars transports keep
these section comparisons in the quotient coefficient ring. Cancel the source
evaluation isomorphism to obtain the stated factorization. -/
theorem strictTensorOrdinaryAdjunct {W : Scheme.{t}} (P Q : Complex l E W)
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    (e : ((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W m)).obj (level l E P m, level l E Q m)) ≅
      (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
        (((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).obj
          (level l E P m),
         ((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).obj
          (level l E Q m)))
    (he : CoefficientScalarTensorGenerators.{u, t + 1, t} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W m) (integralCoefficientCommRingSheaf l E W n)
      (coefficientFiniteQuotientExtension l E W hmn)
      (hF := coefficientFiniteQuotientExtensionAdditive l E W hmn)
      (coefficientFiniteQuotientUnitSection l E W hmn) (level l E P m) (level l E Q m) e) :
    ((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).map
        (coefficientEvaluationTensorIso l E W m P Q).hom ≫ e.hom ≫
        (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).map
          (Prod.mkHom (ordinaryAlpha l E P S D hmn) (ordinaryAlpha l E Q S D hmn)) =
      ordinaryAlpha l E (total l E P Q) S D hmn ≫
        (coefficientEvaluationTensorIso l E W n P Q).hom := by
  exact ordinary_tensor l E P Q S D hmn e he

end WeilConjectures.StrictQuotient

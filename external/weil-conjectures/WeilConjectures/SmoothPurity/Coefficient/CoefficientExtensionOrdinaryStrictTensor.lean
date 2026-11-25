/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import all WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Ordinary strict finite coefficient tensor models

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.monoidalCategory integralScalarReduction
private theorem extensionIso_naturality
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u})
    (α : (Functor.const ℕᵒᵖ).obj R ⟶ B)
    {M N : SheafOfModules.SequenceProjection.Modules R} (f : M ⟶ N) (n : ℕ) :
    ((SheafOfModules.SequenceProjection.extension R B α).map f).app n ≫
        (SheafOfModules.SequenceProjection.extensionIso R B α N n).hom =
      (SheafOfModules.SequenceProjection.extensionIso R B α M n).hom ≫
        SheafOfModules.changeOfRingsHom (α.app (op n)) M f := by
  change (SheafOfModules.SequenceProjection.scalar R B α n).model.E.map f ≫
    eqToHom ((SheafOfModules.SequenceProjection.scalar R B α n).model.obj_eq N) = _
  rw [(SheafOfModules.SequenceProjection.scalar R B α n).model.map_eq]
  simp only [SheafOfModules.SequenceProjection.extensionIso, eqToIso.hom,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem strictUnit_hom_section
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u})
    (M : SheafOfModules.StrictRingSystem B) (n : ℕ) (U : Cᵒᵖ)
    (x : (M.level n).val.obj U) :
    (SheafOfModules.strictSystemSequenceUnitLevel B M n).hom.val.app U x = x := by
  rfl

section TensorNormalization
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

private theorem projectionTensor_eq (φ : R ⟶ S)
    (M : SheafOfModules.SequenceProjection.Modules R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    SheafOfModules.SequenceProjection.tensorSection φ M U s x =
      (toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, c, r} φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{v, c, r} φ M)
  have h := (η.app U).hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
  change (toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, c, r} φ M).presheaf).app U
      ((s * 1) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) =
    @SMul.smul (S.obj.obj U) ((SheafOfModules.changeOfRings.{v, c, r} φ M).val.obj U)
      inferInstance s
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, c, r} φ M).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) at h
  simpa only [mul_one, SheafOfModules.SequenceProjection.tensorSection,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply] using h.symm

private theorem projectionTransition_tmul [EssentiallySmall.{r} C]
    (A : Sheaf J CommRingCat.{r}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (M : SheafOfModules.SequenceProjection.Modules A) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (b : (B.obj (op n)).obj.obj U) (b' : (B.obj (op m)).obj.obj U)
    (x : M.val.obj U) (hb : (B.map (homOfLE h).op).hom.app U b = b') :
    HEq ((((SheafOfModules.SequenceProjection.extension A B α).obj M).transition h).val.app U
      (SheafOfModules.systemModelTmul
        (SheafOfModules.SequenceProjection.scalar A B α n).model M U b x))
      (SheafOfModules.systemModelTmul
        (SheafOfModules.SequenceProjection.scalar A B α m).model M U b' x) := by
  subst b'
  exact heq_of_eq (SheafOfModules.SequenceProjection.transition_tmul A B α M h U b x)

private theorem projectionInv_tensor [EssentiallySmall.{r} C]
    (A : Sheaf J CommRingCat.{r}) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (M : SheafOfModules.SequenceProjection.Modules A) (n : ℕ)
    (U : Cᵒᵖ) (s : (B.obj (op n)).obj.obj U) (x : M.val.obj U) :
    (SheafOfModules.SequenceProjection.extensionIso A B α M n).inv.val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf (α.app (op n)) M).presheaf).app U
        (s ⊗ₜ[A.obj.obj U, ((α.app (op n)).hom.app U).hom] x)) =
      SheafOfModules.systemModelTmul
        (SheafOfModules.SequenceProjection.scalar A B α n).model M U s x := by
  erw [← projectionTensor_eq (α.app (op n)) M U s x]
  exact SheafOfModules.SequenceProjection.extensionIso_tensor A B α M n U s x

private theorem strictHorizontal_section [EssentiallySmall.{r} C]
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}) (N : SheafOfModules.StrictRingSystem B)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : (N.level m).val.obj U) :
    ((SheafOfModules.strictSystemToSequenceFunctor B).obj N).val.map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x =
        (N.transition h).val.app U x := by
  change (N.level n).val.map (𝟙 U) ((N.transition h).val.app U x) = _
  erw [PresheafOfModules.map_id]
  rfl

end TensorNormalization

section FunctorTransport
universe c cv d dv r
variable {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {J : GrothendieckTopology D} {R : Sheaf J RingCat.{r}}

private theorem whisker_transport_section_heq
    {X : Type*} [Category X] {F G : C ⥤ SheafOfModules.{r} R}
    (h : F = G) (K : X ⥤ C) (M : X) (U : Dᵒᵖ)
    (x : (G.obj (K.obj M)).val.obj U) :
    HEq ((((Functor.isoWhiskerLeft K (eqToIso h)).inv.app M).val.app U) x) x := by
  cases h
  rfl

private theorem ab_conjugate_apply_heq
    {A B A' B' : AddCommGrpCat.{r}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B')
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g)
    (x : A) (y : A') (hxy : HEq x y) : HEq (f x) (g y) := by
  subst A' B'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst g
  have hx : x = y := eq_of_heq hxy
  subst y
  rfl

private theorem restrict_apply_heq {S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {M N : SheafOfModules.{r} S} (f : M ⟶ N) (U : Dᵒᵖ)
    (x : (((SheafOfModules.restrictScalars φ).obj M).val.obj U)) (y : M.val.obj U)
    (h : HEq x y) :
    HEq ((((SheafOfModules.restrictScalars φ).map f).val.app U) x) (f.val.app U y) := by
  have hx : x = y := eq_of_heq h
  subst y
  rfl

private theorem restrict_toSheaf_obj {S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    (M : SheafOfModules.{r} S) :
    (SheafOfModules.toSheaf R).obj ((SheafOfModules.restrictScalars φ).obj M) =
      (SheafOfModules.toSheaf S).obj M := rfl

private def moduleAbConjugate {S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {A B : SheafOfModules.{r} R} {C₀ D₀ : SheafOfModules.{r} S}
    (e : A ≅ B) (f : C₀ ≅ D₀)
    (τ : A ⟶ (SheafOfModules.restrictScalars φ).obj C₀) :
    (SheafOfModules.toSheaf R).obj B ⟶ (SheafOfModules.toSheaf S).obj D₀ :=
  (SheafOfModules.toSheaf R).map
    (e.inv ≫ τ ≫ (SheafOfModules.restrictScalars φ).map f.hom) ≫
      eqToHom (restrict_toSheaf_obj φ D₀)

private theorem moduleAbConjugate_apply_heq {S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {A B : SheafOfModules.{r} R} {C₀ D₀ : SheafOfModules.{r} S}
    (e : A ≅ B) (f : C₀ ≅ D₀)
    (τ : A ⟶ (SheafOfModules.restrictScalars φ).obj C₀)
    (U : Dᵒᵖ) (x : B.val.obj U) :
    HEq ((moduleAbConjugate φ e f τ).hom.app U x)
      ((((SheafOfModules.restrictScalars φ).map f.hom).val.app U)
        (τ.val.app U (e.inv.val.app U x))) := by
  rfl

private theorem sheafAb_cast_apply_heq
    {A B A' B' : Sheaf J AddCommGrpCat.{r}} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (U : Dᵒᵖ) (x : A.obj.obj U) (y : A'.obj.obj U)
    (hxy : HEq x y) :
    HEq ((eqToHom hA.symm ≫ f ≫ eqToHom hB).hom.app U y) (f.hom.app U x) := by
  subst A' B'
  have hx : x = y := eq_of_heq hxy
  subst y
  rfl

private theorem moduleAb_conjugation_section {S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    {A B : SheafOfModules.{r} R} {C₀ D₀ : SheafOfModules.{r} S}
    (e : A ≅ B) (f : C₀ ≅ D₀)
    (τ : A ⟶ (SheafOfModules.restrictScalars φ).obj C₀)
    (σ : (SheafOfModules.toSheaf R).obj B ⟶ (SheafOfModules.toSheaf S).obj D₀)
    (h : moduleAbConjugate φ e f τ =
      σ)
    (U : Dᵒᵖ) (x : A.val.obj U) :
    HEq (τ.val.app U x) (f.inv.val.app U (σ.hom.app U (e.hom.val.app U x))) := by
  have h₁ := congrArg (fun k ↦ k.val.app U x) e.hom_inv_id
  have h₂ := congrArg (fun k ↦ k.val.app U (τ.val.app U x)) f.hom_inv_id
  have hx := congrArg (fun k ↦ k.hom.app U (e.hom.val.app U x)) h
  change f.hom.val.app U (τ.val.app U (e.inv.val.app U (e.hom.val.app U x))) =
    σ.hom.app U (e.hom.val.app U x) at hx
  change e.inv.val.app U (e.hom.val.app U x) = x at h₁
  rw [h₁] at hx
  have hy := congrArg (fun z ↦ f.inv.val.app U z) hx
  change f.inv.val.app U (f.hom.val.app U (τ.val.app U x)) = τ.val.app U x at h₂
  rw [h₂] at hy
  exact heq_of_eq hy

private theorem completed_conjugation_section {S T : Sheaf J RingCat.{r}}
    (φ : R ⟶ S) (ψ₀ : T ⟶ R) (ψ₁ : T ⟶ S)
    {A B : SheafOfModules.{r} R} {C₀ D₀ : SheafOfModules.{r} S}
    (e : A ≅ B) (f : C₀ ≅ D₀)
    (τ : A ⟶ (SheafOfModules.restrictScalars φ).obj C₀)
    (σ : (SheafOfModules.restrictScalars ψ₀).obj B ⟶
      (SheafOfModules.restrictScalars ψ₁).obj D₀)
    (h : moduleAbConjugate φ e f τ =
      eqToHom (restrict_toSheaf_obj ψ₀ B).symm ≫
        (SheafOfModules.toSheaf T).map σ ≫ eqToHom (restrict_toSheaf_obj ψ₁ D₀))
    (U : Dᵒᵖ) (x : A.val.obj U) :
    HEq (τ.val.app U x) (f.inv.val.app U (σ.val.app U (e.hom.val.app U x))) := by
  have h₀ := moduleAb_conjugation_section φ e f τ _ h U x
  have hb := sheafAb_cast_apply_heq (restrict_toSheaf_obj ψ₀ B)
    (restrict_toSheaf_obj ψ₁ D₀) ((SheafOfModules.toSheaf T).map σ) U
    (e.hom.val.app U x) (e.hom.val.app U x) (HEq.refl _)
  exact h₀.trans (heq_of_eq (congrArg (fun z ↦ f.inv.val.app U z) (eq_of_heq hb)))

end FunctorTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

private def scalarCoefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l L W :=
  NatTrans.ofOpSequence (fun n ↦ integralScalarRho l E L ι W n) (fun n ↦ by
    simp only [Functor.const_obj_map, coefficientSequenceCommRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact (integralScalarRho_transition l E L ι W n).symm)

private def scalarCoefficientExtension : scalarReductionSource l E W ⥤
    coefficientSequenceModules l L W :=
  SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W) ⋙
      SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)

private instance scalarCoefficientExtension_additive :
    (scalarCoefficientExtension l E L ι W).Additive := by
  unfold scalarCoefficientExtension
  let F := SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)
  let G := SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)
  let : G.Additive := ⟨by
    intro M N f g
    ext U x
    change (((f + g).app U.unop.1).val.app (op U.unop.2)) x = _
    have h := (SheafOfModules.systemEvaluation
      (coefficientSequenceCommRingSystem l L W) U.unop.1).map_add (f := f) (g := g)
    have hx := congrArg (fun f ↦ (f.val.app (op U.unop.2)) x) h
    exact hx⟩
  infer_instance

private theorem coefficientEvaluation_ring (n : ℕ) :
    eqToHom (coefficientSequenceEvaluationRing_eq l L W n).symm =
      SheafOfModules.systemSequenceVerticalRingMap (coefficientSequenceCommRingSystem l L W) n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private theorem coefficientEvaluation_eq_system (n : ℕ) :
    coefficientSequenceEvaluation l L W n =
      SheafOfModules.systemSequenceEvaluation (coefficientSequenceCommRingSystem l L W) n := by
  unfold coefficientSequenceEvaluation SheafOfModules.systemSequenceEvaluation
  exact congrArg (SheafOfModules.pushforward (F := Prod.sectR n W.ProEt))
    (coefficientEvaluation_ring l L W n)

private def coefficientEvaluationSystem (n : ℕ) :
    coefficientSequenceModules l L W ⥤ normalizedDVRModules l L W n :=
  SheafOfModules.systemSequenceEvaluation (coefficientSequenceCommRingSystem l L W) n

private theorem coefficientEvaluation_eq_foldedSystem (n : ℕ) :
    coefficientSequenceEvaluation l L W n = coefficientEvaluationSystem l L W n :=
  coefficientEvaluation_eq_system l L W n

private def coefficientEvaluationIso (n : ℕ) :
    coefficientSequenceEvaluation l L W n ≅ coefficientEvaluationSystem l L W n :=
  eqToIso (coefficientEvaluation_eq_foldedSystem l L W n)

section EvaluationTransport
attribute [local irreducible] constantSheaf coefficientSequenceCommRingSheaf
  coefficientEvaluationSystem

private theorem coefficientEvaluation_transport {X : Type*} [Category X] (n : ℕ)
    (K : X ⥤ coefficientSequenceModules l L W)
    (M : X) (U : W.ProEtᵒᵖ)
    (x : ((coefficientEvaluationSystem l L W n).obj (K.obj M)).val.obj U) :
    HEq ((((Functor.isoWhiskerLeft (E := normalizedDVRModules l L W n) K
      (coefficientEvaluationIso l L W n)).inv.app M).val.app U) x) x := by
  unfold coefficientEvaluationIso
  have h := whisker_transport_section_heq
    (coefficientEvaluation_eq_foldedSystem l L W n) K M U x
  exact h

end EvaluationTransport

@[irreducible] private def scalarCoefficientEvaluation (n : ℕ) :
    scalarCoefficientExtension l E L ι W ⋙ coefficientSequenceEvaluation l L W n ≅
      integralScalarReduction l E L ι W n := by
  let F := SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)
  let G := SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)
  let B := coefficientSequenceCommRingSystem l L W
  let a : F ⋙ G ⋙ coefficientSequenceEvaluation l L W n ≅
      F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n :=
    Functor.isoWhiskerLeft (scalarCoefficientExtension l E L ι W)
      (coefficientEvaluationIso l L W n)
  let b : F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n ≅
      F ⋙ SheafOfModules.systemEvaluation B n :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.strictSystemSequenceUnitLevel B
      (F.obj M) n).symm) (by intros; ext U x; rfl)
  let c : F ⋙ SheafOfModules.systemEvaluation B n ≅
      integralScalarReductionConcrete l E L ι W n :=
    NatIso.ofComponents (fun M ↦
      SheafOfModules.SequenceProjection.extensionIso
        (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) M n)
      (by
        intro M N f
        exact extensionIso_naturality
          (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) f n)
  exact a ≪≫ b ≪≫ c ≪≫ (integralScalarReductionIso l E L ι W n).symm

attribute [local irreducible] constantSheaf coefficientSequenceCommRingSheaf
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  integralScalarRho
  SheafOfModules.SequenceProjection.extensionIso integralScalarReductionIso
  SheafOfModules.strictSystemSequenceUnitLevel SheafOfModules.systemModelTmul

private theorem scalarTensor_ab_hom_ext (n : ℕ) (M : scalarReductionSource l E W)
    (N : Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)})
    (f g : (SheafOfModules.toSheaf _).obj
      ((integralScalarReduction l E L ι W n).obj M) ⟶ N)
    (h : ∀ U s x,
      f.hom.app U (integralScalarTensorSection l E L ι W n M U s x) =
        g.hom.app U (integralScalarTensorSection l E L ι W n M U s x)) : f = g := by
  let e := (SheafOfModules.toSheaf _).mapIso
    ((integralScalarReductionIso l E L ι W n).app M)
  apply (cancel_epi e.inv).mp
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext _ _ _ N.property
  ext U z
  induction z using TensorProduct.inductionOn with
  | tmul s x => exact h U s x
  | add z w hz hw => simpa only [_root_.map_add] using congrArg₂ (· + ·) hz hw

private theorem scalarCoefficientEvaluation_inv (n : ℕ)
    (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (x : ((integralScalarReduction l E L ι W n).obj M).val.obj U) :
    ((scalarCoefficientEvaluation l E L ι W n).inv.app M).val.app U x =
      (SheafOfModules.SequenceProjection.extensionIso
        (completedIntegralCommRingSheafUnrestricted l E W)
        (coefficientSequenceCommRingSystem l L W)
        (scalarCoefficientCone l E L ι W) M n).inv.val.app U
        (((integralScalarReductionIso l E L ι W n).hom.app M).val.app U x) := by
  simp only [scalarCoefficientEvaluation, Iso.trans_inv, NatTrans.comp_app,
    NatIso.ofComponents_inv_app, Iso.symm_inv, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  let T := (SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)).obj M
  let z := (SheafOfModules.SequenceProjection.extensionIso
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W) M n).inv.val.app U
      (((integralScalarReductionIso l E L ι W n).hom.app M).val.app U x)
  have ht := coefficientEvaluation_transport l L W n
    (scalarCoefficientExtension l E L ι W)
    M U
      ((SheafOfModules.strictSystemSequenceUnitLevel (coefficientSequenceCommRingSystem l L W)
        T n).hom.val.app U z)
  have hu := strictUnit_hom_section (coefficientSequenceCommRingSystem l L W) T n U z
  have hc := ht.trans (heq_of_eq hu)
  have hh := eq_of_heq hc
  exact hh

private theorem scalarCoefficientEvaluation_inv_tensor (n : ℕ)
    (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U) :
    ((scalarCoefficientEvaluation l E L ι W n).inv.app M).val.app U
        (integralScalarTensorSection l E L ι W n M U s x) =
      (SheafOfModules.SequenceProjection.extensionIso
        (completedIntegralCommRingSheafUnrestricted l E W)
        (coefficientSequenceCommRingSystem l L W)
        (scalarCoefficientCone l E L ι W) M n).inv.val.app U
          ((toSheafify (Scheme.ProEt.topology W)
            (SheafOfModules.changeOfRingsPresheaf
              ((scalarCoefficientCone l E L ι W).app (op n)) M).presheaf).app U
              (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U,
                (((scalarCoefficientCone l E L ι W).app (op n)).hom.app U).hom] x)) := by
  refine (scalarCoefficientEvaluation_inv l E L ι W n M U
    (integralScalarTensorSection l E L ι W n M U s x)).trans ?_
  let e := (integralScalarReductionIso l E L ι W n).app M
  let z := (toSheafify (Scheme.ProEt.topology W)
    (SheafOfModules.changeOfRingsPresheaf
      ((scalarCoefficientCone l E L ι W).app (op n)) M).presheaf).app U
        (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U,
        (((scalarCoefficientCone l E L ι W).app (op n)).hom.app U).hom] x)
  change (SheafOfModules.SequenceProjection.extensionIso
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W)
        (scalarCoefficientCone l E L ι W) M n).inv.val.app U
      (e.hom.val.app U (e.inv.val.app U z)) = _
  have he := congrArg (fun f ↦ f.val.app U z) e.inv_hom_id
  change e.hom.val.app U (e.inv.val.app U z) = z at he
  exact congrArg
    ((SheafOfModules.SequenceProjection.extensionIso
      (completedIntegralCommRingSheafUnrestricted l E W)
      (coefficientSequenceCommRingSystem l L W)
      (scalarCoefficientCone l E L ι W) M n).inv.val.app U) he

private theorem scalarCoefficientEvaluation_inv_tmul (n : ℕ)
    (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U) :
    ((scalarCoefficientEvaluation l E L ι W n).inv.app M).val.app U
        (integralScalarTensorSection l E L ι W n M U s x) =
      SheafOfModules.systemModelTmul
        (φ := (scalarCoefficientCone l E L ι W).app (op n))
        (SheafOfModules.SequenceProjection.scalar
          (completedIntegralCommRingSheafUnrestricted l E W)
          (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W) n).model
        M U s x := by
  exact (scalarCoefficientEvaluation_inv_tensor l E L ι W n M U s x).trans
    (projectionInv_tensor (completedIntegralCommRingSheafUnrestricted l E W)
      (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W) M n U s x)

section TransitionSections

private theorem coefficientTransition_section (N : coefficientSequenceModules l L W)
    {m n : ℕ} (h : n ≤ m) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l L W m).obj N).val.obj U) :
    ((coefficientSequenceTransition l L W h).app N).val.app U x =
      N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  have ht := (coefficientSequenceTransition_exists l L W h).exists.choose_spec N U
  have hh := ab_conjugate_apply_heq
    (coefficientSequenceEvaluationAb_eq l L W N m U)
    (coefficientSequenceRestrictedEvaluationAb_eq l L W N h U)
    ((forget₂ (ModuleCat.{max u (t + 1)}
      ((integralCoefficientSheaf l L W m).obj.obj U)) AddCommGrpCat).map
        (((coefficientSequenceTransition l L W h).app N).val.app U))
    (N.val.presheaf.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) ht x x (HEq.refl x)
  exact eq_of_heq hh

end TransitionSections

private theorem scalarCoefficientTransition_section (M : scalarReductionSource l E W)
    {m n : ℕ} (h : n ≤ m) (U : W.ProEtᵒᵖ)
    (x : (((coefficientSequenceEvaluation l L W m).obj
      ((scalarCoefficientExtension l E L ι W).obj M)).val.obj U)) :
    ((coefficientSequenceTransition l L W h).app
      ((scalarCoefficientExtension l E L ι W).obj M)).val.app U x =
    (((SheafOfModules.SequenceProjection.extension
      (completedIntegralCommRingSheafUnrestricted l E W)
      (coefficientSequenceCommRingSystem l L W)
      (scalarCoefficientCone l E L ι W)).obj M).transition h).val.app U x := by
  exact (coefficientTransition_section l L W
    ((scalarCoefficientExtension l E L ι W).obj M) h U x).trans
      (strictHorizontal_section (coefficientSequenceCommRingSystem l L W)
        ((SheafOfModules.SequenceProjection.extension
          (completedIntegralCommRingSheafUnrestricted l E W)
          (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)).obj M)
        h U x)

private theorem scalarCoefficientTransition_inv_tensor (n : ℕ)
    (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W (n + 1)).obj.obj U) (x : M.val.obj U) :
    HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app
      ((scalarCoefficientExtension l E L ι W).obj M)).val.app U
        (((scalarCoefficientEvaluation l E L ι W (n + 1)).inv.app M).val.app U
          (integralScalarTensorSection l E L ι W (n + 1) M U s x)))
      (((scalarCoefficientEvaluation l E L ι W n).inv.app M).val.app U
        (integralScalarTensorSection l E L ι W n M U
          ((integralCoefficientSheafTransition l L W n).hom.app U s) x)) := by
  have hi := scalarCoefficientEvaluation_inv_tmul l E L ι W (n + 1) M U s x
  have hj := scalarCoefficientEvaluation_inv_tmul l E L ι W n M U
    ((integralCoefficientSheafTransition l L W n).hom.app U s) x
  have hs : ((coefficientSequenceCommRingSystem l L W).map
      (homOfLE (Nat.le_succ n)).op).hom.app U s =
        (integralCoefficientSheafTransition l L W n).hom.app U s := by
    exact congrArg (fun f ↦ f.hom.app U s)
      (Functor.ofOpSequence_map_homOfLE_succ (coefficientSequenceCommRingTransition l L W) n)
  have hp := projectionTransition_tmul
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)
    M (Nat.le_succ n) U s ((integralCoefficientSheafTransition l L W n).hom.app U s) x hs
  have ht := scalarCoefficientTransition_section l E L ι W M (Nat.le_succ n) U
    (((scalarCoefficientEvaluation l E L ι W (n + 1)).inv.app M).val.app U
      (integralScalarTensorSection l E L ι W (n + 1) M U s x))
  have hc := congrArg (fun z ↦
    (((SheafOfModules.SequenceProjection.extension
      (completedIntegralCommRingSheafUnrestricted l E W)
      (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)).obj M).transition
        (Nat.le_succ n)).val.app U z) hi
  exact (heq_of_eq ht).trans
    ((heq_of_eq hc).trans (hp.trans (heq_of_eq hj.symm)))

attribute [local irreducible] scalarCoefficientExtension

private def scalarCoefficientDirect :
    (integralOperationsGoodComplex l E W).FullSubcategory ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ :=
  (integralOperationsGoodComplex l E W).ι ⋙
    (scalarCoefficientExtension l E L ι W).mapHomologicalComplex (.up ℤ)

private def scalarCoefficientDirectEvaluation (n : ℕ) :
    scalarCoefficientDirect l E L ι W ⋙
        (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n := by
  unfold scalarCoefficientDirect
  exact Functor.isoWhiskerLeft (integralOperationsGoodComplex l E W).ι
    (Functor.mapHomologicalComplexCompIso (scalarCoefficientEvaluation l E L ι W n) (.up ℤ))

attribute [local semireducible] scalarCoefficientExtension
attribute [local irreducible] IsCoefficientExtensionStrictTransition

/-- Ordinary strict finite scalar tensors and their quotient transitions.

Source: Stacks 03EK, 03D7 and 0941; step 1 of
stage3-pur-extension-strict-representatives
(blueprint: stage3-pur-extension-ordinary-strict-tensor).

Proof: use the cone with nth component integralScalarRho. Its naturality follows
from the completed-ring limit projections and the finite quotient inclusion
naturality. Apply the ordinary ringed sequence projection tensor functor and
pass from strict systems to module sheaves on the sequence site. On each level
its extensionIso, the identity-on-sections equivalence unit, and
integralScalarReduction_obj give the natural finite evaluation isomorphism.
Apply this additive functor degreewise and restrict to good complexes.
The projection functor's transition formula sends b tensor x to red(b) tensor x.
The finite evaluation isomorphisms carry those tensor sections to the published
integralScalarTensorSection. The published integralScalarTransition has exactly
the same tensor formula. Forget to abelian sheaves and apply tensor hom-ext:
locally sheafified pure tensors generate, so the two maps agree. Cancel the
finite evaluation isomorphisms to get the required equality on all sections,
and hence its HEq formulation. -/
theorem coefficientExtensionOrdinaryStrictTensor_exists :
    ∃ (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
        CochainComplex (coefficientSequenceModules l L W) ℤ)
      (directEvaluation : ∀ n : ℕ,
        direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
          (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n),
      IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation := by
  refine Exists.intro (scalarCoefficientDirect l E L ι W) ?_
  refine Exists.intro (scalarCoefficientDirectEvaluation l E L ι W) ?_
  unfold IsCoefficientExtensionStrictTransition
  intro P n i U x
  let M := P.obj.X i
  change ((coefficientSequenceEvaluation l L W (n + 1)).obj
    ((scalarCoefficientExtension l E L ι W).obj M)).val.obj U at x
  let e (k : ℕ) := (scalarCoefficientEvaluation l E L ι W k).app M
  let τ := (coefficientSequenceTransition l L W (Nat.le_succ n)).app
    ((scalarCoefficientExtension l E L ι W).obj M)
  let σ := ((integralScalarTransition l E L ι W n).app P.obj).f i
  change HEq (τ.val.app U x)
    ((e n).inv.val.app U (σ.val.app U ((e (n + 1)).hom.val.app U x)))
  let a := moduleAbConjugate (normalizedDVRQuotient l L W (Nat.le_succ n))
    (e (n + 1)) (e n) τ
  let ψ (k : ℕ) := (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l L W k)
  have hk (k : ℕ) : (SheafOfModules.toSheaf _).obj
      (((integralScalarLevel l E L ι W k).obj P.obj).X i) =
      (SheafOfModules.toSheaf _).obj ((integralScalarReduction l E L ι W k).obj M) :=
    restrict_toSheaf_obj (ψ k) ((integralScalarReduction l E L ι W k).obj M)
  let b := eqToHom (hk (n + 1)).symm ≫
    (SheafOfModules.toSheaf _).map σ ≫ eqToHom (hk n)
  have hab : a = b := by
    apply scalarTensor_ab_hom_ext l E L ι W (n + 1) M
    intro V s y
    have ha := moduleAbConjugate_apply_heq
      (normalizedDVRQuotient l L W (Nat.le_succ n)) (e (n + 1)) (e n) τ V
      (integralScalarTensorSection l E L ι W (n + 1) M V s y)
    have ht := scalarCoefficientTransition_inv_tensor l E L ι W n M V s y
    have hc := restrict_apply_heq
      (normalizedDVRQuotient l L W (Nat.le_succ n)) (e n).hom V
      (τ.val.app V ((e (n + 1)).inv.val.app V
        (integralScalarTensorSection l E L ι W (n + 1) M V s y)))
      ((e n).inv.val.app V (integralScalarTensorSection l E L ι W n M V
        ((integralCoefficientSheafTransition l L W n).hom.app V s) y)) ht
    have he := congrArg (fun f ↦ f.val.app V
      (integralScalarTensorSection l E L ι W n M V
        ((integralCoefficientSheafTransition l L W n).hom.app V s) y)) (e n).inv_hom_id
    have hb := sheafAb_cast_apply_heq (hk (n + 1)) (hk n)
      ((SheafOfModules.toSheaf _).map σ) V
      (integralScalarTensorSection l E L ι W (n + 1) M V s y)
      (integralScalarTensorSection l E L ι W (n + 1) M V s y) (HEq.refl _)
    exact eq_of_heq (ha.trans (hc.trans ((heq_of_eq he).trans
      ((heq_of_eq ((integralScalarTransition_existsUnique l E L ι W n).exists.choose_spec
        P.obj i V s y).symm).trans hb.symm))))
  exact completed_conjugation_section
    (normalizedDVRQuotient l L W (Nat.le_succ n)) (ψ (n + 1)) (ψ n)
    (e (n + 1)) (e n) τ σ hab U x

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientNormalizationModels
import all WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.TraceFormula.Supporting.TransportedReductionSystemsNormalized
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarBetaComparison
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedScalarRouteCoordinates

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] substituteInputs
attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients
  sourceExpression targetExpression

private theorem good_of_system {W : Scheme.{u}} (A : StrictQuotient.Complex l E W)
    (hA : StrictQuotient.SystemGood l E A)
    (hn : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A)) :
    ScalarGood l E L false W A := by
  unfold ScalarGood
  exact ⟨hA, (StrictQuotient.levelwiseFlatModels l E W A).2 hA, hn⟩

private theorem normalized_tensor {W : Scheme.{u}}
    (A B : StrictQuotient.Complex l E W)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (hnA : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A))
    (hnB : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj B)) :
    IsNormalizedCoefficientSequence l E W
      (DerivedCategory.Q.obj (StrictQuotient.total l E A B)) := by
  let C := pullbackTensorCalculus l E W
  let F := coefficientSequenceLimit l E W
  have := counit_iso l E _ hnA
  have := counit_iso l E _ hnB
  let eA := asIso (C.adjunction.counit.app (DerivedCategory.Q.obj A))
  let eB := asIso (C.adjunction.counit.app (DerivedCategory.Q.obj B))
  apply CompletedOperations.normalizedIso l E
    ((C.reductionTensor.app (F.obj (DerivedCategory.Q.obj A),
      F.obj (DerivedCategory.Q.obj B))) ≪≫
      C.systemClosed.tensor.mapIso (Iso.prod eA eB) ≪≫
      (pullbackTensorSystemModel l E W A B hA.1 hB.1).symm)
  exact C.reduction_normalized _

private theorem normalized_pull {V W : Scheme.{u}} (g : V ⟶ W)
    (hV : ∀ x : V, IsUnit (l : V.residueField x))
    (hW : ∀ x : W, IsUnit (l : W.residueField x))
    (A : StrictQuotient.Complex l E W)
    (hn : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A)) :
    IsNormalizedCoefficientSequence l E V
      (DerivedCategory.Q.obj (StrictQuotient.pull l E g A)) := by
  have := counit_iso l E _ hn
  let C := pullbackTensorCalculus l E W
  let e := asIso (C.adjunction.counit.app (DerivedCategory.Q.obj A))
  apply CompletedOperations.normalizedIso l E
    ((integralComparisonDerivedSequencePullback l E g).mapIso e ≪≫
      (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.app A)
  exact (transportedReductionSystems_normalized l E E (AlgHom.id _ _) g hV hW C).1 _

private theorem normalized_scalar {W : Scheme.{u}}
    (hW : ∀ x : W, IsUnit (l : W.residueField x))
    (A : StrictQuotient.Complex l E W) (hA : StrictQuotient.SystemGood l E A)
    (hn : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A)) :
    IsNormalizedCoefficientSequence l L W
      (DerivedCategory.Q.obj ((ScalarExtensionTower.scalar l E L ι W).obj A)) := by
  have := counit_iso l E _ hn
  let C := pullbackTensorCalculus l E W
  let e := asIso (C.adjunction.counit.app (DerivedCategory.Q.obj A))
  let a := (integralComparisonSequenceScalarModel l E L ι W).ε.app A
  have ha : IsIso a :=
    (integralComparisonSequenceScalarModel l E L ι W).computes A hA.1
  apply CompletedOperations.normalizedIso l L
    ((integralComparisonDerivedSequenceScalar l E L ι W).mapIso e ≪≫ @asIso _ _ _ _ a ha)
  exact (transportedReductionSystems_normalized l E L ι (𝟙 W) hW hW C).2 _

private theorem scalar_generated_good
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    {d : Bool} {W : Scheme.{u}} {A : ScalarComplex l E L d W}
    (hA : ScalarGenerated l E L ι h f (fun i ↦ quotient l E (P i).obj) d W A) :
    ScalarGood l E L d W A := by
  have hn (i : Fin 3) :
      IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj (quotient l E (P i).obj)) :=
    expressions_normalized l E h f P
      (fun i ↦ completedQuotientReductionPresentation l E Y (P i)) (.input i)
  have hu (D : Type u) [Field D] [Algebra ℚ_[l] D] [FiniteDimensional ℚ_[l] D]
      (W : Scheme.{u}) (hw : W = Z ∨ W = X ∨ W = Y) :
      ScalarGood l D D false W
        (HomologicalComplex.tensorUnit (coefficientSequenceModules l D W) (.up ℤ)) := by
    have hw' : ∀ x : W, IsUnit (l : W.residueField x) := by
      rcases hw with rfl | rfl | rfl <;> exact fun x ↦ isUnit_of_invertible _
    exact good_of_system l D D _ (StrictQuotient.unit_system_good l D W)
      (CompletedOperations.modelUnit l D (W := fun _ : Unit ↦ W) () hw')
  have hp {V W : Scheme.{u}} (g : V ⟶ W) (hg : StrictQuotient.AllowedArrow h f g) :
      (∀ x : V, IsUnit (l : V.residueField x)) ∧
      (∀ x : W, IsUnit (l : W.residueField x)) := by
    cases hg <;> exact ⟨fun x ↦ isUnit_of_invertible _, fun x ↦ isUnit_of_invertible _⟩
  induction hA with
  | input i => exact good_of_system l E L _ (quotient_good l E (P i)) (hn i)
  | unitE W hw => simpa only [ScalarGood] using hu E W hw
  | unitL W hw => simpa only [ScalarGood] using hu L W hw
  | @tensorE W A B hA hB ihA ihB =>
      unfold ScalarGood at ihA ihB ⊢
      exact ⟨StrictQuotient.tensor_system_good l E A B ihA.1 ihB.1,
        (StrictQuotient.levelwiseFlatModels l E W _).2
          (StrictQuotient.tensor_system_good l E A B ihA.1 ihB.1),
        normalized_tensor l E A B ihA.1 ihB.1 ihA.2.2 ihB.2.2⟩
  | @tensorL W A B hA hB ihA ihB =>
      unfold ScalarGood at ihA ihB ⊢
      exact ⟨StrictQuotient.tensor_system_good l L A B ihA.1 ihB.1,
        (StrictQuotient.levelwiseFlatModels l L W _).2
          (StrictQuotient.tensor_system_good l L A B ihA.1 ihB.1),
        normalized_tensor l L A B ihA.1 ihB.1 ihA.2.2 ihB.2.2⟩
  | @pullE V W g hg A hA ihA =>
      unfold ScalarGood at ihA ⊢
      exact ⟨StrictQuotient.pull_system_good l E g A ihA.1,
        (StrictQuotient.levelwiseFlatModels l E V _).2
          (StrictQuotient.pull_system_good l E g A ihA.1),
        normalized_pull l E g (hp g hg).1 (hp g hg).2 A ihA.2.2⟩
  | @pullL V W g hg A hA ihA =>
      unfold ScalarGood at ihA ⊢
      exact ⟨StrictQuotient.pull_system_good l L g A ihA.1,
        (StrictQuotient.levelwiseFlatModels l L V _).2
          (StrictQuotient.pull_system_good l L g A ihA.1),
        normalized_pull l L g (hp g hg).1 (hp g hg).2 A ihA.2.2⟩
  | @scalar W A hA ihA =>
      unfold ScalarGood at ihA ⊢
      have loc : ∀ {d W A},
          ScalarGenerated l E L ι h f (fun i ↦ quotient l E (P i).obj) d W A →
          W = Z ∨ W = X ∨ W = Y := by
        intro d W A hA
        induction hA with
        | input => exact Or.inr (Or.inr rfl)
        | unitE W hw => exact hw
        | unitL W hw => exact hw
        | tensorE _ _ ihA _ => exact ihA
        | tensorL _ _ ihA _ => exact ihA
        | pullE g hg _ _ => cases hg <;> simp
        | pullL g hg _ _ => cases hg <;> simp
        | scalar _ ihA => exact ihA
      have hw := loc hA
      have hw' : ∀ x : W, IsUnit (l : W.residueField x) := by
        rcases hw with rfl | rfl | rfl <;> exact fun x ↦ isUnit_of_invertible _
      have hs := ScalarExtensionTower.scalar_good l E L ι W A ihA.1
      exact ⟨hs, (StrictQuotient.levelwiseFlatModels l L W _).2 hs,
        normalized_scalar l E L ι hw' A ihA.1 ihA.2.2⟩

private theorem scalar_expressions_generated
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    ScalarGenerated l E L ι h f (fun i ↦ quotient l E (P i).obj) true W
      (strictValue l L (scalarQuotients l E L ι P) A) := by
  induction A with
  | input i =>
      change ScalarGenerated l E L ι h f (fun i ↦ quotient l E (P i).obj) true Y
        ((ScalarExtensionTower.scalar l E L ι Y).obj (quotient l E (P i).obj))
      exact .scalar (.input i)
  | unitY => exact .unitL Y (Or.inr (Or.inr rfl))
  | unitX => exact .unitL X (Or.inr (Or.inl rfl))
  | unitZ => exact .unitL Z (Or.inl rfl)
  | tensor A B ihA ihB => exact .tensorL ihA ihB
  | pullF A ih => exact .pullL f .first ih
  | pullH A ih => exact .pullL h .second ih
  | pullHF A ih => exact .pullL (h ≫ f) .composite ih

private theorem scalar_substitution_iso {W : Scheme.{u}}
    {ρ : IntegralComparisonRoosModel l L W}
    (S : IntegralComparisonScalarModel l E L ι W (pullbackTensorCalculus l E W) ρ)
    {K : DerivedCategory (scalarReductionSource l E W)}
    (A : StrictQuotient.Complex l E W) (hA : StrictQuotient.SystemGood l E A)
    (hn : IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj A))
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (hβ : IsIso β) :
    IsIso (scalarSubstitution l E L ι S A β) := by
  have := hβ
  unfold scalarSubstitution
  exact (S.realization.app K ≪≫ (coefficientSequenceLimit l L W).mapIso
    ((integralComparisonDerivedSequenceScalar l E L ι W).mapIso
      (@asIso _ _ _ _ (reduction l E β) (reduction_iso l E β hn)) ≪≫
      @asIso _ _ _ _ ((integralComparisonSequenceScalarModel l E L ι W).ε.app A)
        ((integralComparisonSequenceScalarModel l E L ι W).computes A hA.1))).isIso_hom

private theorem scalar_beta_iso
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A))
    {ρY : IntegralComparisonRoosModel l L Y}
    (SY : IntegralComparisonScalarModel l E L ι Y (pullbackTensorCalculus l E Y) ρY)
    (goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A))
    {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :
    IsIso (scalarBeta l E L ι M P φ good SY goodL A) := by
  have hn {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :=
    scalar_generated_good l E L ι h f M P φ (scalar_expressions_generated l E L ι h f P A)
  unfold ScalarGood at hn
  unfold scalarBeta
  refine substitute_inputs_iso l L (h := h) (f := f) (scalarQuotients l E L ι P)
    (fun i ↦ (integralScalarExtension l E L ι Y).obj (M i).obj)
    (fun i ↦ scalarSubstitution l E L ι SY (quotient l E (P i).obj)
      (substitution l E P (fun j ↦ (M j).obj) φ good (.input i)))
    goodL (fun A ↦ (hn A).2.2) ?_ A
  intro i
  exact scalar_substitution_iso l E L ι SY _ (quotient_good l E (P i))
    (expressions_normalized l E h f P
      (fun i ↦ completedQuotientReductionPresentation l E Y (P i)) (.input i))
    _ (invertible (.input i))

private theorem cancel_coordinate {C : Type*} [Category C] {A B D F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ F) (e : F ≅ D)
    (hc : a ≫ b = c ≫ e.hom) : a ≫ b ≫ e.inv = c := by
  rw [← Category.assoc, hc, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem postcompose_coordinate {C : Type*} [Category C] {A B D F G H I : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ F) (d : F ⟶ G)
    (s : G ⟶ H) (t : H ⟶ D) (i : D ⟶ I)
    (hc : a ≫ b = c ≫ d ≫ s ≫ t) :
    a ≫ b ≫ i = c ≫ d ≫ s ≫ t ≫ i := by
  rw [← Category.assoc, hc]
  simp only [Category.assoc]

private theorem cancel_coordinate_three {C : Type*} [Category C] {A B D F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ F) (d : F ⟶ G) (s : G ⟶ H)
    (e : H ≅ D) (hc : a ≫ b = c ≫ d ≫ s ≫ e.hom) :
    a ≫ b ≫ e.inv = c ≫ d ≫ s := by
  rw [← Category.assoc, hc]
  simp only [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Scalar quotient closure and the limit image of the two strict scalar routes.
Source: realization proof steps 6 and 7; Stacks 03EL, 07A4 and 0941
(blueprint: lem-pur-completed-comparison-scalar-limit-image).

Proof: coefficient-extension reduction gives the actual scalar quotient systems.
On flat-term K-flat representatives, balanced association sends (x tensor a) tensor b
to x tensor iota(a)*b, with insertion-of-one inverse. This commutes with quotient
transitions and restrictions. Induct over ScalarGenerated, using tensor and
constant-coefficient inverse-image preservation to obtain flat K-flat normalized
expressions. The normalized scalar model realizes the canonical completed scalar
functor; its counit formula is exactly scalarSubstitution. Induction on the same
expression syntax identifies the L realization with scalarBeta and proves its
invertibility. The strict coefficient square sends b tensor (x tensor y) by both
routes to (b tensor x) tensor (1 tensor y); balancing and local generation prove
equality. Apply the total-limit functor. Expand the normalized scalar, tensor and
pullback realization equations and cancel successive inverse substitutions. The
L comparison becomes the canonical completed comparison by its representative
normalization. The two resulting equations are exactly the two composites in
ScalarLimitImage for each of the equal strict routes. No finite coefficient-map
flatness is used, so ramified extensions are included. -/
theorem completedComparisonScalarLimitImage
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A)) :
    (∀ (d : Bool) (W : Scheme.{u}) (A : ScalarComplex l E L d W),
      ScalarGenerated l E L ι h f (fun i ↦ quotient l E (P i).obj) d W A →
        ScalarGood l E L d W A) ∧
    ScalarLimitImage l E L ι h f M P φ good invertible := by
  have closed : ∀ (d : Bool) (W : Scheme.{u}) (A : ScalarComplex l E L d W),
      ScalarGenerated l E L ι h f (fun i ↦ quotient l E (P i).obj) d W A →
        ScalarGood l E L d W A :=
    fun _ _ _ hA ↦ scalar_generated_good l E L ι h f M P φ hA
  have models (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)] :
      Nonempty (IntegralComparisonRoosModel l L W) := by
    obtain ⟨ML, _⟩ := CompletedOperations.normalizedCompletedOperationModels l L
      (fun _ : Unit ↦ W) (fun _ x ↦ isUnit_of_invertible (l : W.residueField x))
    exact ⟨ML.roos ()⟩
  obtain ⟨ρX⟩ := models X
  obtain ⟨ρY⟩ := models Y
  obtain ⟨SX⟩ := primitiveQuotientScalarModelExistence l E L ι X
    (fun x ↦ isUnit_of_invertible (l : X.residueField x)) (pullbackTensorCalculus l E X) ρX
  obtain ⟨SY⟩ := primitiveQuotientScalarModelExistence l E L ι Y
    (fun y ↦ isUnit_of_invertible (l : Y.residueField y)) (pullbackTensorCalculus l E Y) ρY
  have normalizedL {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W) :=
    closed true W _ (scalar_expressions_generated l E L ι h f P A)
  unfold ScalarGood at normalizedL
  let goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A) :=
    fun A ↦ (normalizedL A).1
  have invertibleL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (scalarBeta l E L ι M P φ good SY goodL A) :=
    fun A ↦ scalar_beta_iso l E L ι h f M P φ good invertible SY goodL A
  obtain ⟨hsquare, hleft, hright⟩ :=
    completedScalarRouteCoordinates l E L ι h f M P φ good invertible ρX ρY SX SY goodL
  have hcanonical := completedScalarBetaComparison l E L ι h f M P φ good SY goodL
  let βt := scalarBeta l E L ι M P φ good SY goodL (targetExpression h f)
  let e := @asIso _ _ _ _ βt (invertibleL (targetExpression h f))
  refine ⟨closed, ?_⟩
  unfold ScalarLimitImage
  refine ⟨ρX, ρY, SX, SY, goodL, invertibleL, hsquare, ?_, ?_⟩
  · unfold scalarTransport
    exact cancel_coordinate _ _ _ e hcanonical
  · intro v hv
    have hv' : v = (scalarLeft l E L ι f (quotient l E (P 0).obj)
        (quotient l E (P 1).obj)).hom := by
      rcases hv with hv | hv
      · exact hv
      · exact hv.trans (congrArg Iso.hom hsquare).symm
    subst v
    constructor
    · unfold scalarTransport
      exact postcompose_coordinate _ _ _ _ _ _ e.inv hleft
    · rw [← hsquare] at hright
      exact cancel_coordinate_three _ _ _ _ _ e hright

end WeilConjectures.CompletedQuotient

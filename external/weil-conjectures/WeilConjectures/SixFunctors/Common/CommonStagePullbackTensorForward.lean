/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonStageInclusionTensorNaturality
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
import WeilConjectures.SixFunctors.Common.CommonStagePullbackTensorInclusion
import all Mathlib.Logic.Small.Defs

/-! # Forward transport of the canonical pullback/tensor inclusion square

Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-stage-pullback-tensor-normalized-forward).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option Elab.async false
set_option linter.auxLemma false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

section

-- Keep the coefficient-category structures abstract during diagram elaboration.
attribute [local irreducible] equivShrink
  HasDerivedCategory.standard integralCoefficientLinear
  instCategoryDerivedCategory DerivedCategory.instPreadditive HomologicalComplex.instCategory
  SheafOfModules.instCategory SheafOfModules.instAbelian
  completedIntegralCommRingSheafUnrestricted
  ObjectProperty.FullSubcategory.category
  rationalPullbackScalarComparison rationalTensorScalarComparison
  Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue
  sfRationalScalarExtension sfConstructibleIntegralScalarExtension
  sfIntegralScalarComp sfIntegralScalarUnit
  canonicalRationalPullbackTensor canonicalCommonStagePullbackTensor
  rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor commonStagePullbackComparison
  commonStageTensorComparison operationStageTransitionIso
  GeneralAlgebraicallyClosedCoefficients.unitor ScalarLocalization.category Scheme.residueField
  StageSystem.PairCategory.categoryStruct Preadditive.fullSubcategory
  sfIntegralConstructible ScalarLocalization.linear ScalarLocalization.preadditive
  Linear.homModule Preadditive.homGroup Linear.fullSubcategory sfIntegralConstructibleLinear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage
  StageSystem.ι
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  commonStagePullbackObject commonStageTensorObject

private theorem forward_of_inverse
    {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
    [Category* A] [Category* B] [Category* A'] [Category* B']
    (F : A ⥤ B) (F' : A' ⥤ B') (c : A ⥤ A') (d : B ⥤ B')
    (e : F ⋙ d ≅ c ⋙ F')
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (TA' : A' × A' ⥤ A') (TB' : B' × B' ⥤ B')
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA') (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (M N : A) (mu : F.obj (TA.obj (M, N)) ⟶ TB.obj (F.obj M, F.obj N))
    (mu' : F'.obj (TA'.obj (c.obj M, c.obj N)) ⟶
      TB'.obj (F'.obj (c.obj M), F'.obj (c.obj N)))
    (h : F'.map (tA.inv.app (M, N)) ≫ e.inv.app (TA.obj (M, N)) ≫ d.map mu =
      mu' ≫ TB'.map (Prod.mkHom (e.inv.app M) (e.inv.app N)) ≫
        tB.inv.app (F.obj M, F.obj N)) :
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' := by
  let z := TB'.mapIso (Iso.prod (e.app M).symm (e.app N).symm) ≪≫
    (tB.app (F.obj M, F.obj N)).symm
  apply (cancel_mono z.hom).1
  change (d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
      TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N))) ≫
      (TB'.map (Prod.mkHom (e.inv.app M) (e.inv.app N)) ≫
        tB.inv.app (F.obj M, F.obj N)) =
    (e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu') ≫
      (TB'.map (Prod.mkHom (e.inv.app M) (e.inv.app N)) ≫
        tB.inv.app (F.obj M, F.obj N))
  simp only [Category.assoc]
  conv_lhs =>
    rw [← TB'.map_comp_assoc]
    simp only [prod_comp, Iso.hom_inv_id_app, ← prod_id, Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  rw [← h]
  simp only [← F'.map_comp_assoc, Iso.hom_inv_id_app]
  erw [TB'.map_id, F'.map_id]
  simp only [Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem inverse_of_identity_component
    {C : Type*} [Category* C] {A B : C} (e : A ≅ B) (h : B = A)
    (he : HEq e.hom (𝟙 A)) : e.inv = eqToHom h := by
  cases h
  have hi := e.hom_inv_id
  simpa only [eq_of_heq he, Category.id_comp, eqToHom_refl] using hi

private theorem normalized_forward_generic
    {A B A' B' : Type*}
    [Category* A] [Category* B] [Category* A'] [Category* B']
    (c : A ⥤ A') (d : B ⥤ B')
    (F F₀ : A ⥤ B) (F' F'₀ : A' ⥤ B')
    (TA TA₀ : A × A ⥤ A) (TB TB₀ : B × B ⥤ B)
    (TA' TA'₀ : A' × A' ⥤ A') (TB' TB'₀ : B' × B' ⥤ B')
    (hF : F = F₀) (hF' : F' = F'₀)
    (hTA : TA = TA₀) (hTB : TB = TB₀) (hTA' : TA' = TA'₀) (hTB' : TB' = TB'₀)
    (tA : TA ⋙ c ≅ c.prod c ⋙ TA') (tB : TB ⋙ d ≅ d.prod d ⋙ TB')
    (tA₀ : TA₀ ⋙ c ≅ c.prod c ⋙ TA'₀) (tB₀ : TB₀ ⋙ d ≅ d.prod d ⋙ TB'₀)
    (htA : HEq tA tA₀) (htB : HEq tB tB₀)
    (e : F ⋙ d ≅ c ⋙ F')
    (he : ∀ K, HEq (e.hom.app K) (𝟙 (d.obj (F.obj K))))
    (ho : ∀ K, F'₀.obj (c.obj K) = d.obj (F₀.obj K))
    (M N : A)
    (mu : F.obj (TA.obj (M, N)) ⟶ TB.obj (F.obj M, F.obj N))
    (mu' : F'.obj (TA'.obj (c.obj M, c.obj N)) ⟶
      TB'.obj (F'.obj (c.obj M), F'.obj (c.obj N)))
    (mu₀ : F₀.obj (TA₀.obj (M, N)) ⟶ TB₀.obj (F₀.obj M, F₀.obj N))
    (mu'₀ : F'₀.obj (TA'₀.obj (c.obj M, c.obj N)) ⟶
      TB'₀.obj (F'₀.obj (c.obj M), F'₀.obj (c.obj N)))
    (hmu : HEq mu mu₀) (hmu' : HEq mu' mu'₀)
    (h : F'₀.map (tA₀.inv.app (M, N)) ≫ eqToHom (ho (TA₀.obj (M, N))) ≫ d.map mu₀ =
      mu'₀ ≫ TB'₀.map (Prod.mkHom (eqToHom (ho M)) (eqToHom (ho N))) ≫
        tB₀.inv.app (F₀.obj M, F₀.obj N)) :
    d.map mu ≫ tB.hom.app (F.obj M, F.obj N) ≫
        TB'.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TA.obj (M, N)) ≫ F'.map (tA.hom.app (M, N)) ≫ mu' := by
  subst F F' TA TB TA' TB'
  cases eq_of_heq htA
  cases eq_of_heq htB
  cases eq_of_heq hmu
  cases eq_of_heq hmu'
  have hei (K : A) : e.inv.app K = eqToHom (ho K) :=
    inverse_of_identity_component (e.app K) (ho K) (he K)
  apply forward_of_inverse F₀ F'₀ c d e TA₀ TB₀ TA'₀ TB'₀ tA₀ tB₀ M N mu₀ mu'₀
  simpa only [hei] using h

/-- Normalized pullback and tensor data preserve the canonical forward inclusion square.

Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-stage-pullback-tensor-normalized-forward).

Proof: substitute the given functor equalities and heterogeneous comparison
normalizations. The pullback comparison has identity components, so its inverse
is the prescribed object-equality morphism. Apply the canonical inverse inclusion
square. Postcompose by the tensor of inverse pullback comparisons and the inverse
target tensorator, then cancel the isomorphisms by functoriality to obtain the
forward equation. No geometric hypothesis on the scheme map is used. -/
theorem commonStagePullbackTensor_forward_of_normalizations
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : Index l Ω)
    (R : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (F : generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (TY : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y ×
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y ⥤
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (TX : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ×
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (UY : generalAlgebraicallyClosedConstructibleCategory l Ω Y ×
      generalAlgebraicallyClosedConstructibleCategory l Ω Y ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (UX : generalAlgebraicallyClosedConstructibleCategory l Ω X ×
      generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (hR : R = rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
    (hF : F = commonStageDerivedPullback l Ω f)
    (hTY : TY = rationalDerivedTensor l (Coefficient.{u} l Ω E) Y)
    (hTX : TX = rationalDerivedTensor l (Coefficient.{u} l Ω E) X)
    (hUY : UY = commonStageDerivedTensor l Ω Y)
    (hUX : UX = commonStageDerivedTensor l Ω X)
    (tY : TY ⋙ inclusion (Y := Y) E ≅
      (inclusion (Y := Y) E).prod (inclusion (Y := Y) E) ⋙ UY)
    (tX : TX ⋙ inclusion (Y := X) E ≅
      (inclusion (Y := X) E).prod (inclusion (Y := X) E) ⋙ UX)
    (htY : HEq tY (commonInclusionTensorComparison l Ω Y E))
    (htX : HEq tX (commonInclusionTensorComparison l Ω X E))
    (e : R ⋙ inclusion (Y := X) E ≅ inclusion (Y := Y) E ⋙ F)
    (he : ∀ K, HEq (e.hom.app K) (𝟙 ((inclusion (Y := X) E).obj (R.obj K))))
    (M N : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (mu : R.obj (TY.obj (M, N)) ⟶ TX.obj (R.obj M, R.obj N))
    (mu' : F.obj (UY.obj ((inclusion (Y := Y) E).obj M,
      (inclusion (Y := Y) E).obj N)) ⟶
        UX.obj (F.obj ((inclusion (Y := Y) E).obj M),
          F.obj ((inclusion (Y := Y) E).obj N)))
    (hmu : HEq mu (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω E) f M N).hom)
    (hmu' : HEq mu' (canonicalCommonStagePullbackTensor l Ω f
      ((inclusion (Y := Y) E).obj M) ((inclusion (Y := Y) E).obj N)).hom) :
    (inclusion (Y := X) E).map mu ≫ tX.hom.app (R.obj M, R.obj N) ≫
        UX.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (TY.obj (M, N)) ≫ F.map (tY.hom.app (M, N)) ≫ mu' := by
  have ho : ∀ K, (commonStageDerivedPullback l Ω f).obj K =
      commonStagePullbackObject l Ω f K := by
    unfold commonStageDerivedPullback
    exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1
  exact normalized_forward_generic (inclusion (Y := Y) E) (inclusion (Y := X) E)
    R (rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
    F (commonStageDerivedPullback l Ω f)
    TY (rationalDerivedTensor l (Coefficient.{u} l Ω E) Y)
    TX (rationalDerivedTensor l (Coefficient.{u} l Ω E) X)
    UY (commonStageDerivedTensor l Ω Y) UX (commonStageDerivedTensor l Ω X)
    hR hF hTY hTX hUY hUX tY tX
    (commonInclusionTensorComparison l Ω Y E) (commonInclusionTensorComparison l Ω X E)
    htY htX e he (fun K ↦ ho ((inclusion (Y := Y) E).obj K)) M N mu mu'
    (canonicalRationalPullbackTensor l (Coefficient.{u} l Ω E) f M N).hom
    (canonicalCommonStagePullbackTensor l Ω f
      ((inclusion (Y := Y) E).obj M) ((inclusion (Y := Y) E).obj N)).hom
    hmu hmu' (commonStagePullbackTensor_inclusion_inverse l Ω f E M N)

end
end WeilConjectures

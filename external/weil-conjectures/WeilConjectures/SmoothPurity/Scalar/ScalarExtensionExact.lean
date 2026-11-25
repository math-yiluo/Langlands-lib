/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import WeilConjectures.SmoothPurity.Supporting.RationalizationKaroubi
public import WeilConjectures.CategoryTheory.ScalarLocalization.RationalizationLocalization
public import WeilConjectures.CategoryTheory.Shift.CommShiftExt
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Functor

import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

/-! # Exactness of finite scalar extension

Source: blueprint `sec-smooth-purity/sk-prop-sf-pf-reduction`, order 1883
(blueprint: lem-weil-scalar-extension-exact-triangulated).
The shift comparison is specified on integral representatives, including its sign.
-/

@[expose] public section
set_option autoImplicit false

universe d u
open CategoryTheory TensorProduct

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The shift comparison of the integral functor induced from its ambient functor. -/
private noncomputable abbrev integralLiftCommShift :
    (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ :=
  inferInstanceAs (((boundedConstructibleDerivedCompleteIntegral D l hl L Y).lift
    ((boundedConstructibleDerivedCompleteIntegral D l hl E Y).ι ⋙
      integralOrdinaryDerivedScalar l E L ι Y)
    (fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y K.obj
      K.property)).CommShift ℤ)

private theorem integralLiftCommShift_spec (n : ℤ)
    (K : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    HEq ((@Functor.commShiftIso _ _ _ _ (integralConstructibleScalarExtension D l hl E L ι Y) ℤ
        _ _ _ (integralLiftCommShift D l hl E Y L ι) n).hom.app K).hom
      (((integralOrdinaryDerivedScalar l E L ι Y).commShiftIso n).hom.app K.obj) :=
  ObjectProperty.lift_ι_comp_commShiftIso_hom_app_hom_heq (A := ℤ)
    (boundedConstructibleDerivedCompleteIntegral D l hl L Y)
    (boundedConstructibleDerivedCompleteIntegral D l hl E Y)
    (integralOrdinaryDerivedScalar l E L ι Y)
    (fun K ↦ integralOrdinaryDerivedScalar_constructible D l hl E L ι Y K.obj K.property) n K

set_option linter.unusedVariables false in
/-- The full subcategory inherits the ordinary derived tensor shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: the ambient termwise exact tensor functor has its canonical derived shift
comparison. Full faithfulness of the inclusions lifts it uniquely. The ambient zero
and addition coherence equations imply the same equations after this lift. -/
theorem integralConstructibleScalarCommShift_existsUnique :
    ∃! c : (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ,
      (fun [commInst :
          (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ] ↦
        ∀ (n : ℤ) K,
          HEq (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso n).hom.app
              K).hom
            (((integralOrdinaryDerivedScalar l E L ι Y).commShiftIso n).hom.app K.obj))
        (commInst := c) := by
  refine ⟨integralLiftCommShift D l hl E Y L ι, integralLiftCommShift_spec D l hl E Y L ι, ?_⟩
  intro c hc
  apply Functor.commShift_ext
  intro n
  ext K
  exact eq_of_heq ((hc n K).trans (integralLiftCommShift_spec D l hl E Y L ι n K).symm)

/-- The uniquely normalized integral shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance integralConstructibleScalarCommShift :
    (integralConstructibleScalarExtension D l hl E L ι Y).CommShift ℤ :=
  (integralConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

private theorem integralConstructibleScalarCommShift_eq :
    integralConstructibleScalarCommShift D l hl E Y L ι = integralLiftCommShift D l hl E Y L ι :=
  (integralConstructibleScalarCommShift_existsUnique D l hl E Y L ι).unique
    (integralConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose_spec
    (integralLiftCommShift_spec D l hl E Y L ι)

private theorem integralConstructibleScalar_isTriangulated :
    (integralConstructibleScalarExtension D l hl E L ι Y).IsTriangulated := by
  rw [integralConstructibleScalarCommShift_eq]
  exact ObjectProperty.isTriangulated_lift _ _ _

attribute [local instance] integralConstructibleShift_linear

/-- Raw rationalization is the localization at the rationalization class. -/
private instance rationalLocalization_isLocalization :
    (rationalConstructibleLocalization D l hl E Y).IsLocalization
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)) :=
  ScalarLocalization.localization_isLocalization _ _ _

/-- Raw rationalization is exact for the recorded triangulation. -/
private theorem rationalLocalization_isTriangulated :
    (rationalConstructibleLocalization D l hl E Y).IsTriangulated :=
  (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.2
    |>.choose_spec.2.1

private theorem rationalLocalization_obj_shift
    (X : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    (rationalConstructibleLocalization D l hl E Y).obj (X⟦(1 : ℤ)⟧) =
      ((rationalConstructibleLocalization D l hl E Y).obj X)⟦(1 : ℤ)⟧ :=
  (Functor.congr_obj (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.1
    ((rationalConstructibleLocalization D l hl E Y).obj X)).symm

private theorem rationalLocalization_commShiftIso_hom_app
    (X : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    ((rationalConstructibleLocalization D l hl E Y).commShiftIso (1 : ℤ)).hom.app X =
      eqToHom (rationalLocalization_obj_shift D l hl E Y X) :=
  eq_eqToHom_of_heq_id _ _
    ((rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.2.choose_spec.choose_spec.1 X)

private theorem rationalLocalization_commShiftIso_inv_app
    (X : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
    ((rationalConstructibleLocalization D l hl E Y).commShiftIso (1 : ℤ)).inv.app X =
      eqToHom (rationalLocalization_obj_shift D l hl E Y X).symm := by
  rw [← cancel_epi
      (((rationalConstructibleLocalization D l hl E Y).commShiftIso (1 : ℤ)).hom.app X),
    Iso.hom_inv_id_app, rationalLocalization_commShiftIso_hom_app, eqToHom_trans, eqToHom_refl]

/-- The raw rational functor restricts to integral extension followed by rationalization. -/
private noncomputable def rationalOrdinaryLiftingIso :
    rationalConstructibleLocalization D l hl E Y ⋙
        rationalOrdinaryScalarExtension D l hl E Y L ι ≅
      integralConstructibleScalarExtension D l hl E L ι Y ⋙
        rationalConstructibleLocalization D l hl L Y :=
  NatIso.ofComponents (fun K ↦ Iso.refl _) (fun {K M} f ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.comp_map]
    refine ((rationalScalarHom_existsUnique D l hl E Y L ι K M).exists.choose_spec 1 f).trans ?_
    rw [map_one]
    rfl)

private noncomputable instance rationalOrdinaryLifting :
    Localization.Lifting (rationalConstructibleLocalization D l hl E Y)
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y))
      (integralConstructibleScalarExtension D l hl E L ι Y ⋙
        rationalConstructibleLocalization D l hl L Y)
      (rationalOrdinaryScalarExtension D l hl E Y L ι) :=
  ⟨rationalOrdinaryLiftingIso D l hl E Y L ι⟩

/-- The shift comparison of the raw rational functor induced by localization. -/
private noncomputable abbrev rationalOrdinaryLocalizedCommShift :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ :=
  Functor.commShiftOfLocalization (rationalConstructibleLocalization D l hl E Y)
    (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
      (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y)) ℤ
    (integralConstructibleScalarExtension D l hl E L ι Y ⋙
      rationalConstructibleLocalization D l hl L Y)
    (rationalOrdinaryScalarExtension D l hl E Y L ι)

private theorem rationalOrdinaryLocalizedCommShift_spec
    (K : rationalConstructibleCategory D l hl E Y) :
    HEq ((@Functor.commShiftIso _ _ _ _ (rationalOrdinaryScalarExtension D l hl E Y L ι) ℤ _ _ _
        (rationalOrdinaryLocalizedCommShift D l hl E Y L ι) (1 : ℤ)).hom.app K)
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ[
        Padic.coefficientExtensionIntegers l L]
        (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso
          (1 : ℤ)).hom.app K.obj)) := by
  have h := Functor.commShiftOfLocalization_iso_hom_app
    (rationalConstructibleLocalization D l hl E Y)
    (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
      (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y))
    (integralConstructibleScalarExtension D l hl E L ι Y ⋙
      rationalConstructibleLocalization D l hl L Y)
    (rationalOrdinaryScalarExtension D l hl E Y L ι) (1 : ℤ) K.obj
  refine (heq_of_eq h).trans ?_
  have e₁ (X) : (Localization.Lifting.iso (rationalConstructibleLocalization D l hl E Y)
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y))
      (integralConstructibleScalarExtension D l hl E L ι Y ⋙
        rationalConstructibleLocalization D l hl L Y)
      (rationalOrdinaryScalarExtension D l hl E Y L ι)).hom.app X = 𝟙 _ := rfl
  have e₂ (X) : (Localization.Lifting.iso (rationalConstructibleLocalization D l hl E Y)
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y))
      (integralConstructibleScalarExtension D l hl E L ι Y ⋙
        rationalConstructibleLocalization D l hl L Y)
      (rationalOrdinaryScalarExtension D l hl E Y L ι)).inv.app X = 𝟙 _ := rfl
  simp only [e₁, e₂, CategoryTheory.Functor.map_id,
    Functor.commShiftIso_comp_hom_app, rationalLocalization_commShiftIso_inv_app,
    rationalLocalization_commShiftIso_hom_app, eqToHom_map]
  refine (eqToHom_comp_heq _ _).trans ?_
  refine (heq_of_eq (Category.id_comp 
    (obj := rationalConstructibleCategory D l hl L Y) _)).trans ?_
  refine (heq_of_eq (Category.comp_id (obj := rationalConstructibleCategory D l hl L Y) _)).trans ?_
  exact comp_eqToHom_heq _ _

set_option linter.unusedVariables false in
/-- The rational shift comparison is the integral one tensored with one.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: localize the integral shift comparison and inverse. Naturality on pure tensors
extends by additivity. The rational shift by one is the tensor-induced integral shift;
its localization comparison is the identity. Thus the displayed normalization holds.
Iteration and inverse shifts give a coherent comparison for every integer. A coherent
comparison for integer shifts is determined by its component at one, proving uniqueness. -/
theorem rationalOrdinaryScalarCommShift_existsUnique :
    ∃! c : (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst :
          (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        ∀ K, HEq
          (((rationalOrdinaryScalarExtension D l hl E Y L ι).commShiftIso (1 : ℤ)).hom.app K)
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L)) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L]
            (((integralConstructibleScalarExtension D l hl E L ι Y).commShiftIso
              (1 : ℤ)).hom.app K.obj))) (commInst := c) := by
  refine ⟨rationalOrdinaryLocalizedCommShift D l hl E Y L ι,
    rationalOrdinaryLocalizedCommShift_spec D l hl E Y L ι, ?_⟩
  intro c hc
  exact Functor.commShift_ext_of_one _ _ (fun K ↦
    eq_of_heq ((hc K).trans (rationalOrdinaryLocalizedCommShift_spec D l hl E Y L ι K).symm))

/-- The normalized rational shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalOrdinaryScalarCommShift :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).CommShift ℤ :=
  (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

private theorem rationalOrdinaryScalarCommShift_eq :
    rationalOrdinaryScalarCommShift D l hl E Y L ι =
      rationalOrdinaryLocalizedCommShift D l hl E Y L ι :=
  (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L ι).unique
    (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L ι).exists.choose_spec
    (rationalOrdinaryLocalizedCommShift_spec D l hl E Y L ι)

private theorem rationalOrdinaryScalar_isTriangulated :
    (rationalOrdinaryScalarExtension D l hl E Y L ι).IsTriangulated := by
  rw [rationalOrdinaryScalarCommShift_eq]
  let := rationalOrdinaryLocalizedCommShift D l hl E Y L ι
  have := Localization.essSurj_mapArrow (rationalConstructibleLocalization D l hl E Y)
    (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
      (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y))
  have := rationalLocalization_isTriangulated D l hl E Y
  have := rationalLocalization_isTriangulated D l hl L Y
  have := integralConstructibleScalar_isTriangulated D l hl E Y L ι
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso (rationalConstructibleLocalization D l hl E Y)
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y))
      (integralConstructibleScalarExtension D l hl E L ι Y ⋙
        rationalConstructibleLocalization D l hl L Y)
      (rationalOrdinaryScalarExtension D l hl E Y L ι))

set_option linter.unusedVariables false in
/-- The published completed functor carries the unique shift comparison making its
normalized comparison with ordinary tensor commute with every integer shift.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: conjugate the ordinary derived tensor comparison by rationalOrdinaryComparison.
The ordinary comparison satisfies zero and addition coherence; naturality of the
conjugating isomorphism carries both equations to the completed functor. The displayed
commutation fixes every component uniquely, including the signed shift by one. -/
theorem rationalConstructibleScalarCommShift_existsUnique :
    ∃! c : (rationalScalarExtension D l hl E Y L ι).CommShift ℤ,
      (fun [commInst : (rationalScalarExtension D l hl E Y L ι).CommShift ℤ] ↦
        NatTrans.CommShift (rationalOrdinaryComparison D l hl E Y L ι).hom ℤ)
        (commInst := c) := by
  refine ⟨Functor.CommShift.ofIso (rationalOrdinaryComparison D l hl E Y L ι) ℤ,
    Functor.CommShift.ofIso_compatibility _ _, ?_⟩
  intro c hc
  exact Functor.commShift_ext_of_iso _ _ _ hc (Functor.CommShift.ofIso_compatibility _ _)

/-- The shift comparison transported through the canonical completion comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalConstructibleScalarCommShift :
    (rationalScalarExtension D l hl E Y L ι).CommShift ℤ :=
  (rationalConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose

/-- The existing completed scalar functor is exact for its specified shift comparison.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated).
Proof: ordinary finite free tensor is exact on sheaves and hence on derived complexes.
Restriction to the constructible full subcategories and rationalization preserve its
image triangles, proving rationalOrdinaryScalar_exact. The normalized natural
isomorphism rationalOrdinaryComparison commutes with the displayed shifts, so its
triangle isomorphisms transport preservation to the published completed functor. -/
theorem rationalConstructibleScalar_exact :
    (rationalScalarExtension D l hl E Y L ι).IsTriangulated := by
  have : NatTrans.CommShift (rationalOrdinaryComparison D l hl E Y L ι).hom ℤ :=
    (rationalConstructibleScalarCommShift_existsUnique D l hl E Y L ι).exists.choose_spec
  have := rationalOrdinaryScalar_isTriangulated D l hl E Y L ι
  exact (Functor.isTriangulated_iff_of_iso (rationalOrdinaryComparison D l hl E Y L ι)).1
    inferInstance

/-- The published scalar functor is additive by its original tensor-Hom specification.
Source: blueprint order 1883 (blueprint: lem-weil-scalar-extension-exact-triangulated). -/
noncomputable instance rationalConstructibleScalar_additive :
    (rationalScalarExtension D l hl E Y L ι).Additive :=
  rationalScalarExtension_additive D l hl E Y L ι

attribute [instance] rationalConstructibleScalar_exact

end WeilConjectures

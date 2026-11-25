/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.ExceptionalCanonicalIntegralScalarShift
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.ExceptionalIntegralAdjunctionLocalizationData
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import WeilConjectures.SixFunctors.Exceptional.ExceptionalCanonicalStageScalarShift

/-! # Normalization of a single scalar localization square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfIntegralConstructible WeilConjectures.sfRationalTriangulationDatum
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry

private theorem map_iso_id_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {U V : C} (e : U ≅ V) (hU : U = V)
    (he : HEq e.hom (𝟙 U)) : HEq (F.map e.hom) (𝟙 (F.obj U)) := by
  subst V
  rw [eq_of_heq he, F.map_id]

private theorem normalized_paste_id {D : Type*} [Category D] {U V W : D}
    (f : U ⟶ V) (g : V ⟶ W) (hU : U = V) (hV : V = W)
    (hf : HEq f (𝟙 U)) (hg : HEq g (𝟙 V)) : HEq (f ≫ g) (𝟙 U) := by
  subst V
  subst W
  rw [eq_of_heq hf, eq_of_heq hg, Category.id_comp]

namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance 2000] shift Shrink.instField
attribute [local instance] constructionInclusionShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem rationalizationShift_eq
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v}) :
    integralRationalizationShift.{u, v} l Ω E T =
      (letI := finiteTorIntegralShift l Ω E T
       inferInstance : (rationalization.{u, v} l Ω E T).CommShift ℤ) := by
  unfold integralRationalizationShift finiteTorIntegralShift
  rfl

/-- The ordinary-realization shift descends to the published canonical rational scalar shift.
Source: Zheng, Construction 6.2; the normalized scalar square in Construction 6.6
(blueprint: lem-sf-canonical-scalar-localization-shift).

Proof: the normalized integral restriction square compares the finite-Tor scalar
functor with the intrinsic integral scalar functor, using their canonical shifts.
The intrinsic scalar localization square compares this functor with rational scalar
extension. Paste the two shift-compatible squares and the associators. Finite-Tor
rationalization is the intrinsic rationalization composed with the full inclusion.
Both squares have identity transport components, so their composite has the stated
normalization. Identity field inclusions and the zero object are included. No geometric
operation or choice of rational operation shifts occurs in this argument. -/
theorem canonical_scalar_localization_shift
    (a b : AlgebraicallyClosedCoefficients.Index l Ω) (h : a ≤ b)
    (T : Scheme.{max u v})
    (S : Scalar.{u, v} l Ω
      (s := .integral (commonField.{u, v} l Ω a))
      (t := .integral (commonField.{u, v} l Ω b))
      (PurCompactSupport.completedChange l
        (commonField.{u, v} l Ω a).carrier (commonField.{u, v} l Ω b).carrier
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h)) T)
    (hS : S.functor ⋙ RingStage.inclusion.{u, v} l Ω T
        (.integral (commonField.{u, v} l Ω b)) =
      RingStage.inclusion.{u, v} l Ω T (.integral (commonField.{u, v} l Ω a)) ⋙
        integralScalarExtensionOfUniverses l
          (commonField.{u, v} l Ω a).carrier (commonField.{u, v} l Ω b).carrier
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h) T)
    (nS : ∀ K, HEq (S.realization.inv.app K)
      ((completedScalarComparison l
        (commonField.{u, v} l Ω a).carrier (commonField.{u, v} l Ω b).carrier
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h) T).app K.obj)) :
    letI : HasShift (C.{u, v} l Ω T (.integral (commonField.{u, v} l Ω a))) ℤ :=
      shift l Ω T (.integral (commonField.{u, v} l Ω a))
    letI : HasShift (C.{u, v} l Ω T (.integral (commonField.{u, v} l Ω b))) ℤ :=
      shift l Ω T (.integral (commonField.{u, v} l Ω b))
    letI := canonicalIntegralScalarShift l Ω S
    letI : (rationalization.{u, v} l Ω (commonField.{u, v} l Ω a) T).CommShift ℤ :=
      integralRationalizationShift.{u, v} l Ω (commonField.{u, v} l Ω a) T
    letI : (rationalization.{u, v} l Ω (commonField.{u, v} l Ω b) T).CommShift ℤ :=
      integralRationalizationShift.{u, v} l Ω (commonField.{u, v} l Ω b) T
    letI : (rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω a)
        (commonField.{u, v} l Ω b)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h) T).CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω T a b h
    ∃ e : rationalization.{u, v} l Ω (commonField.{u, v} l Ω a) T ⋙
        rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω a)
          (commonField.{u, v} l Ω b)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h) T ≅
        S.functor ⋙ rationalization.{u, v} l Ω (commonField.{u, v} l Ω b) T,
      (∀ K, HEq (e.hom.app K)
        (𝟙 ((rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω a)
          (commonField.{u, v} l Ω b)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h) T).obj
            ((rationalization.{u, v} l Ω (commonField.{u, v} l Ω a) T).obj K)))) ∧
      e.hom.CommShift ℤ := by
  let E := commonField.{u, v} l Ω a
  let L := commonField.{u, v} l Ω b
  let i := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h
  let IE := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  let IL := PurCompactSupport.finiteTorIntegralInclusion l L.carrier T
  let QE := sfRationalConstructibleLocalization l E.carrier T
  let QL := sfRationalConstructibleLocalization l L.carrier T
  let SI := GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T a b h
  let R := rationalScalar.{u, v} l Ω E L i T
  letI : HasShift (C.{u, v} l Ω T (.integral E)) ℤ := shift l Ω T (.integral E)
  letI : HasShift (C.{u, v} l Ω T (.integral L)) ℤ := shift l Ω T (.integral L)
  letI : IE.CommShift ℤ := finiteTorIntegralShift l Ω E T
  letI : IL.CommShift ℤ := finiteTorIntegralShift l Ω L T
  letI : S.functor.CommShift ℤ := canonicalIntegralScalarShift l Ω S
  letI : (rationalization.{u, v} l Ω E T).CommShift ℤ :=
    integralRationalizationShift.{u, v} l Ω E T
  letI : (rationalization.{u, v} l Ω L T).CommShift ℤ :=
    integralRationalizationShift.{u, v} l Ω L T
  letI : SI.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω T a b h
  letI : R.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω T a b h
  obtain ⟨eI, heI, hsI⟩ := canonical_integral_scalar_square l Ω a b h T S hS nS
  obtain ⟨eR, heR, hsR⟩ := canonical_stage_scalar_shift l Ω T a b h
  haveI : eI.hom.CommShift ℤ := hsI
  haveI : eR.hom.CommShift ℤ := hsR
  let e : rationalization.{u, v} l Ω E T ⋙ R ≅
      S.functor ⋙ rationalization.{u, v} l Ω L T :=
    Functor.associator IE QE R ≪≫ Functor.isoWhiskerLeft IE eR ≪≫
      (Functor.associator IE SI QL).symm ≪≫ Functor.isoWhiskerRight eI QL ≪≫
      Functor.associator S.functor IL QL
  refine ⟨e, ?_, ?_⟩
  · intro K
    have hU : R.obj (QE.obj (IE.obj K)) = QL.obj (SI.obj (IE.obj K)) :=
      sfRationalScalarExtension_obj l E.carrier T 0
        (Fact.out : l.Prime).ne_zero L.carrier i _
    have hV : SI.obj (IE.obj K) = IL.obj (S.functor.obj K) := by
      apply ObjectProperty.FullSubcategory.ext
      exact (Functor.congr_obj hS K).symm
    simp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    exact normalized_paste_id _ _ hU (congrArg QL.obj hV) (heR (IE.obj K))
      (map_iso_id_heq QL (eI.app K) hV (heI K))
  · -- rewrite the two shift instances while `e` is still folded (small motive); unfolding `e`
    -- first makes the second rewrite's motive check time out at the default heartbeat limit
    rw [rationalizationShift_eq l Ω E T, rationalizationShift_eq l Ω L T]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
    infer_instance

end WeilConjectures.ConstructibleExceptionalCoefficients

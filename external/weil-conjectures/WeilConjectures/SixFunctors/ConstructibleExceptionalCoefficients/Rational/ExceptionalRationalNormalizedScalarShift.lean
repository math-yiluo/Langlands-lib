/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalCommonCoherence
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.ExceptionalIntegralAdjunctionLocalizationData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Canonical.ExceptionalCanonicalScalarLocalizationShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.DeligneLaumon.CompactSupportNormalizedScalarIsomorphisms
import all WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ExceptionalScalarMateLocalization

/-! # The scalar shift square after canonical rational normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfIntegralConstructible WeilConjectures.sfRationalTriangulationDatum
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance 2000] shift Shrink.instField
attribute [local instance] Scalar.commShift Scalar.additive Operation.leftShift
  Operation.rightShift constructionInclusionShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem normalized_q_shift
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ] [HasShift C₄ ℤ]
    [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₃ ℤ] [HasShift D₄ ℤ]
    (IX : C₁ ⥤ D₁) (IY : C₂ ⥤ D₂) (JX : C₃ ⥤ D₃) (JY : C₄ ⥤ D₄)
    [JY.Faithful]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) (SX : C₁ ⥤ C₃) (SY : C₂ ⥤ C₄)
    (H : D₁ ⥤ D₂) (J : D₃ ⥤ D₄) (AX : D₁ ⥤ D₃) (AY : D₂ ⥤ D₄)
    [IX.CommShift ℤ] [IY.CommShift ℤ] [JX.CommShift ℤ] [JY.CommShift ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] [SX.CommShift ℤ] [SY.CommShift ℤ]
    [H.CommShift ℤ] [J.CommShift ℤ] [AX.CommShift ℤ] [AY.CommShift ℤ]
    (rF : F ⋙ IY ≅ IX ⋙ H) (rG : G ⋙ JY ≅ JX ⋙ J)
    (x : SX ⋙ JX ≅ IX ⋙ AX) (y : SY ⋙ JY ≅ IY ⋙ AY)
    (q : F ⋙ SY ≅ SX ⋙ G) (z : H ⋙ AY ⟶ AX ⋙ J)
    [rF.hom.CommShift ℤ] [rG.hom.CommShift ℤ]
    [x.hom.CommShift ℤ] [y.hom.CommShift ℤ] [z.CommShift ℤ]
    (hn : ∀ K, JY.map (q.hom.app K) ≫ rG.hom.app (SX.obj K) ≫
        J.map (x.hom.app K) =
      y.hom.app (F.obj K) ≫ AY.map (rF.hom.app K) ≫ z.app (IX.obj K)) :
    q.hom.CommShift ℤ := by
  let e : (F ⋙ SY) ⋙ JY ⟶ (SX ⋙ G) ⋙ JY :=
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft F y.hom ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight rF.hom AY ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft IX z ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight x.inv J ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft SX rG.inv ≫
      (Functor.associator _ _ _).inv
  have he : (Functor.whiskerRight q.hom JY) = e := by
    ext K
    apply (cancel_mono (rG.hom.app (SX.obj K) ≫ J.map (x.hom.app K))).mp
    simpa [e, Category.assoc, ← Functor.map_comp] using hn K
  haveI : e.CommShift ℤ := by
    dsimp only [e]
    infer_instance
  haveI : (Functor.whiskerRight q.hom JY).CommShift ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight q.hom JY

private theorem normalized_paste
    {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D) (G : E ⥤ D)
    {U V : C} {R S : E} {A B : D}
    (p : U ≅ V) (q : B ≅ G.obj S) (x : R ≅ S) (y : T.obj U ≅ A)
    (a : A ⟶ B) (b : T.obj V ⟶ G.obj R)
    (hU : U = V) (hR : R = S) (hA : T.obj U = A) (hB : B = G.obj S)
    (hp : HEq p.hom (𝟙 U)) (hq : HEq q.hom (𝟙 B))
    (hx : HEq x.hom (𝟙 R)) (hy : HEq y.hom (𝟙 (T.obj U)))
    (hb : HEq b a) :
    b = T.map p.inv ≫ y.hom ≫ a ≫ q.hom ≫ G.map x.inv := by
  subst V
  subst S
  subst A
  subst B
  have hp' : p.hom = 𝟙 U := eq_of_heq hp
  have hq' : q.hom = 𝟙 (G.obj R) := eq_of_heq hq
  have hx' : x.hom = 𝟙 R := eq_of_heq hx
  have hy' : y.hom = 𝟙 (T.obj U) := eq_of_heq hy
  have hpi : p.inv = 𝟙 U := by
    simpa only [hp', Category.id_comp] using p.hom_inv_id
  have hxi : x.inv = 𝟙 R := by
    simpa only [hx', Category.id_comp] using x.hom_inv_id
  rw [hpi, hxi, hq', hy', T.map_id, G.map_id]
  simpa only [Category.id_comp, Category.comp_id] using eq_of_heq hb

private theorem comparison_cast_shift
    {C₁ C₂ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
    {F : C₁ ⥤ C₂} {G : D₁ ⥤ D₂} [F.CommShift ℤ] [G.CommShift ℤ]
    {TX TX' : C₁ ⥤ D₁} {TY TY' : C₂ ⥤ D₂}
    (hx : TX = TX') (hy : TY = TY')
    (sx : TX'.CommShift ℤ) (sy : TY'.CommShift ℤ)
    (q : F ⋙ TY' ≅ TX' ⋙ G)
    (hq : letI := sx; letI := sy; q.hom.CommShift ℤ) :
    letI : TX.CommShift ℤ := cast (congrArg (fun T ↦ T.CommShift ℤ) hx.symm) sx
    letI : TY.CommShift ℤ := cast (congrArg (fun T ↦ T.CommShift ℤ) hy.symm) sy
    (commonComparisonCast hx hy q).hom.CommShift ℤ := by
  cases hx
  cases hy
  exact hq

variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
  (P : RationalStageAssembly.{u, v} l Ω D hl A)

attribute [local instance] constructionInclusionShift

private theorem integral_normalized_comparison_shift
    (c : Compactification f) (E L : FieldStage.{max u v} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) :
    let a := PurCompactSupport.completedChange l E.carrier L.carrier i
    let ha := Allowed.integral E L i
    let SX : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L) a X :=
      A.scalar (s := .integral E) (t := .integral L) a ha true
    let SY : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L) a Y :=
      A.scalar (s := .integral E) (t := .integral L) a ha false
    let q := Scalar.counitQ l Ω SX SY
      (A.comparison c (s := .integral E) (t := .integral L) a ha)
    letI : SX.functor.CommShift ℤ := canonicalIntegralScalarShift l Ω SX
    letI : SY.functor.CommShift ℤ := canonicalIntegralScalarShift l Ω SY
    letI : (A.operation c (.integral E)).F.CommShift ℤ :=
      (A.operation c (.integral E)).leftShift
    letI : (A.operation c (.integral L)).F.CommShift ℤ :=
      (A.operation c (.integral L)).leftShift
    q.hom.CommShift ℤ := by
  let a := PurCompactSupport.completedChange l E.carrier L.carrier i
  let ha := Allowed.integral E L i
  let SX : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L) a X :=
    A.scalar (s := .integral E) (t := .integral L) a ha true
  let SY : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L) a Y :=
    A.scalar (s := .integral E) (t := .integral L) a ha false
  let q := Scalar.counitQ l Ω SX SY
    (A.comparison c (s := .integral E) (t := .integral L) a ha)
  have hn := A.comparison_normalized c (s := .integral E) (t := .integral L) a ha
  letI : SX.functor.CommShift ℤ := canonicalIntegralScalarShift l Ω SX
  letI : SY.functor.CommShift ℤ := canonicalIntegralScalarShift l Ω SY
  letI := canonicalIntegralScalarShift_compatibility l Ω SX
  letI := canonicalIntegralScalarShift_compatibility l Ω SY
  letI := constructionInclusionShift l Ω X (.integral E)
  letI := constructionInclusionShift l Ω Y (.integral E)
  letI := constructionInclusionShift l Ω X (.integral L)
  letI := constructionInclusionShift l Ω Y (.integral L)
  letI : (RingStage.inclusion l Ω Y (.integral L)).Faithful :=
    (finiteTorConstructibleIntegral l L.carrier Y).fullyFaithfulι.faithful
  letI : (A.operation c (.integral E)).F.CommShift ℤ :=
    (A.operation c (.integral E)).leftShift
  letI : (A.operation c (.integral L)).F.CommShift ℤ :=
    (A.operation c (.integral L)).leftShift
  letI := A.leftShift c (.integral E)
  letI := A.leftShift c (.integral L)
  letI := PurCompactSupport.comparison_commShift a c
  exact normalized_q_shift
    (RingStage.inclusion l Ω X (.integral E))
    (RingStage.inclusion l Ω Y (.integral E))
    (RingStage.inclusion l Ω X (.integral L))
    (RingStage.inclusion l Ω Y (.integral L))
    (A.operation c (.integral E)).F (A.operation c (.integral L)).F
    SX.functor SY.functor
    (PurCompactSupport.image ((RingStage.integral E).coefficients l) c)
    (PurCompactSupport.image ((RingStage.integral L).coefficients l) c)
    (pbcDerivedExtend (a.map X)) (pbcDerivedExtend (a.map Y))
    (A.left c (.integral E)) (A.left c (.integral L))
    SX.realization SY.realization q
    (PurCompactSupport.comparison a c) hn

/-- The rational scalar comparison commutes with canonically normalized shifts.
This concerns only one finite coefficient enlargement. It asserts no shift structure,
exactness, or adjunction on the common-field pair categories.
Source: Zheng, Constructions 6.2 and 6.6; common-field exactness proof, step 2
(blueprint: lem-sf-rational-normalized-scalar-shift).

Proof: fix an enlargement i ≤ j and use the integral scalar functors supplied by A.
Their realizations identify them with the completed scalar extensions, including their
shift maps. Indeed the realizations commute with shifts, and the full integral
inclusions reflect the resulting equality. The normalized integral counit comparison
therefore commutes with the canonical scalar shifts. Precompose the desired rational
square with integral rationalization at i. The normalization hs identifies the finite
operation shifts with the localizations of the integral operation shifts. The equation
P.scalar_normalized identifies the rational comparison with the localized integral
comparison, while P.action identifies the operation on each localized integral arrow.
The scalar localization comparisons identify its two scalar sides with the canonical
rational scalar shifts. The precomposed square is consequently the localization of
the integral square. Rationalization is a localization by residue Tor, so natural
transformations out of it are faithful; cancel its invertible shift comparison to
obtain the square on all rational objects. Finally commonStageTransition_eq and
commonComparisonCast transport the scalar functors and this square to the published
stage transitions. This argument applies to every integer shift, including zero and
negative shifts, and to identity coefficient extensions. -/
theorem rational_common_normalized_scalar_shift
    (c : Compactification f)
    (s : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      ((rationalCommonLeft A P c).Φ i).CommShift ℤ)
    (hs : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      let E := commonField.{u, v} l Ω i
      letI : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift l Ω X (.integral E)
      letI : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift l Ω Y (.integral E)
      letI : (A.operation c (.integral E)).F.CommShift ℤ :=
        (A.operation c (.integral E)).leftShift
      letI := integralRationalizationShift.{u, v} l Ω E X
      letI := integralRationalizationShift.{u, v} l Ω E Y
      letI : (P.operation c E).F.CommShift ℤ := s i
      (P.localization c E).q.hom.CommShift ℤ) :
    ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
      letI := s i
      letI := s j
      ((rationalCommonLeft A P c).β h).hom.CommShift ℤ := by
  intro i j h
  let E := commonField.{u, v} l Ω i
  let L := commonField.{u, v} l Ω j
  let inc := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h
  let a := PurCompactSupport.completedChange l E.carrier L.carrier inc
  let ha := Allowed.integral E L inc
  let SX : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L) a X :=
    A.scalar (s := .integral E) (t := .integral L) a ha true
  let SY : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L) a Y :=
    A.scalar (s := .integral E) (t := .integral L) a ha false
  let α := Scalar.counitQ l Ω SX SY
    (A.comparison c (s := .integral E) (t := .integral L) a ha)
  let qE := (P.localization c E).q
  let qL := (P.localization c L).q
  let β := (P.scalar c E L inc).q
  let QX := rationalization.{u, v} l Ω E X
  let QY := rationalization.{u, v} l Ω E Y
  let PX := rationalization.{u, v} l Ω L X
  let PY := rationalization.{u, v} l Ω L Y
  let TX := rationalScalar.{u, v} l Ω E L inc X
  let TY := rationalScalar.{u, v} l Ω E L inc Y
  let FI := (A.operation c (.integral E)).F
  let GI := (A.operation c (.integral L)).F
  let FR := (P.operation c E).F
  let GR := (P.operation c L).F
  letI : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift l Ω X (.integral E)
  letI : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift l Ω Y (.integral E)
  letI : HasShift (C.{u, v} l Ω X (.integral L)) ℤ := shift l Ω X (.integral L)
  letI : HasShift (C.{u, v} l Ω Y (.integral L)) ℤ := shift l Ω Y (.integral L)
  letI : FI.CommShift ℤ := (A.operation c (.integral E)).leftShift
  letI : GI.CommShift ℤ := (A.operation c (.integral L)).leftShift
  letI : SX.functor.CommShift ℤ := canonicalIntegralScalarShift l Ω SX
  letI : SY.functor.CommShift ℤ := canonicalIntegralScalarShift l Ω SY
  letI : QX.CommShift ℤ := integralRationalizationShift l Ω E X
  letI : QY.CommShift ℤ := integralRationalizationShift l Ω E Y
  letI : PX.CommShift ℤ := integralRationalizationShift l Ω L X
  letI : PY.CommShift ℤ := integralRationalizationShift l Ω L Y
  letI : FR.CommShift ℤ := s i
  letI : GR.CommShift ℤ := s j
  letI : TX.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X i j h
  letI : TY.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y i j h
  haveI : α.hom.CommShift ℤ := integral_normalized_comparison_shift l Ω D hl A c E L inc
  haveI : qE.hom.CommShift ℤ := hs i
  haveI : qL.hom.CommShift ℤ := hs j
  obtain ⟨cX, hcX, hcXs⟩ := canonical_scalar_localization_shift l Ω i j h X SX
    (A.integralScalar_eq E L inc true) (A.integralScalar_normalized E L inc true)
  obtain ⟨cY, hcY, hcYs⟩ := canonical_scalar_localization_shift l Ω i j h Y SY
    (A.integralScalar_eq E L inc false) (A.integralScalar_normalized E L inc false)
  letI := hcXs
  letI := hcYs
  let q₀ : QX ⋙ (FR ⋙ TY) ≅ QX ⋙ (TX ⋙ GR) :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight qE.symm TY ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft FI cY ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight α PY ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft SX.functor qL ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight cX.symm GR ≪≫
      Functor.associator _ _ _
  have he : Functor.whiskerLeft QX β.hom = q₀.hom := by
    ext K
    simp only [q₀, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    erw [Category.id_comp]
    exact normalized_paste TY GR (qE.app K) (qL.app (SX.functor.obj K))
      (cX.app K) (cY.app (FI.obj K)) (PY.map (α.hom.app K))
      (β.hom.app (QX.obj K))
      ((P.action c E).1 K).symm
      (Functor.congr_obj (scalar_factor l Ω E L inc X SX.functor
        (A.integralScalar_eq E L inc true)) K)
      (Functor.congr_obj (scalar_factor l Ω E L inc Y SY.functor
        (A.integralScalar_eq E L inc false)) (FI.obj K))
      ((P.action c L).1 (SX.functor.obj K)).symm
      (P.identity c E K) (P.identity c L (SX.functor.obj K))
      (hcX K) (hcY (FI.obj K)) (P.scalar_normalized c E L inc K)
  haveI : q₀.hom.CommShift ℤ := by
    dsimp only [q₀, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom]
    infer_instance
  haveI : (Functor.whiskerLeft QX β.hom).CommShift ℤ := by
    rw [he]
    infer_instance
  letI : ∀ x : X, Invertible (l : X.residueField x) :=
    sfCompactSupportScalarResidueUnit l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) X
  let WX := (MorphismProperty.isomorphisms _).inverseImage QX
  haveI : QX.IsLocalization WX := rationalization_isLocalization l Ω E X
    (integral_residue_tor D l hl E.carrier X).2
  have hβ : β.hom.CommShift ℤ := shift_of_whisker QX WX β.hom
  have hx := commonStageTransition_eq l Ω X h
  have hy := commonStageTransition_eq l Ω Y h
  have hc := comparison_cast_shift (F := FR) (G := GR) hx hy
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X i j h)
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y i j h) β hβ
  dsimp only [E, L, FR, GR, β, hx, hy, inc,
    GeneralAlgebraicallyClosedCoefficients.stageCategory, C, category, commonField] at hc
  exact hc

end WeilConjectures.ConstructibleExceptionalCoefficients

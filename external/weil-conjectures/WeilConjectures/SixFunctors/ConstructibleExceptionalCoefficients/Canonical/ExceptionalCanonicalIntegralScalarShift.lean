/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SixFunctors.Exceptional.ExceptionalOrdinaryCompletedScalarShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-! # The normalized integral scalar restriction square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem full_hom_heq {D : Type*} [Category D] {P : ObjectProperty D}
    {A B A' B' : P.FullSubcategory} (ha : A.obj = A'.obj) (hb : B.obj = B'.obj)
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f.hom g.hom) : HEq f g := by
  have ea : A = A' := ObjectProperty.FullSubcategory.ext ha
  have eb : B = B' := ObjectProperty.FullSubcategory.ext hb
  subst A'
  subst B'
  exact heq_of_eq (ObjectProperty.hom_ext _ (eq_of_heq h))

private theorem normalized_realization_cancel
    {D : Type*} [Category D] {U V V' W : D}
    (r : U ≅ V) (e : U ≅ W) (θ : V' ≅ W) (t : V ⟶ V') (χ : W ⟶ V)
    (hV : V = V') (hθ : HEq θ.inv χ) (he : e.hom ≫ χ = r.hom)
    (ht : t ≫ θ.hom = r.inv ≫ e.hom) : HEq t (𝟙 V) := by
  subst V'
  have hθ' : θ.inv = χ := eq_of_heq hθ
  apply heq_of_eq
  apply (cancel_mono θ.hom).mp
  rw [ht, Category.id_comp]
  apply (cancel_epi r.hom).mp
  rw [Iso.hom_inv_id_assoc, ← he, ← hθ', Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem remove_paste_identities
    {C D : Type*} [Category C] [Category D] (O : C ⥤ D)
    {A V W : D} {U : C} (f : A ⟶ V) (g : V ⟶ W)
    (a : A ⟶ O.obj U) (b : O.obj U ⟶ W)
    (h : f ≫ 𝟙 V ≫ g = a ≫ O.map (𝟙 U) ≫ b) : f ≫ g = a ≫ b := by
  simpa only [Category.id_comp, O.map_id] using h

private theorem restriction_iso
    {C₁ C₂ C₃ C₄ D₁ D₂ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂]
    [sC1 : HasShift C₁ ℤ] [sC2 : HasShift C₂ ℤ]
    [sC3 : HasShift C₃ ℤ] [sC4 : HasShift C₄ ℤ]
    [HasShift D₁ ℤ] [HasShift D₂ ℤ]
    (IX : C₁ ⥤ D₁) (IY : C₂ ⥤ D₁) (JX : C₃ ⥤ D₂) (JY : C₄ ⥤ D₂)
    (IE : C₁ ⥤ C₂) (IL : C₃ ⥤ C₄) (S : C₁ ⥤ C₃) (SI : C₂ ⥤ C₄)
    (O B : D₁ ⥤ D₂)
    [sIX : IX.CommShift ℤ] [sIY : IY.CommShift ℤ] [sJX : JX.CommShift ℤ] [sJY : JY.CommShift ℤ]
    [sIE : IE.CommShift ℤ] [sIL : IL.CommShift ℤ] [sS : S.CommShift ℤ] [sSI : SI.CommShift ℤ]
    [sO : O.CommShift ℤ] [sB : B.CommShift ℤ] [fullJY : JY.Full] [faithfulJY : JY.Faithful]
    (rF : IE ⋙ IY ≅ IX) (rG : IL ⋙ JY ≅ JX)
    (χ : IY ⋙ O ≅ SI ⋙ JY) (θ : S ⋙ JX ≅ IX ⋙ B) (eO : O ≅ B)
    [hRF : rF.hom.CommShift ℤ] [hRG : rG.hom.CommShift ℤ]
    [hChi : χ.hom.CommShift ℤ] [hTheta : θ.hom.CommShift ℤ]
    [hOrd : eO.hom.CommShift ℤ]
    : ∃ e : IE ⋙ SI ≅ S ⋙ IL, e.hom.CommShift ℤ ∧
      ∀ K, JY.map (e.hom.app K) ≫ rG.hom.app (S.obj K) ≫ θ.hom.app K =
        χ.inv.app (IE.obj K) ≫ O.map (rF.hom.app K) ≫ eO.hom.app (IX.obj K) := by
  let t : (IE ⋙ SI) ⋙ JY ≅ (S ⋙ IL) ⋙ JY :=
    Functor.associator IE SI JY ≪≫ Functor.isoWhiskerLeft IE χ.symm ≪≫
      (Functor.associator IE IY O).symm ≪≫ Functor.isoWhiskerRight rF O ≪≫
      Functor.isoWhiskerLeft IX eO ≪≫ θ.symm ≪≫
      Functor.isoWhiskerLeft S rG.symm ≪≫ (Functor.associator S IL JY).symm
  let e := Functor.fullyFaithfulCancelRight JY t
  have ht : Functor.whiskerRight e.hom JY = t.hom := by
    ext K
    simp only [e, Functor.whiskerRight_app, Functor.fullyFaithfulCancelRight_hom_app,
      Functor.map_preimage]
  refine ⟨e, ?_, ?_⟩
  · haveI : t.hom.CommShift ℤ := by
      dsimp only [t, Iso.trans_hom, Iso.symm_hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
      infer_instance
    haveI : (Functor.whiskerRight e.hom JY).CommShift ℤ := by rw [ht]; infer_instance
    exact NatTrans.CommShift.of_whiskerRight e.hom JY
  · intro K
    have h := congr_app ht K
    simpa [t, Category.assoc] using
      congrArg (fun f ↦ f ≫ rG.hom.app (S.obj K) ≫ θ.hom.app K) h

attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfRationalTriangulationDatum
  WeilConjectures.completedCoefficientMap WeilConjectures.completedScalarChangeData
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
section ScalarNormalization
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})

private def ordinaryComparison :
    (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι W ⋙ (sfIntegralConstructible l L W).ι :=
  sfIntegralOrdinaryComparison l E L ι W

end ScalarNormalization

private theorem ordinaryComparison_shift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (W : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L) :
    letI : (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω W E L h
    NatTrans.CommShift (ordinaryComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).hom ℤ := by
  constructor
  intro n
  ext K
  have hn := (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
    l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) W).exists.choose_spec n K
  have hn' := eq_of_heq hn
  change _ = (ordinaryComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).inv.app (K⟦n⟧) ≫
      (((sfIntegralConstructible l (Coefficient.{u} l Ω E) W).ι ⋙
        integralOrdinaryDerivedScalar l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W).commShiftIso n).hom.app K ≫
      (shiftFunctor (DerivedCategory (integralTowerModules l (Coefficient.{u} l Ω L) W)) n).map
        ((ordinaryComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) W).hom.app K) at hn'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc, ObjectProperty.ι_map]
  change _ = (ordinaryComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W).hom.app (K⟦n⟧) ≫ _
  rw [← Category.assoc, hn']
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]

end WeilConjectures

attribute [local irreducible] WeilConjectures.finiteTorConstructibleIntegral
  WeilConjectures.sfIntegralConstructible
  Functor.CommShift.ofComp

namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance 2000] Shrink.instField
attribute [local instance 5000] integralTowerHasDerivedCategory
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The finite-Tor inclusion carries the shift lifted from its full realization.
Source: inherited shifts on full coefficient subcategories
(blueprint: lem-sf-canonical-integral-scalar-square). -/
@[irreducible]
def finiteTorIntegralShift (E : FieldStage.{max u v} l) (T : Scheme.{max u v}) :
    letI : HasShift (C.{u, v} l Ω T (.integral E)) ℤ := shift l Ω T (.integral E)
    (PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).CommShift ℤ := by
  letI : HasShift (C.{u, v} l Ω T (.integral E)) ℤ := shift l Ω T (.integral E)
  letI := constructionInclusionShift l Ω T (.integral E)
  exact Functor.CommShift.ofComp
    (show PurCompactSupport.finiteTorIntegralInclusion l E.carrier T ⋙
      (sfIntegralConstructible l E.carrier T).ι ≅
        RingStage.inclusion.{u, v} l Ω T (.integral E) from Iso.refl _) ℤ

/-- The finite-Tor inclusion shift preserves its ambient realization.
Source: full-subcategory shift lifting
(blueprint: lem-sf-canonical-integral-scalar-square). -/
theorem finiteTorIntegralShift_compatibility
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v}) :
    letI : HasShift (C.{u, v} l Ω T (.integral E)) ℤ := shift l Ω T (.integral E)
    letI := constructionInclusionShift l Ω T (.integral E)
    letI := finiteTorIntegralShift l Ω E T
    NatTrans.CommShift (show PurCompactSupport.finiteTorIntegralInclusion l E.carrier T ⋙
      (sfIntegralConstructible l E.carrier T).ι ≅
        RingStage.inclusion.{u, v} l Ω T (.integral E) from Iso.refl _).hom ℤ := by
  letI : HasShift (C.{u, v} l Ω T (.integral E)) ℤ := shift l Ω T (.integral E)
  letI := constructionInclusionShift l Ω T (.integral E)
  have hc := Functor.CommShift.ofComp_compatibility
    (show PurCompactSupport.finiteTorIntegralInclusion l E.carrier T ⋙
      (sfIntegralConstructible l E.carrier T).ι ≅
        RingStage.inclusion.{u, v} l Ω T (.integral E) from Iso.refl _) ℤ
  unfold finiteTorIntegralShift
  exact hc

/-- The shift on an integral scalar functor induced by its specified ordinary realization.
This is an actual fully faithful lift of the ambient scalar shift, independent of any
shift stored in the scalar record. Source: Zheng, Construction 6.2, and the canonical
completed scalar comparison (blueprint: lem-sf-canonical-integral-scalar-square). -/
@[irreducible]
def canonicalIntegralScalarShift
    {E L : FieldStage.{max u v} l} {i : E.carrier →ₐ[Padic l] L.carrier}
    {T : Scheme.{max u v}}
    (S : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) T) :
    S.functor.CommShift ℤ :=
by
  letI : (RingStage.inclusion.{u, v} l Ω T (.integral L)).Full :=
    (finiteTorConstructibleIntegral l L.carrier T).fullyFaithfulι.full
  letI : (RingStage.inclusion.{u, v} l Ω T (.integral L)).Faithful :=
    (finiteTorConstructibleIntegral l L.carrier T).fullyFaithfulι.faithful
  letI := constructionInclusionShift l Ω T (.integral E)
  letI := constructionInclusionShift l Ω T (.integral L)
  letI : (AlgebraicGeometry.Scheme.pbcDerivedExtend
      ((PurCompactSupport.completedChange l E.carrier L.carrier i).map T)).CommShift ℤ :=
    PurCompactSupport.scalarCommShift _
  exact Functor.CommShift.ofComp S.realization ℤ

/-- The ordinary realization preserves its induced shift.
Source: full-faithful shift lifting (blueprint: lem-sf-canonical-integral-scalar-square). -/
theorem canonicalIntegralScalarShift_compatibility
    {E L : FieldStage.{max u v} l} {i : E.carrier →ₐ[Padic l] L.carrier}
    {T : Scheme.{max u v}}
    (S : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) T) :
    letI := constructionInclusionShift l Ω T (.integral E)
    letI := constructionInclusionShift l Ω T (.integral L)
    letI := canonicalIntegralScalarShift l Ω S
    S.realization.hom.CommShift ℤ := by
  letI : (RingStage.inclusion.{u, v} l Ω T (.integral L)).Full :=
    (finiteTorConstructibleIntegral l L.carrier T).fullyFaithfulι.full
  letI : (RingStage.inclusion.{u, v} l Ω T (.integral L)).Faithful :=
    (finiteTorConstructibleIntegral l L.carrier T).fullyFaithfulι.faithful
  letI := constructionInclusionShift l Ω T (.integral E)
  letI := constructionInclusionShift l Ω T (.integral L)
  letI : (AlgebraicGeometry.Scheme.pbcDerivedExtend
      ((PurCompactSupport.completedChange l E.carrier L.carrier i).map T)).CommShift ℤ :=
    PurCompactSupport.scalarCommShift _
  have hc := Functor.CommShift.ofComp_compatibility S.realization ℤ
  unfold canonicalIntegralScalarShift
  exact hc

/-- The normalized finite-Tor scalar functor embeds with the canonical intrinsic scalar shift.
Source: Zheng, Construction 6.2, and the ordinary completed scalar comparison
(blueprint: lem-sf-canonical-integral-scalar-square).

Proof: paste the shift-compatible ordinary-model comparison, intrinsic completion comparison,
and supplied scalar realization, then lift through the fully faithful intrinsic inclusion.
Faithfulness reflects the shift equation. The object part of the ambient functor equality,
the realization normalization and the completion identity identify each lifted component
with identity transport. -/
theorem canonical_integral_scalar_square
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
    let E := commonField.{u, v} l Ω a
    let L := commonField.{u, v} l Ω b
    let IE := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
    let IL := PurCompactSupport.finiteTorIntegralInclusion l L.carrier T
    letI : HasShift (C.{u, v} l Ω T (.integral E)) ℤ := shift l Ω T (.integral E)
    letI : HasShift (C.{u, v} l Ω T (.integral L)) ℤ := shift l Ω T (.integral L)
    letI : IE.CommShift ℤ := finiteTorIntegralShift l Ω E T
    letI : IL.CommShift ℤ := finiteTorIntegralShift l Ω L T
    letI := canonicalIntegralScalarShift l Ω S
    let SI := GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T a b h
    letI : SI.CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω T a b h
    ∃ e : IE ⋙ SI ≅ S.functor ⋙ IL,
      (∀ K, HEq (e.hom.app K) (𝟙 ((IE ⋙ SI).obj K))) ∧ e.hom.CommShift ℤ := by
  let E := commonField.{u, v} l Ω a
  let L := commonField.{u, v} l Ω b
  let i := AlgebraicallyClosedCoefficients.coefficientInclusion l Ω a b h
  let IE := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  let IL := PurCompactSupport.finiteTorIntegralInclusion l L.carrier T
  let IX := RingStage.inclusion.{u, v} l Ω T (.integral E)
  let JX := RingStage.inclusion.{u, v} l Ω T (.integral L)
  let IY := (sfIntegralConstructible l E.carrier T).ι
  let JY := (sfIntegralConstructible l L.carrier T).ι
  let SI := GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T a b h
  let O := integralOrdinaryDerivedScalar l E.carrier L.carrier i T
  let B := AlgebraicGeometry.Scheme.pbcDerivedExtend
    ((PurCompactSupport.completedChange l E.carrier L.carrier i).map T)
  letI sE : HasShift (C.{u, v} l Ω T (.integral E)) ℤ := shift l Ω T (.integral E)
  letI sL : HasShift (C.{u, v} l Ω T (.integral L)) ℤ := shift l Ω T (.integral L)
  letI siE : HasShift (sfIntegralConstructibleCategory l E.carrier T) ℤ :=
    ObjectProperty.hasShift (sfIntegralConstructible l E.carrier T) (A := ℤ)
  letI siL : HasShift (sfIntegralConstructibleCategory l L.carrier T) ℤ :=
    ObjectProperty.hasShift (sfIntegralConstructible l L.carrier T) (A := ℤ)
  letI iyShift : IY.CommShift ℤ :=
    ObjectProperty.commShiftι (sfIntegralConstructible l E.carrier T) (A := ℤ)
  letI jyShift : JY.CommShift ℤ :=
    ObjectProperty.commShiftι (sfIntegralConstructible l L.carrier T) (A := ℤ)
  letI ixShift : IX.CommShift ℤ := constructionInclusionShift l Ω T (.integral E)
  letI jxShift : JX.CommShift ℤ := constructionInclusionShift l Ω T (.integral L)
  letI ieShift : IE.CommShift ℤ := finiteTorIntegralShift l Ω E T
  letI ilShift : IL.CommShift ℤ := finiteTorIntegralShift l Ω L T
  letI sShift : S.functor.CommShift ℤ := canonicalIntegralScalarShift l Ω S
  letI siShift : SI.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω T a b h
  letI bShift : B.CommShift ℤ := PurCompactSupport.scalarCommShift
    ((PurCompactSupport.completedChange l E.carrier L.carrier i).map T)
  let θ : S.functor ⋙ JX ≅ IX ⋙ B := S.realization
  letI := canonicalIntegralScalarShift_compatibility l Ω S
  let ordinaryData := ordinary_completed_scalar_shift l E.carrier L.carrier i T
  let e₀ := ordinaryData.choose
  have hχ := ordinaryData.choose_spec.1
  have heO := ordinaryData.choose_spec.2
  let eO := e₀
  let χ : IY ⋙ O ≅ SI ⋙ JY :=
    sfIntegralOrdinaryComparison l E.carrier L.carrier i T
  letI chiShift : χ.hom.CommShift ℤ := ordinaryComparison_shift l Ω T a b h
  let rF : IE ⋙ IY ≅ IX := Iso.refl _
  let rG : IL ⋙ JY ≅ JX := Iso.refl _
  letI := finiteTorIntegralShift_compatibility l Ω E T
  letI := finiteTorIntegralShift_compatibility l Ω L T
  have restrictionData := restriction_iso IX IY JX JY IE IL S.functor SI O B
    (C₁ := C.{u, v} l Ω T (.integral E))
    (C₂ := sfIntegralConstructibleCategory l E.carrier T)
    (C₃ := C.{u, v} l Ω T (.integral L))
    (C₄ := sfIntegralConstructibleCategory l L.carrier T)
    (sC1 := sE) (sC2 := siE) (sC3 := sL) (sC4 := siL)
    (sIX := ixShift) (sIY := iyShift) (sJX := jxShift) (sJY := jyShift)
    (sIE := ieShift) (sIL := ilShift) (sS := sShift) (sSI := siShift) (sB := bShift)
    (sO := CategoryTheory.Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt
      (integralOrdinaryScalar l E.carrier L.carrier i T))
    (fullJY := (sfIntegralConstructible l L.carrier T).fullyFaithfulι.full)
    (faithfulJY := (sfIntegralConstructible l L.carrier T).fullyFaithfulι.faithful)
    rF rG χ θ eO (hOrd := heO)
  obtain ⟨e, hs, he⟩ := restrictionData
  refine ⟨e, ?_, hs⟩
  intro K
  have hV : SI.obj (IE.obj K) = IL.obj (S.functor.obj K) := by
    apply ObjectProperty.FullSubcategory.ext
    exact (Functor.congr_obj hS K).symm
  have ht : JY.map (e.hom.app K) ≫ θ.hom.app K =
      χ.inv.app (IE.obj K) ≫ eO.hom.app (IX.obj K) := by
    exact remove_paste_identities O (JY.map (e.hom.app K)) (θ.hom.app K)
      (χ.inv.app (IE.obj K)) (eO.hom.app (IX.obj K)) (he K)
  have hn := normalized_realization_cancel (χ.app (IE.obj K)) (eO.app K.obj)
    (θ.app K) (JY.map (e.hom.app K))
    ((intrinsicScalarCompletion l E.carrier L.carrier i T).app (IE.obj K))
    (congrArg JY.obj hV)
    ((nS K).trans (intrinsicScalarCompletion_app_heq l E.carrier L.carrier i T (IE.obj K)).symm)
    (intrinsicScalarCompletion_paste l E.carrier L.carrier i T eO hχ (IE.obj K)) ht
  exact full_hom_heq rfl (congrArg JY.obj hV).symm hn

end WeilConjectures.ConstructibleExceptionalCoefficients

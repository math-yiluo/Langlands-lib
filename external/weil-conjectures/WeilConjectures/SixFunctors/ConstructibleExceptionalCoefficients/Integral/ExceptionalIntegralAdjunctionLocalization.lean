/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.ExceptionalIntegralAdjunctionLocalizationData
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Raw localization of one integral linear adjunction

Source: Zheng, Construction 6.2, localization of the integral coefficient category.
The functors below are actual tensor extensions, with no choice of object or arrow maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfIntegralConstructible WeilConjectures.sfRationalTriangulationDatum
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v w
open CategoryTheory AlgebraicGeometry TensorProduct
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (E : FieldStage.{max u v} l) (X Y : Scheme.{max u v})

variable {X Y}

private def integralRepresentativeEquivalence (T : Scheme.{max u v})
    (h : sfIntegralConstructible l E.carrier T = finiteTorConstructibleIntegral l E.carrier T) :
    sfIntegralConstructibleCategory l E.carrier T ≌ C.{u, v} l Ω T (.integral E) where
  functor := integralRepresentative l Ω E T h
  inverse := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  unitIso := NatIso.ofComponents
    (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents
    (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp K := by
    apply ObjectProperty.hom_ext
    change 𝟙 K.obj ≫ 𝟙 K.obj = 𝟙 K.obj
    exact Category.id_comp _

private theorem localizedCounit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (TX : C ⥤ C') (WX : MorphismProperty C) [TX.IsLocalization WX]
    (TY : D ⥤ D') (WY : MorphismProperty D) [TY.IsLocalization WY]
    (Fq : C' ⥤ D') (Gq : D' ⥤ C')
    [CatCommSq F TX TY Fq] [CatCommSq G TY TX Gq] (M : D) :
    (CatCommSq.iso F TX TY Fq).hom.app (G.obj M) ≫
      Fq.map ((CatCommSq.iso G TY TX Gq).hom.app M) ≫
      (adj.localization TX WX TY WY Fq Gq).counit.app (TY.obj M) =
        TY.map (adj.counit.app M) := by
  rw [Adjunction.localization_counit_app]
  rw [← Fq.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [Fq.map_id (TX.obj (G.obj M))]
  rw [Category.id_comp, Iso.hom_inv_id_app_assoc]

section AbstractLocalization
variable {C₁ C₂ D₁ D₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  [Limits.HasZeroObject C₁] [Limits.HasZeroObject C₂]
  [Limits.HasZeroObject D₁] [Limits.HasZeroObject D₂]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D₁] [Preadditive D₂]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [∀ n : ℤ, (shiftFunctor D₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂]
  [Pretriangulated D₁] [Pretriangulated D₂]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : F ⊣ G) [F.CommShift ℤ]
  (TX : C₁ ⥤ D₁) (TY : C₂ ⥤ D₂) [TX.CommShift ℤ] [TY.CommShift ℤ]
  (Fq : D₁ ⥤ D₂) (Gq : D₂ ⥤ D₁)
  (q : F ⋙ TY ≅ TX ⋙ Fq) (b : G ⋙ TX ≅ TY ⋙ Gq)

private structure ExactLocalization where
  adjunction : Fq ⊣ Gq
  leftShift : Fq.CommShift ℤ
  rightShift : Gq.CommShift ℤ
  leftExact : letI := leftShift; Fq.IsTriangulated
  rightExact : letI := rightShift; Gq.IsTriangulated
  unitShift : letI := leftShift; letI := rightShift; adjunction.unit.CommShift ℤ
  counitShift : letI := leftShift; letI := rightShift; adjunction.counit.CommShift ℤ
  comparisonShift : letI := leftShift; q.hom.CommShift ℤ
  counit (M : C₂) : q.hom.app (G.obj M) ≫ Fq.map (b.hom.app M) ≫
    adjunction.counit.app (TY.obj M) = TY.map (adj.counit.app M)

variable (WX : MorphismProperty C₁) [TX.IsLocalization WX]
  (WY : MorphismProperty C₂) [TY.IsLocalization WY]
  [TX.IsTriangulated] [TY.IsTriangulated] [TX.mapArrow.EssSurj] [F.IsTriangulated]

private def exactLocalization : ExactLocalization adj TX TY Fq Gq q b := by
  let : Localization.Lifting TX WX (F ⋙ TY) Fq := ⟨q.symm⟩
  let : Fq.CommShift ℤ := Functor.commShiftOfLocalization TX WX ℤ (F ⋙ TY) Fq
  have : NatTrans.CommShift q.symm.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization TX WX ℤ (F ⋙ TY) Fq
  have hq : NatTrans.CommShift q.hom ℤ := NatTrans.CommShift.of_iso_inv q.symm ℤ
  have : Fq.IsTriangulated := Functor.isTriangulated_of_precomp_iso q.symm
  let : CatCommSq F TX TY Fq := ⟨q⟩
  let : CatCommSq G TY TX Gq := ⟨b⟩
  let aq := adj.localization TX WX TY WY Fq Gq
  let : Gq.CommShift ℤ := aq.rightAdjointCommShift ℤ
  have : aq.CommShift ℤ := aq.commShift_of_leftAdjoint ℤ
  exact {
    adjunction := aq
    leftShift := inferInstance
    rightShift := inferInstance
    leftExact := inferInstance
    rightExact := aq.isTriangulated_rightAdjoint
    unitShift := inferInstance
    counitShift := inferInstance
    comparisonShift := hq
    counit := localizedCounit adj TX WX TY WY Fq Gq }
end AbstractLocalization

private theorem mate_shift
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (adj : F ⊣ G) (adj' : F' ⊣ G')
    [F.CommShift ℤ] [G.CommShift ℤ] [F'.CommShift ℤ] [G'.CommShift ℤ]
    [adj.CommShift ℤ] [adj'.CommShift ℤ]
    (TX : C ⥤ C') (TY : D ⥤ D') [TX.CommShift ℤ] [TY.CommShift ℤ]
    (q : F ⋙ TY ≅ TX ⋙ F') (b : G ⋙ TX ⟶ TY ⋙ G')
    [NatTrans.CommShift q.hom ℤ]
    (hc : ∀ L, q.hom.app (G.obj L) ≫ F'.map (b.app L) ≫
      adj'.counit.app (TY.obj L) = TY.map (adj.counit.app L)) :
    NatTrans.CommShift b ℤ := by
  let m := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ q.inv))
  have hm : NatTrans.CommShift m ℤ := by
    dsimp [m, mateEquiv]
    infer_instance
  have hb : b = m := by
    ext L
    apply (adj'.homEquiv _ _).symm.injective
    change F'.map (b.app L) ≫ adj'.counit.app _ =
      F'.map (m.app L) ≫ adj'.counit.app _
    rw [mateEquiv_counit]
    apply (cancel_epi (q.hom.app (G.obj L))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hc L
  rw [hb]
  exact hm

private theorem rawRationalComparisonHom
    (F : C.{u, v} l Ω X (.integral E) ⥤ C.{u, v} l Ω Y (.integral E))
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (K : C.{u, v} l Ω X (.integral E)) :
    HEq ((rawRationalComparison l Ω E F hX).hom.app K)
      (𝟙 ((rationalization.{u, v} l Ω E Y).obj (F.obj K))) := by
  exact heq_of_eq rfl

attribute [local irreducible] rawRationalFunctor rawRationalComparison

private theorem integralLocalization (E : FieldStage.{w} l) (T : Scheme.{w}) :
    (sfRationalConstructibleLocalization l E.carrier T).IsLocalization
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E.carrier))
        (sfIntegralConstructibleCategory l E.carrier T)) := by
  have : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l E.carrier T) n).Linear
      (Padic.coefficientExtensionIntegers l E.carrier) :=
    CategoryTheory.ScalarLocalization.semilinear_all_shift_linear _ _
  exact CategoryTheory.ScalarLocalization.semilinear_localization_isLocalization _ _ _

private theorem rationalizationLocalization (T : Scheme.{max u v})
    (h : sfIntegralConstructible l E.carrier T = finiteTorConstructibleIntegral l E.carrier T) :
    (rationalization.{u, v} l Ω E T).IsLocalization
      ((Rationalization.W (Submonoid.powers
        (Padic.coefficientExtensionUniformizer l E.carrier))
          (sfIntegralConstructibleCategory l E.carrier T)).inverseImage
            (PurCompactSupport.finiteTorIntegralInclusion l E.carrier T)) := by
  let Q := sfRationalConstructibleLocalization l E.carrier T
  let W := Rationalization.W (Submonoid.powers
    (Padic.coefficientExtensionUniformizer l E.carrier))
      (sfIntegralConstructibleCategory l E.carrier T)
  let j := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  have : Q.IsLocalization W := integralLocalization l E T
  apply Functor.IsLocalization.of_equivalence_source Q W (j ⋙ Q) (W.inverseImage j)
    (integralRepresentativeEquivalence l Ω E T h)
  · intro K L f hf
    exact MorphismProperty.le_isoClosure _ _ hf
  · intro K L f hf
    exact Localization.inverts Q W (j.map f) hf
  · exact Iso.refl _

private theorem rationalizationExact (T : Scheme.{max u v}) :
    letI := integralRationalizationShift.{u, v} l Ω E T
    (rationalization.{u, v} l Ω E T).IsTriangulated := by
  let j := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  let e : j ⋙ (sfIntegralConstructible l E.carrier T).ι ≅
      (finiteTorConstructibleIntegral l E.carrier T).ι := Iso.refl _
  let : j.CommShift ℤ := Functor.CommShift.ofComp e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  have : j.IsTriangulated := (Functor.isTriangulated_iff_comp_right e).2 inferInstance
  exact (inferInstance : (j ⋙ sfRationalConstructibleLocalization l E.carrier T).IsTriangulated)

private theorem rationalizationArrowEssSurj (T : Scheme.{max u v})
    (h : sfIntegralConstructible l E.carrier T = finiteTorConstructibleIntegral l E.carrier T) :
    (rationalization.{u, v} l Ω E T).mapArrow.EssSurj := by
  let Q := sfRationalConstructibleLocalization l E.carrier T
  let W := Rationalization.W (Submonoid.powers
    (Padic.coefficientExtensionUniformizer l E.carrier))
      (sfIntegralConstructibleCategory l E.carrier T)
  have : Q.IsLocalization W := integralLocalization l E T
  have : Q.mapArrow.EssSurj := Localization.essSurj_mapArrow Q W
  have : (PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).IsEquivalence :=
    (integralRepresentativeEquivalence l Ω E T h).symm.isEquivalence_functor
  exact (inferInstance : ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).mapArrow ⋙
    Q.mapArrow).EssSurj)

attribute [local irreducible] integralRationalizationShift

private theorem exists_normalized_raw_core
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y) :
    ∃ R : RawLocalizedAdjunction l Ω E X Y A hX hY,
      (∀ M, (rawRationalComparison l Ω E A.F hX).hom.app (A.G.obj M) ≫
        (rawRationalFunctor l Ω E X Y A.F hX).map
          ((rawRationalComparison l Ω E A.G hY).hom.app M) ≫
        R.adjunction.counit.app ((rationalization.{u, v} l Ω E Y).obj M) =
          (rationalization.{u, v} l Ω E Y).map (A.adjunction.counit.app M)) ∧
      (letI := integralRationalizationShift l Ω E X
       letI := integralRationalizationShift l Ω E Y
       letI := A.leftShift
       letI := R.leftShift
       NatTrans.CommShift (rawRationalComparison l Ω E A.F hX).hom ℤ) := by
  let TX := rationalization.{u, v} l Ω E X
  let TY := rationalization.{u, v} l Ω E Y
  let WX := (Rationalization.W (Submonoid.powers
    (Padic.coefficientExtensionUniformizer l E.carrier))
      (sfIntegralConstructibleCategory l E.carrier X)).inverseImage
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
  let WY := (Rationalization.W (Submonoid.powers
    (Padic.coefficientExtensionUniformizer l E.carrier))
      (sfIntegralConstructibleCategory l E.carrier Y)).inverseImage
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y)
  have : TX.IsLocalization WX := rationalizationLocalization l Ω E X hX
  have : TY.IsLocalization WY := rationalizationLocalization l Ω E Y hY
  let : TX.CommShift ℤ := integralRationalizationShift l Ω E X
  let : TY.CommShift ℤ := integralRationalizationShift l Ω E Y
  have : TX.IsTriangulated := rationalizationExact l Ω E X
  have : TY.IsTriangulated := rationalizationExact l Ω E Y
  have : TX.mapArrow.EssSurj := rationalizationArrowEssSurj l Ω E X hX
  let : A.F.CommShift ℤ := A.leftShift
  let : A.G.CommShift ℤ := A.rightShift
  have : A.F.IsTriangulated := A.leftExact
  let Fq := rawRationalFunctor l Ω E X Y A.F hX
  let Gq := rawRationalFunctor l Ω E Y X A.G hY
  let q : A.F ⋙ TY ≅ TX ⋙ Fq := rawRationalComparison l Ω E A.F hX
  let b : A.G ⋙ TX ≅ TY ⋙ Gq := rawRationalComparison l Ω E A.G hY
  let P := exactLocalization A.adjunction TX TY Fq Gq q b WX WY
  let R : RawLocalizedAdjunction l Ω E X Y A hX hY := {
    adjunction := P.adjunction
    leftShift := P.leftShift
    rightShift := P.rightShift
    leftExact := P.leftExact
    rightExact := P.rightExact
    unitShift := P.unitShift
    counitShift := P.counitShift }
  exact ⟨R, P.counit, P.comparisonShift⟩

set_option linter.unusedVariables false in
/-- The localized adjunction admits the identity normalized coefficient comparison.
Source: Zheng, Construction 6.2, normalization after scalar localization
(blueprint: lem-sf-integral-adjunction-raw-localization-identity).
The adjunction's counit and left shift comparison are normalized explicitly; an arbitrary
adjunction structure on the raw functors does not satisfy this assertion. -/
theorem exists_raw_localized_identity_comparison
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y)
    (R : RawLocalizedAdjunction l Ω E X Y A hX hY)
    (hc : ∀ M, (rawRationalComparison l Ω E A.F hX).hom.app (A.G.obj M) ≫
      (rawRationalFunctor l Ω E X Y A.F hX).map
        ((rawRationalComparison l Ω E A.G hY).hom.app M) ≫
      R.adjunction.counit.app ((rationalization.{u, v} l Ω E Y).obj M) =
        (rationalization.{u, v} l Ω E Y).map (A.adjunction.counit.app M))
    (hq : letI := integralRationalizationShift l Ω E X
          letI := integralRationalizationShift l Ω E Y
          letI := A.leftShift
          letI := R.leftShift
          NatTrans.CommShift (rawRationalComparison l Ω E A.F hX).hom ℤ) :
    ∃ (q : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E)
        (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)),
      (∀ K, HEq (q.q.hom.app K)
        (𝟙 ((rationalization.{u, v} l Ω E Y).obj (A.F.obj K)))) ∧
      (∀ M, HEq (q.b.hom.app M)
        (𝟙 ((rationalization.{u, v} l Ω E X).obj (A.G.obj M)))) ∧
      q.shiftX = integralRationalizationShift l Ω E X ∧
      q.shiftY = integralRationalizationShift l Ω E Y := by
  let TX := rationalization.{u, v} l Ω E X
  let TY := rationalization.{u, v} l Ω E Y
  let : TX.CommShift ℤ := integralRationalizationShift l Ω E X
  let : TY.CommShift ℤ := integralRationalizationShift l Ω E Y
  let : (rawRationalFunctor l Ω E X Y A.F hX).CommShift ℤ := R.leftShift
  let : (rawRationalFunctor l Ω E Y X A.G hY).CommShift ℤ := R.rightShift
  let : A.F.CommShift ℤ := A.leftShift
  let : A.G.CommShift ℤ := A.rightShift
  let q := rawRationalComparison l Ω E A.F hX
  let b := rawRationalComparison l Ω E A.G hY
  have : NatTrans.CommShift q.hom ℤ := hq
  have : A.adjunction.CommShift ℤ := ⟨A.unitShift, A.counitShift⟩
  have : R.adjunction.CommShift ℤ := ⟨R.unitShift, R.counitShift⟩
  have hb : NatTrans.CommShift b.hom ℤ :=
    mate_shift A.adjunction R.adjunction TX TY q b.hom hc
  let c : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E) TX TY := {
    shiftX := integralRationalizationShift l Ω E X
    shiftY := integralRationalizationShift l Ω E Y
    comparison := { q := q, b := b, counit := hc, qShift := hq, bShift := hb } }
  refine ⟨c, ?_, ?_, rfl, rfl⟩
  · intro K
    exact rawRationalComparisonHom l Ω E A.F hX K
  · intro M
    exact rawRationalComparisonHom l Ω E A.G hY M

/-- A single integral linear adjunction localizes on its literal tensor Hom maps.
There is no compactification, compact-support realization, or change of coefficient field.
Source: Zheng, Construction 6.2, and scalar localization of adjunctions
(blueprint: lem-sf-integral-adjunction-raw-localization).
-/
theorem exists_integral_adjunction_raw_localization
    (A : Operation.{u, v} l Ω X Y (.integral E))
    [A.F.Additive] [A.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    (hX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X)
    (hY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y) :
    ∃ (R : RawLocalizedAdjunction l Ω E X Y A hX hY)
      (q : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E)
        (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)),
      (∀ K, HEq (q.q.hom.app K)
        (𝟙 ((rationalization.{u, v} l Ω E Y).obj (A.F.obj K)))) ∧
      (∀ M, HEq (q.b.hom.app M)
        (𝟙 ((rationalization.{u, v} l Ω E X).obj (A.G.obj M)))) ∧
      q.shiftX = integralRationalizationShift l Ω E X ∧
      q.shiftY = integralRationalizationShift l Ω E Y := by
  obtain ⟨R, hc, hqs⟩ := exists_normalized_raw_core l Ω E A hX hY
  obtain ⟨q, hq, hb, hx, hy⟩ :=
    exists_raw_localized_identity_comparison l Ω E A hX hY R hc hqs
  exact ⟨R, q, hq, hb, hx, hy⟩

end WeilConjectures.ConstructibleExceptionalCoefficients

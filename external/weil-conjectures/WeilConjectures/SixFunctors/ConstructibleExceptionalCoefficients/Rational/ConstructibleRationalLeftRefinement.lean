/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.DeligneLaumon.CompactSupportNormalizedScalarIsomorphisms
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-! # Raw rational descent of a compatible integral refinement

Source: Zheng Section 5 and Stacks 0F7B, 0F7I; normalized exceptional construction
(blueprint: lem-sf-constructible-rational-left-refinement). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] Operation.leftShift Operation.rightShift
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private def integralInverse (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    (T : Scheme.{max u v}) [T.Over (Spec (.of D.k))]
    (E : FieldStage.{max u v} l) :
    sfIntegralConstructibleCategory l E.carrier T ⥤ C.{u, v} l Ω T (.integral E) := by
  let : ∀ x : T, Invertible (l : T.residueField x) :=
    sfCompactSupportScalarResidueUnit l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) T
  have h := (integral_residue_tor D l hl E.carrier T).2
  exact { obj K := ⟨K.obj, h ▸ K.property⟩
          map f := ObjectProperty.homMk f.hom }

private theorem rationalization_surjective
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    (T : Scheme.{max u v}) [T.Over (Spec (.of D.k))]
    (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω T (.rational E)) :
    ∃ L : C.{u, v} l Ω T (.integral E), (rationalization.{u, v} l Ω E T).obj L = K := by
  exact ⟨(integralInverse l Ω D hl T E).obj K.obj, rfl⟩

private theorem normalized_conjugate {A : Type*} [Category A]
    {W X Y Z : A} (q : W ≅ X) (r : Y ≅ Z) (a : W ⟶ Y)
    (hX : X = W) (hZ : Z = Y)
    (hq : HEq q.hom (𝟙 W)) (hr : HEq r.hom (𝟙 Y)) :
    HEq (q.inv ≫ a ≫ r.hom) a := by
  subst X Z
  have hq' : q = Iso.refl W := Iso.ext (eq_of_heq hq)
  have hr' : r = Iso.refl Y := Iso.ext (eq_of_heq hr)
  subst q r
  simp

private theorem fullSubcategory_functor_eq {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty B) (F G : A ⥤ P.FullSubcategory) (h : F ⋙ P.ι = G ⋙ P.ι) :
    F = G := by
  have hobj (K : A) : F.obj K = G.obj K := by
    apply ObjectProperty.FullSubcategory.ext
    exact Functor.congr_obj h K
  refine CategoryTheory.Functor.ext hobj ?_
  intro K M f
  apply P.ι.map_injective
  simpa only [Functor.map_comp, eqToHom_map, Functor.comp_obj, Functor.comp_map] using
    Functor.congr_hom h f

private theorem scalar_localization_eq (E L : FieldStage.{max u v} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (T : Scheme.{max u v})
    (S : C.{u, v} l Ω T (.integral E) ⥤ C.{u, v} l Ω T (.integral L))
    (hS : S ⋙ (finiteTorConstructibleIntegral l L.carrier T).ι =
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i T) :
    rationalization.{u, v} l Ω E T ⋙ rationalScalar.{u, v} l Ω E L i T =
      S ⋙ rationalization.{u, v} l Ω L T := by
  let I := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  let I' := PurCompactSupport.finiteTorIntegralInclusion l L.carrier T
  let U := sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
    E.carrier L.carrier i T
  have hI : S ⋙ I' = I ⋙ U :=
    fullSubcategory_functor_eq (sfIntegralConstructible l L.carrier T) _ _ hS
  apply Functor.hext
  · intro K
    exact (sfRationalScalarExtension_obj l E.carrier T 0
      (Fact.out : l.Prime).ne_zero L.carrier i _).trans
      (congrArg (sfRationalConstructibleLocalization l L.carrier T).obj
        (Functor.congr_obj hI.symm K))
  · intro K M f
    have ht := sfRationalScalarExtension_map_tmul l E.carrier T 0
      (Fact.out : l.Prime).ne_zero L.carrier i (I.obj K) (I.obj M) (I.map f) 1
    simp only [map_one] at ht
    exact ht.trans (Functor.hcongr_hom
      (congrArg (fun V ↦ V ⋙ sfRationalConstructibleLocalization l L.carrier T) hI.symm) f)

private theorem map_heq {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) {W X Y Z : A} (hW : W = Y) (hX : X = Z)
    {a : W ⟶ X} {b : Y ⟶ Z} (h : HEq a b) : HEq (G.map a) (G.map b) := by
  subst Y Z
  exact heq_of_eq (congrArg G.map (eq_of_heq h))

private theorem app_heq {A B : Type*} [Category A] [Category B]
    {G H : A ⥤ B} (η : G ⟶ H) {K M : A} (h : K = M) :
    HEq (η.app K) (η.app M) := by
  subst M
  rfl

private theorem field_q_shift {X Y : Scheme.{max u v}} {s t : Stage.{max u v} l}
    (A : Operation.{u, v} l Ω X Y s) (B : Operation.{u, v} l Ω X Y t)
    (TX : C.{u, v} l Ω X s ⥤ C.{u, v} l Ω X t)
    (TY : C.{u, v} l Ω Y s ⥤ C.{u, v} l Ω Y t)
    (d : CounitFieldComparison.{u, v} l Ω A B TX TY)
    (sx : TX.CommShift ℤ) (sy : TY.CommShift ℤ)
    (hx : sx = d.shiftX) (hy : sy = d.shiftY) :
    letI := A.leftShift
    letI := B.leftShift
    letI := sx
    letI := sy
    d.q.hom.CommShift ℤ := by
  subst sx
  subst sy
  let := d.shiftX
  let := d.shiftY
  exact d.comparison.qShift

variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (R : CoefficientConstructionRing.{u, v} l Ω D hl (f := f))

/-- Localize a scalar-compatible integral refinement on the fixed rational functors.
Source: Zheng Section 5 and raw coefficient localization, exceptional step 6
(blueprint: lem-sf-constructible-rational-left-refinement).

Proof: the residue-Tor criterion identifies the integral finite-Tor domain with
the intrinsic constructible integral category. Whisker the given integral
isomorphism by raw localization and conjugate by the two fixed localization q
maps. The localization universal property extends this isomorphism uniquely to
all rational arrows: for a fraction multiply integral naturality by the inverse
of its denominator. The identity q normalization reduces its component to the
literal localization of the given integral component, giving the HEq below.
The equal source and target localization shift structures allow the q shift
squares to cancel, so the integral shift square descends to the rational one.
For scalar extension apply localization to the given integral scalar square.
The specified rational scalar q normalization identifies its two q terms with
those of the fixed rational functors. Every rational object has an integral
representative and every rational arrow is generated by integral arrows and
inverse denominators, so this proves the square on the whole rational category.
This construction also applies to zero objects and the identity refinement;
it makes no choice of a new rational object or adjunction. -/
theorem exists_rational_left_refinement
    (F : CoefficientConstructionFields.{u, v} l Ω D hl R)
    {c d : Compactification f}
    (hX : ∀ E, (F.rationalizationComparison c E).shiftX =
      (F.rationalizationComparison d E).shiftX)
    (hY : ∀ E, (F.rationalizationComparison c E).shiftY =
      (F.rationalizationComparison d E).shiftY)
    (hid : ∀ (a : Compactification f) (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)),
      HEq ((F.rationalizationComparison a E).q.hom.app K)
        (𝟙 ((rationalization.{u, v} l Ω E Y).obj ((R.operation a (.integral E)).F.obj K))))
    (α : ∀ E : FieldStage.{max u v} l,
      (R.operation c (.integral E)).F ≅ (R.operation d (.integral E)).F)
    (hα : ∀ E,
      letI := (R.operation c (.integral E)).leftShift
      letI := (R.operation d (.integral E)).leftShift
      (α E).hom.CommShift ℤ)
    (hs :
      ∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u, v} l Ω X (.integral E)),
      let a := PurCompactSupport.completedChange l E.carrier L.carrier i
      let ha := Allowed.integral E L i
      (R.scalar (s := .integral E) (t := .integral L) a ha false).functor.map ((α E).hom.app K) ≫
          (Scalar.counitQ.{u, v} l Ω
            (R.scalar (s := .integral E) (t := .integral L) a ha true)
            (R.scalar (s := .integral E) (t := .integral L) a ha false)
            (R.comparison d (s := .integral E) (t := .integral L) a ha)).hom.app K =
        (Scalar.counitQ.{u, v} l Ω
            (R.scalar (s := .integral E) (t := .integral L) a ha true)
            (R.scalar (s := .integral E) (t := .integral L) a ha false)
            (R.comparison c (s := .integral E) (t := .integral L) a ha)).hom.app K ≫
          (α L).hom.app
            ((R.scalar (s := .integral E) (t := .integral L) a ha true).functor.obj K)) :
    ∃ β : ∀ E : FieldStage.{max u v} l,
        (R.operation c (.rational E)).F ≅ (R.operation d (.rational E)).F,
      (∀ E,
        letI := (R.operation c (.rational E)).leftShift
        letI := (R.operation d (.rational E)).leftShift
        (β E).hom.CommShift ℤ) ∧
      (∀ (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)),
        HEq ((β E).hom.app ((rationalization.{u, v} l Ω E X).obj K))
          ((rationalization.{u, v} l Ω E Y).map ((α E).hom.app K))) ∧
      (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
        (K : C.{u, v} l Ω X (.rational E)),
        (rationalScalar.{u, v} l Ω E L i Y).map ((β E).hom.app K) ≫
            (F.rationalComparison d E L i).q.hom.app K =
          (F.rationalComparison c E L i).q.hom.app K ≫
            (β L).hom.app ((rationalScalar.{u, v} l Ω E L i X).obj K)) := by
  classical
  let J (E : FieldStage.{max u v} l) := integralInverse l Ω D hl X E
  let e (E : FieldStage.{max u v} l) :
      sfRationalConstructibleLocalization l E.carrier X ⋙ (R.operation c (.rational E)).F ≅
        sfRationalConstructibleLocalization l E.carrier X ⋙
          (R.operation d (.rational E)).F :=
    Functor.isoWhiskerLeft (J E) (F.rationalizationComparison c E).q.symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (J E) (α E))
        (rationalization.{u, v} l Ω E Y) ≪≫
      Functor.isoWhiskerLeft (J E) (F.rationalizationComparison d E).q
  have descent (E : FieldStage.{max u v} l) :=
    ScalarLocalization.naturalIso_of_integral
      (Padic.coefficientExtensionIntegers l E.carrier)
      (sfIntegralConstructibleCategory l E.carrier X)
      (Padic.coefficientExtensionUniformizer l E.carrier)
      (R.operation c (.rational E)).F (R.operation d (.rational E)).F (e E)
  choose β hβ _ using descent
  have hβ' (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
      (β E).hom.app ((rationalization.{u, v} l Ω E X).obj K) =
        (F.rationalizationComparison c E).q.inv.app K ≫
          (rationalization.{u, v} l Ω E Y).map ((α E).hom.app K) ≫
          (F.rationalizationComparison d E).q.hom.app K := by
    exact hβ E ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  have hβnorm (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
      HEq ((β E).hom.app ((rationalization.{u, v} l Ω E X).obj K))
        ((rationalization.{u, v} l Ω E Y).map ((α E).hom.app K)) := by
    rw [hβ']
    exact normalized_conjugate
      ((F.rationalizationComparison c E).q.app K)
      ((F.rationalizationComparison d E).q.app K) _
      ((F.rationalAction c E).1 K) ((F.rationalAction d E).1 K)
      (hid c E K) (hid d E K)
  refine ⟨β, ?_, hβnorm, ?_⟩
  · intro E
    let := (R.operation c (.integral E)).leftShift
    let := (R.operation d (.integral E)).leftShift
    let := (R.operation c (.rational E)).leftShift
    let := (R.operation d (.rational E)).leftShift
    let := (F.rationalizationComparison c E).shiftX
    let := (F.rationalizationComparison c E).shiftY
    let := hα E
    have : (F.rationalizationComparison c E).q.hom.CommShift ℤ :=
      field_q_shift l Ω _ _ _ _ (F.rationalizationComparison c E) _ _ rfl rfl
    have : (F.rationalizationComparison d E).q.hom.CommShift ℤ :=
      field_q_shift l Ω _ _ _ _ (F.rationalizationComparison d E) _ _ (hX E) (hY E)
    let e' := (F.rationalizationComparison c E).q.symm ≪≫
      Functor.isoWhiskerRight (α E) (rationalization.{u, v} l Ω E Y) ≪≫
      (F.rationalizationComparison d E).q
    have he' : e'.hom.CommShift ℤ := by
      change ((F.rationalizationComparison c E).q.inv ≫
        Functor.whiskerRight (α E).hom (rationalization.{u, v} l Ω E Y) ≫
          (F.rationalizationComparison d E).q.hom).CommShift ℤ
      infer_instance
    have heq : Functor.whiskerLeft (rationalization.{u, v} l Ω E X) (β E).hom =
        e'.hom := by
      ext K
      exact hβ' E K
    have : (Functor.whiskerLeft (rationalization.{u, v} l Ω E X)
        (β E).hom).CommShift ℤ := heq.symm ▸ he'
    apply NatTrans.CommShift.of_whiskerLeft (β E).hom
      (rationalization.{u, v} l Ω E X)
    intro K
    obtain ⟨L, rfl⟩ := rationalization_surjective l Ω D hl X E K
    exact ⟨L, 𝟙 _, by infer_instance⟩
  · intro E L i K
    obtain ⟨K, rfl⟩ := rationalization_surjective l Ω D hl X E K
    let a := PurCompactSupport.completedChange l E.carrier L.carrier i
    let ha := Allowed.integral E L i
    let SX := R.scalar (s := .integral E) (t := .integral L) a ha true
    let SY := R.scalar (s := .integral E) (t := .integral L) a ha false
    let QX := rationalization.{u, v} l Ω E X
    let QY := rationalization.{u, v} l Ω E Y
    let QX' := rationalization.{u, v} l Ω L X
    let QY' := rationalization.{u, v} l Ω L Y
    let TX := rationalScalar.{u, v} l Ω E L i X
    let TY := rationalScalar.{u, v} l Ω E L i Y
    have hSX : QX ⋙ TX = SX.functor ⋙ QX' :=
      scalar_localization_eq l Ω E L i X SX.functor (R.integralScalar_eq E L i true)
    have hSY : QY ⋙ TY = SY.functor ⋙ QY' :=
      scalar_localization_eq l Ω E L i Y SY.functor (R.integralScalar_eq E L i false)
    have hsrc (a : Compactification f) :
        TY.obj ((R.operation a (.rational E)).F.obj (QX.obj K)) =
          QY'.obj (SY.functor.obj ((R.operation a (.integral E)).F.obj K)) :=
      (congrArg TY.obj ((F.rationalAction a E).1 K)).trans
        (Functor.congr_obj hSY ((R.operation a (.integral E)).F.obj K))
    have htgt (a : Compactification f) :
        (R.operation a (.rational L)).F.obj (TX.obj (QX.obj K)) =
          QY'.obj ((R.operation a (.integral L)).F.obj (SX.functor.obj K)) :=
      (congrArg (R.operation a (.rational L)).F.obj (Functor.congr_obj hSX K)).trans
        ((F.rationalAction a L).1 (SX.functor.obj K))
    have hm : HEq (TY.map ((β E).hom.app (QX.obj K)))
        (QY'.map (SY.functor.map ((α E).hom.app K))) :=
      (map_heq TY ((F.rationalAction c E).1 K) ((F.rationalAction d E).1 K)
        (hβnorm E K)).trans (Functor.hcongr_hom hSY ((α E).hom.app K))
    have hb : HEq ((β L).hom.app (TX.obj (QX.obj K)))
        (QY'.map ((α L).hom.app (SX.functor.obj K))) :=
      (app_heq (β L).hom (Functor.congr_obj hSX K)).trans (hβnorm L (SX.functor.obj K))
    have hleft : HEq
        (TY.map ((β E).hom.app (QX.obj K)) ≫
          (F.rationalComparison d E L i).q.hom.app (QX.obj K))
        (QY'.map (SY.functor.map ((α E).hom.app K) ≫
          (Scalar.counitQ.{u, v} l Ω SX SY
            (R.comparison d (s := .integral E) (t := .integral L) a ha)).hom.app K)) := by
      rw [QY'.map_comp]
      exact CategoryTheory.heq_comp (hsrc c) (hsrc d) (htgt d)
        hm (F.rational_normalized d E L i K)
    have hright : HEq
        ((F.rationalComparison c E L i).q.hom.app (QX.obj K) ≫
          (β L).hom.app (TX.obj (QX.obj K)))
        (QY'.map ((Scalar.counitQ.{u, v} l Ω SX SY
            (R.comparison c (s := .integral E) (t := .integral L) a ha)).hom.app K ≫
          (α L).hom.app (SX.functor.obj K))) := by
      rw [QY'.map_comp]
      exact CategoryTheory.heq_comp (hsrc c) (htgt c) (htgt d)
        (F.rational_normalized c E L i K) hb
    exact eq_of_heq (hleft.trans
      ((heq_of_eq (congrArg QY'.map (hs E L i K))).trans hright.symm))

end WeilConjectures.ConstructibleExceptionalCoefficients

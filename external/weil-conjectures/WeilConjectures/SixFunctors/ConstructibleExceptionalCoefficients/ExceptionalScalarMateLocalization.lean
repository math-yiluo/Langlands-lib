/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.ExceptionalIntegralAdjunctionLocalization
import all WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.ExceptionalIntegralAdjunctionLocalization
import Mathlib.CategoryTheory.Localization.Equivalence

/-! # Localization of a supplied integral coefficient mate

Source: Zheng, Construction 6.2. Only one change of coefficient field is considered;
there is no geometric construction or common-field coherence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfIntegralConstructible WeilConjectures.sfRationalTriangulationDatum
  WeilConjectures.sfRationalScalarExtension Padic.coefficientExtensionIntegers
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v w
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance] Operation.leftAdditive Operation.rightAdditive
  Operation.leftShift Operation.rightShift
attribute [local instance] Scalar.commShift Scalar.additive
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X Y : Scheme.{max u v}}

private theorem full_hom_heq {D : Type*} [Category D] {P : ObjectProperty D}
    {A B A' B' : P.FullSubcategory} (ha : A.obj = A'.obj) (hb : B.obj = B'.obj)
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f.hom g.hom) : HEq f g := by
  have ea : A = A' := ObjectProperty.FullSubcategory.ext ha
  have eb : B = B' := ObjectProperty.FullSubcategory.ext hb
  subst A'; subst B'
  exact heq_of_eq (ObjectProperty.hom_ext _ (eq_of_heq h))

private theorem shift_of_whisker
    {D D' H : Type*} [Category D] [Category D'] [Category H]
    [HasShift D ℤ] [HasShift D' ℤ] [HasShift H ℤ]
    (Q : D ⥤ D') (W : MorphismProperty D) [Q.IsLocalization W] [Q.CommShift ℤ]
    {F G : D' ⥤ H} [F.CommShift ℤ] [G.CommShift ℤ]
    (a : F ⟶ G) [NatTrans.CommShift (Functor.whiskerLeft Q a) ℤ] :
    NatTrans.CommShift a ℤ := by
  constructor
  intro n
  apply Localization.natTrans_ext Q W
  intro K
  apply (cancel_epi (F.map ((Q.commShiftIso n).hom.app K))).1
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft Q a) n K
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc, ← a.naturality_assoc] using h

private theorem iso_map_conjugate
    {D H : Type*} [Category D] [Category H]
    {F G : D ⥤ H} (e : F ≅ G) {K M : D} (f : K ⟶ M) :
    e.hom.app K ≫ G.map f ≫ e.inv.app M = F.map f := by
  rw [← e.hom.naturality_assoc f, e.hom_inv_id_app, Category.comp_id]

private theorem scalar_factor
    (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (T : Scheme.{max u v})
    (S : C.{u, v} l Ω T (.integral E) ⥤ C.{u, v} l Ω T (.integral L))
    (hS : S ⋙ RingStage.inclusion.{u, v} l Ω T (.integral L) =
      RingStage.inclusion.{u, v} l Ω T (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i T) :
    rationalization.{u, v} l Ω E T ⋙ rationalScalar.{u, v} l Ω E L i T =
      S ⋙ rationalization.{u, v} l Ω L T := by
  apply Functor.hext
  · intro K
    refine (sfRationalScalarExtension_obj l E.carrier T 0
      (Fact.out : l.Prime).ne_zero L.carrier i _).trans ?_
    apply congrArg (sfRationalConstructibleLocalization l L.carrier T).obj
    apply ObjectProperty.FullSubcategory.ext
    exact (Functor.congr_obj hS K).symm
  · intro K K' f
    have hm := sfRationalScalarExtension_map_tmul l E.carrier T 0
      (Fact.out : l.Prime).ne_zero L.carrier i
      ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).obj K)
      ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).obj K')
      ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).map f) 1
    simp only [map_one] at hm
    refine hm.trans ?_
    have hi := Functor.hcongr_hom hS f
    have ho (K) := Functor.congr_obj hS K
    have hh : HEq
        ((PurCompactSupport.finiteTorIntegralInclusion l L.carrier T).map (S.map f))
        ((sfConstructibleIntegralScalarExtension 0 l
          (Fact.out : l.Prime).ne_zero E.carrier L.carrier i T).map
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier T).map f)) := by
      exact full_hom_heq (ho K) (ho K') hi
    exact (CategoryTheory.ScalarLocalization.hom_map_heq
      (sfRationalConstructibleLocalization l L.carrier T)
      (by apply ObjectProperty.FullSubcategory.ext; exact ho K)
      (by apply ObjectProperty.FullSubcategory.ext; exact ho K') hh).symm

private theorem rationalization_isLocalization
    (E : FieldStage.{max u v} l) (T : Scheme.{max u v})
    (h : sfIntegralConstructible l E.carrier T = finiteTorConstructibleIntegral l E.carrier T) :
    (rationalization.{u, v} l Ω E T).IsLocalization
      ((MorphismProperty.isomorphisms _).inverseImage (rationalization.{u, v} l Ω E T)) := by
  let Q := sfRationalConstructibleLocalization l E.carrier T
  let W := Rationalization.W (Submonoid.powers
    (Padic.coefficientExtensionUniformizer l E.carrier))
      (sfIntegralConstructibleCategory l E.carrier T)
  have : Q.IsLocalization W := integralLocalization l E T
  let Q' := rationalization.{u, v} l Ω E T
  let W' := (MorphismProperty.isomorphisms _).inverseImage Q'
  let e := integralRepresentativeEquivalence l Ω E T h
  refine Functor.IsLocalization.of_equivalence_source Q W Q' W' e ?_ ?_ (Iso.refl _)
  · intro K L f hf
    apply W'.le_isoClosure
    change IsIso (Q.map f)
    exact Localization.inverts Q W f hf
  · intro K L f hf
    exact hf

attribute [local irreducible] integralScalarExtensionOfUniverses

/-- The scalar localization comparison commutes with every integer shift.
The comparison is the identity transport on integral representatives; the square
retains the canonical endpoint rationalization shifts.
Source: Zheng, Construction 6.2, shift compatibility in coefficient localization
(blueprint: lem-sf-integral-scalar-mate-localization). -/
@[irreducible]
def scalarShiftLocalization
    (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (T : Scheme.{max u v})
    (S : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) T)
    (cs : (rationalScalar.{u, v} l Ω E L i T).CommShift ℤ) : Prop :=
  letI := cs
  letI := S.commShift
  letI := integralRationalizationShift.{u, v} l Ω E T
  letI := integralRationalizationShift.{u, v} l Ω L T
  ∃ c : rationalization.{u, v} l Ω E T ⋙ rationalScalar.{u, v} l Ω E L i T ≅
      S.functor ⋙ rationalization.{u, v} l Ω L T,
    (∀ K, HEq (c.hom.app K)
      (𝟙 ((rationalScalar.{u, v} l Ω E L i T).obj
        ((rationalization.{u, v} l Ω E T).obj K)))) ∧
    c.hom.CommShift ℤ

/-- Localize a single supplied counit square on the explicit raw tensor functors.
Source: Zheng, Construction 6.2, scalar-extension paragraph
(blueprint: lem-sf-integral-scalar-mate-localization).

Proof: identify the two scalar localization squares using the published object and
pure-tensor formulas and the supplied ambient functor equalities. Rationalization
is a categorical localization after transport along the integral representative
equivalence. Paste the supplied integral comparisons with the endpoint localization
isomorphisms and descend the resulting natural isomorphisms by fully faithful
precomposition. Equip each rational scalar functor with the shift structure induced
by localization. The pasted comparisons commute with shifts; faithfulness and the
invertible rationalization shift comparisons imply the descended shift equations.
The normalized qA and qB components identify the rationalized integral counits.
On integral representatives, substitute the descended component formulas, cancel
inverse endpoint comparisons, and use counit naturality and d.counit. Naturality of
the scalar localization comparison closes the equation. Every rational object has
an integral representative by the supplied predicate equality. Finally the endpoint
localization comparisons are identity transports, so their heterogeneous component
formula gives the asserted normalization of q. The same argument covers identity
coefficient embeddings and zero categories. -/
theorem exists_integral_scalar_mate_localization
    (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (A : Operation.{u, v} l Ω X Y (.integral E))
    (B : Operation.{u, v} l Ω X Y (.integral L))
    [A.F.Additive] [A.G.Additive] [B.F.Additive] [B.G.Additive]
    [A.F.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [A.G.Linear (Padic.coefficientExtensionIntegers l E.carrier)]
    [B.F.Linear (Padic.coefficientExtensionIntegers l L.carrier)]
    [B.G.Linear (Padic.coefficientExtensionIntegers l L.carrier)]
    {hEX : sfIntegralConstructible l E.carrier X = finiteTorConstructibleIntegral l E.carrier X}
    {hEY : sfIntegralConstructible l E.carrier Y = finiteTorConstructibleIntegral l E.carrier Y}
    {hLX : sfIntegralConstructible l L.carrier X = finiteTorConstructibleIntegral l L.carrier X}
    {hLY : sfIntegralConstructible l L.carrier Y = finiteTorConstructibleIntegral l L.carrier Y}
    (R : RawLocalizedAdjunction.{u, v} l Ω E X Y A hEX hEY)
    (S : RawLocalizedAdjunction.{u, v} l Ω L X Y B hLX hLY)
    (qA : CounitFieldComparison.{u, v} l Ω A (R.operation l Ω E)
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y))
    (qB : CounitFieldComparison.{u, v} l Ω B (S.operation l Ω L)
      (rationalization.{u, v} l Ω L X) (rationalization.{u, v} l Ω L Y))
    (hqA : ∀ K, HEq (qA.q.hom.app K)
      (𝟙 ((rationalization.{u, v} l Ω E Y).obj (A.F.obj K))))
    (hbA : ∀ M, HEq (qA.b.hom.app M)
      (𝟙 ((rationalization.{u, v} l Ω E X).obj (A.G.obj M))))
    (hqB : ∀ K, HEq (qB.q.hom.app K)
      (𝟙 ((rationalization.{u, v} l Ω L Y).obj (B.F.obj K))))
    (hbB : ∀ M, HEq (qB.b.hom.app M)
      (𝟙 ((rationalization.{u, v} l Ω L X).obj (B.G.obj M))))
    (hsAX : qA.shiftX = integralRationalizationShift.{u, v} l Ω E X)
    (hsAY : qA.shiftY = integralRationalizationShift.{u, v} l Ω E Y)
    (hsBX : qB.shiftX = integralRationalizationShift.{u, v} l Ω L X)
    (hsBY : qB.shiftY = integralRationalizationShift.{u, v} l Ω L Y)
    (SX : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) X)
    (SY : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) Y)
    (hSX : SX.functor ⋙ RingStage.inclusion.{u, v} l Ω X (.integral L) =
      RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i X)
    (hSY : SY.functor ⋙ RingStage.inclusion.{u, v} l Ω Y (.integral L) =
      RingStage.inclusion.{u, v} l Ω Y (.integral E) ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i Y)
    (d : letI := SX.commShift
      letI := SY.commShift
      CounitComparison.{u, v} l Ω A B SX.functor SY.functor) :
    letI := SX.commShift
    letI := SY.commShift
    ∃ e : CounitFieldComparison.{u, v} l Ω (R.operation l Ω E) (S.operation l Ω L)
        (rationalScalar.{u, v} l Ω E L i X) (rationalScalar.{u, v} l Ω E L i Y),
      (∀ K : C.{u, v} l Ω X (.integral E),
        HEq (e.q.hom.app ((rationalization.{u, v} l Ω E X).obj K))
          ((rationalization.{u, v} l Ω L Y).map (d.q.hom.app K))) ∧
      scalarShiftLocalization.{u, v} l Ω E L i X SX e.shiftX ∧
      scalarShiftLocalization.{u, v} l Ω E L i Y SY e.shiftY := by
  rcases qA with @⟨sAX, sAY, qA⟩
  rcases qB with @⟨sBX, sBY, qB⟩
  dsimp only at hsAX hsAY hsBX hsBY
  subst sAX; subst sAY; subst sBX; subst sBY
  let QX := rationalization.{u, v} l Ω E X
  let QY := rationalization.{u, v} l Ω E Y
  let PX := rationalization.{u, v} l Ω L X
  let PY := rationalization.{u, v} l Ω L Y
  let TX := rationalScalar.{u, v} l Ω E L i X
  let TY := rationalScalar.{u, v} l Ω E L i Y
  let A' := R.operation l Ω E
  let B' := S.operation l Ω L
  let : A.F.CommShift ℤ := A.leftShift
  let : A.G.CommShift ℤ := A.rightShift
  let : B.F.CommShift ℤ := B.leftShift
  let : B.G.CommShift ℤ := B.rightShift
  let : A'.F.CommShift ℤ := A'.leftShift
  let : A'.G.CommShift ℤ := A'.rightShift
  let : B'.F.CommShift ℤ := B'.leftShift
  let : B'.G.CommShift ℤ := B'.rightShift
  let WX := (MorphismProperty.isomorphisms _).inverseImage QX
  let WY := (MorphismProperty.isomorphisms _).inverseImage QY
  have : QX.IsLocalization WX := rationalization_isLocalization.{u, v} l Ω E X hEX
  have : QY.IsLocalization WY := rationalization_isLocalization.{u, v} l Ω E Y hEY
  let : QX.CommShift ℤ := integralRationalizationShift.{u, v} l Ω E X
  let : QY.CommShift ℤ := integralRationalizationShift.{u, v} l Ω E Y
  let : PX.CommShift ℤ := integralRationalizationShift.{u, v} l Ω L X
  let : PY.CommShift ℤ := integralRationalizationShift.{u, v} l Ω L Y
  let : SX.functor.CommShift ℤ := SX.commShift
  let : SY.functor.CommShift ℤ := SY.commShift
  let cX : QX ⋙ TX ≅ SX.functor ⋙ PX := eqToIso (scalar_factor.{u, v} l Ω E L i X _ hSX)
  let cY : QY ⋙ TY ≅ SY.functor ⋙ PY := eqToIso (scalar_factor.{u, v} l Ω E L i Y _ hSY)
  let : Localization.Lifting QX WX (SX.functor ⋙ PX) TX := ⟨cX⟩
  let : Localization.Lifting QY WY (SY.functor ⋙ PY) TY := ⟨cY⟩
  let csX : TX.CommShift ℤ :=
    Functor.commShiftOfLocalization QX WX ℤ (SX.functor ⋙ PX) TX
  let csY : TY.CommShift ℤ :=
    Functor.commShiftOfLocalization QY WY ℤ (SY.functor ⋙ PY) TY
  let : TX.CommShift ℤ := csX
  let : TY.CommShift ℤ := csY
  have : cX.hom.CommShift ℤ :=
    NatTrans.commShift_iso_hom_of_localization QX WX ℤ (SX.functor ⋙ PX) TX
  have : cY.hom.CommShift ℤ :=
    NatTrans.commShift_iso_hom_of_localization QY WY ℤ (SY.functor ⋙ PY) TY
  have : qA.q.hom.CommShift ℤ := qA.qShift
  have : qA.b.hom.CommShift ℤ := qA.bShift
  have : qB.q.hom.CommShift ℤ := qB.qShift
  have : qB.b.hom.CommShift ℤ := qB.bShift
  have : d.q.hom.CommShift ℤ := d.qShift
  have : d.b.hom.CommShift ℤ := d.bShift
  let q₀ : QX ⋙ (A'.F ⋙ TY) ≅ QX ⋙ (TX ⋙ B'.F) :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight qA.q.symm TY ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft A.F cY ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight d.q PY ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft SX.functor qB.q ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight cX.symm B'.F ≪≫
      Functor.associator _ _ _
  let b₀ : QY ⋙ (A'.G ⋙ TX) ≅ QY ⋙ (TY ⋙ B'.G) :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight qA.b.symm TX ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft A.G cX ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight d.b PX ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft SY.functor qB.b ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight cY.symm B'.G ≪≫
      Functor.associator _ _ _
  let ffX := Localization.fullyFaithfulWhiskeringLeft QX WX (C.{u, v} l Ω Y (.rational L))
  let ffY := Localization.fullyFaithfulWhiskeringLeft QY WY (C.{u, v} l Ω X (.rational L))
  let q : A'.F ⋙ TY ≅ TX ⋙ B'.F := ffX.preimageIso q₀
  let b : A'.G ⋙ TX ≅ TY ⋙ B'.G := ffY.preimageIso b₀
  have hq : Functor.whiskerLeft QX q.hom = q₀.hom := ffX.map_preimage _
  have hb : Functor.whiskerLeft QY b.hom = b₀.hom := ffY.map_preimage _
  have : q₀.hom.CommShift ℤ := by
    dsimp only [q₀, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom]
    repeat' apply NatTrans.CommShift.comp
  have : b₀.hom.CommShift ℤ := by
    dsimp only [b₀, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom]
    repeat' apply NatTrans.CommShift.comp
  have : (Functor.whiskerLeft QX q.hom).CommShift ℤ := by rw [hq]; infer_instance
  have : (Functor.whiskerLeft QY b.hom).CommShift ℤ := by rw [hb]; infer_instance
  have : q.hom.CommShift ℤ := shift_of_whisker QX WX q.hom
  have : b.hom.CommShift ℤ := shift_of_whisker QY WY b.hom
  have hqA' (K) : qA.q.hom.app K = 𝟙 _ := eq_of_heq (hqA K)
  have hbA' (K) : qA.b.hom.app K = 𝟙 _ := eq_of_heq (hbA K)
  have hqB' (K) : qB.q.hom.app K = 𝟙 _ := eq_of_heq (hqB K)
  have hbB' (K) : qB.b.hom.app K = 𝟙 _ := eq_of_heq (hbB K)
  have hqAi (K) : qA.q.inv.app K = 𝟙 _ := by
    have h := qA.q.hom_inv_id_app K
    erw [hqA', Category.id_comp] at h
    exact h
  have hbAi (K) : qA.b.inv.app K = 𝟙 _ := by
    have h := qA.b.hom_inv_id_app K
    erw [hbA', Category.id_comp] at h
    exact h
  have qval (K) : q.hom.app (QX.obj K) =
      cY.hom.app (A.F.obj K) ≫ PY.map (d.q.hom.app K) ≫ B'.F.map (X := PX.obj (SX.functor.obj K))
        (Y := TX.obj (QX.obj K)) (cX.inv.app K) := by
    have h := congr_app hq K
    simp only [q₀, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      hqAi, hqB'] at h
    erw [CategoryTheory.Functor.map_id] at h
    repeat' erw [Category.id_comp] at h
    repeat' erw [Category.comp_id] at h
    exact h
  have bval (K) : b.hom.app (QY.obj K) =
      cX.hom.app (A.G.obj K) ≫ PX.map (d.b.hom.app K) ≫ B'.G.map (X := PY.obj (SY.functor.obj K))
        (Y := TY.obj (QY.obj K)) (cY.inv.app K) := by
    have h := congr_app hb K
    simp only [b₀, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      hbAi, hbB'] at h
    erw [CategoryTheory.Functor.map_id] at h
    repeat' erw [Category.id_comp] at h
    repeat' erw [Category.comp_id] at h
    exact h
  have counitA (M) : A'.adjunction.counit.app (QY.obj M) =
      QY.map (A.adjunction.counit.app M) := by
    have h := qA.counit M
    erw [hqA', hbA', CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at h
    exact h
  have counitB (M) : B'.adjunction.counit.app (PY.obj M) =
      PY.map (B.adjunction.counit.app M) := by
    have h := qB.counit M
    erw [hqB', hbB', CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at h
    exact h
  have hc : ∀ M, q.hom.app (A'.G.obj M) ≫ B'.F.map (b.hom.app M) ≫
      B'.adjunction.counit.app (TY.obj M) = TY.map (A'.adjunction.counit.app M) := by
    intro M
    obtain ⟨M, rfl⟩ : ∃ M₀, QY.obj M₀ = M :=
      ⟨⟨M.obj.obj, hEY ▸ M.obj.property⟩, rfl⟩
    change q.hom.app (QX.obj (A.G.obj M)) ≫ _ = _
    erw [qval, bval]
    erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    repeat' erw [Category.assoc]
    erw [reassoc_of% ((B'.F.mapIso (cX.app (A.G.obj M))).inv_hom_id)]
    erw [B'.adjunction.counit_naturality (cY.inv.app M), counitB]
    have hm : B'.F.map (PX.map (d.b.hom.app M)) =
        PY.map (B.F.map (d.b.hom.app M)) := by
      have h := qB.q.hom.naturality (d.b.hom.app M)
      simp only [Functor.comp_map] at h
      erw [hqB', hqB', Category.comp_id, Category.id_comp] at h
      exact h.symm
    have hd := congrArg (fun f => PY.map f) (d.counit M)
    simp only [CategoryTheory.Functor.map_comp] at hd
    erw [hm, reassoc_of% hd]
    calc
      _ = TY.map (QY.map (A.adjunction.counit.app M)) :=
        iso_map_conjugate cY (A.adjunction.counit.app M)
      _ = _ := congrArg (fun f => TY.map f) (counitA M).symm
  let e : CounitFieldComparison.{u, v} l Ω A' B' TX TY :=
    { shiftX := csX
      shiftY := csY
      comparison :=
        { q := q
          b := b
          counit := hc
          qShift := inferInstance
          bShift := inferInstance } }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro K
    change HEq (q.hom.app (QX.obj K)) (PY.map (d.q.hom.app K))
    rw [qval]
    dsimp only [cX, cY]
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map]
    exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  · unfold scalarShiftLocalization
    refine ⟨cX, ?_, inferInstance⟩
    intro K
    dsimp only [cX]
    rw [eqToIso.hom, eqToHom_app]
    exact eqToHom_heq_id_dom _ _ _
  · unfold scalarShiftLocalization
    refine ⟨cY, ?_, inferInstance⟩
    intro K
    dsimp only [cY]
    rw [eqToIso.hom, eqToHom_app]
    exact eqToHom_heq_id_dom _ _ _

end WeilConjectures.ConstructibleExceptionalCoefficients

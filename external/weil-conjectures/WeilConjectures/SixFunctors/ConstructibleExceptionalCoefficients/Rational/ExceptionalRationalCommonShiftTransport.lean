/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalCommonCoherence
import all WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Integral.ExceptionalIntegralAdjunctionLocalization
import WeilConjectures.DeligneLaumon.CompactSupportNormalizedScalarIsomorphisms
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SmoothPurity.Sf.SfQbarLocalizationShiftDescent
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalNormalizedScalarShift

/-! # Proved shift normalization and endpoint transport helpers

These helpers implement canonical finite normalization, common left-shift descent,
and transport back to supplied finite shifts. The public representative theorem
also exposes the literal object surjectivity used in that transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfIntegralConstructible WeilConjectures.sfRationalTriangulationDatum
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v w u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalShiftCorrection
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]

private def shiftIso (F : C ⥤ D) (s : F.CommShift ℤ) (n : ℤ) :
    shiftFunctor C n ⋙ F ≅ F ⋙ shiftFunctor D n :=
  letI := s
  F.commShiftIso n

@[instance_reducible]
private def correction (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (J : D ⥤ E) (q₀ q₁ : Q.CommShift ℤ) (j₀ : J.CommShift ℤ) : J.CommShift ℤ := by
  let s : (Q ⋙ J).CommShift ℤ := by
    letI := q₀
    letI := j₀
    infer_instance
  letI := q₁
  letI := s
  letI : Localization.Lifting Q W (Q ⋙ J) J := ⟨Iso.refl _⟩
  exact Functor.commShiftOfLocalization Q W ℤ (Q ⋙ J) J

private theorem correction_hom (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (J : D ⥤ E) (q₀ q₁ : Q.CommShift ℤ) (j₀ : J.CommShift ℤ) (n : ℤ) (K : C) :
    (shiftIso J (correction Q W J q₀ q₁ j₀) n).hom.app (Q.obj K) =
      J.map ((shiftIso Q q₁ n).inv.app K) ≫
        J.map ((shiftIso Q q₀ n).hom.app K) ≫
          (shiftIso J j₀ n).hom.app (Q.obj K) := by
  let s : (Q ⋙ J).CommShift ℤ := by
    let :=  q₀
    let :=  j₀
    infer_instance
  let :=  q₁
  let :=  s
  let : Localization.Lifting Q W (Q ⋙ J) J := ⟨Iso.refl _⟩
  have hi : Localization.Lifting.iso Q W (Q ⋙ J) J = Iso.refl _ := rfl
  have h := Functor.commShiftOfLocalization_iso_hom_app Q W (Q ⋙ J) J n K
  rw [hi] at h
  simpa [shiftIso, Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Category.assoc] using h

private theorem correction_comp (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (J : D ⥤ E) (q₀ q₁ : Q.CommShift ℤ) (j₀ : J.CommShift ℤ) (n : ℤ) (K : C) :
    J.map ((shiftIso Q q₁ n).hom.app K) ≫
        (shiftIso J (correction Q W J q₀ q₁ j₀) n).hom.app (Q.obj K) =
      J.map ((shiftIso Q q₀ n).hom.app K) ≫
        (shiftIso J j₀ n).hom.app (Q.obj K) := by
  rw [correction_hom, ← J.map_comp_assoc, Iso.hom_inv_id_app,
    J.map_id, Category.id_comp]

end WeilConjectures.ExceptionalShiftCorrection

namespace WeilConjectures.ExceptionalShiftCorrection
universe a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ a₆ b₆
variable {C₁ : Type a₁} {C₂ : Type a₂} {D₁ : Type a₃} {D₂ : Type a₄}
  {E₁ : Type a₅} {E₂ : Type a₆}
  [Category.{b₁} C₁] [Category.{b₂} C₂] [Category.{b₃} D₁] [Category.{b₄} D₂]
  [Category.{b₅} E₁] [Category.{b₆} E₂]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [HasShift E₁ ℤ] [HasShift E₂ ℤ]

private theorem restrictionChange
    (QX : C₁ ⥤ D₁) (QY : C₂ ⥤ D₂)
    (WX : MorphismProperty C₁) (WY : MorphismProperty C₂)
    [QX.IsLocalization WX] [QY.IsLocalization WY]
    (hX : Function.Surjective QX.obj)
    (IX : D₁ ⥤ E₁) (IY : D₂ ⥤ E₂) (F : C₁ ⥤ C₂) (Fq : D₁ ⥤ D₂) (H : E₁ ⥤ E₂)
    (q : F ⋙ QY ≅ QX ⋙ Fq) (e : Fq ⋙ IY ≅ IX ⋙ H)
    (qx₀ qx₁ : QX.CommShift ℤ) (qy₀ qy₁ : QY.CommShift ℤ)
    (ix₀ : IX.CommShift ℤ) (iy₀ : IY.CommShift ℤ)
    (f₀ f₁ : Fq.CommShift ℤ) [F.CommShift ℤ] [H.CommShift ℤ]
    (hq₀ : letI := qx₀; letI := qy₀; letI := f₀; q.hom.CommShift ℤ)
    (hq₁ : letI := qx₁; letI := qy₁; letI := f₁; q.hom.CommShift ℤ)
    (he₀ : letI := ix₀; letI := iy₀; letI := f₀; e.hom.CommShift ℤ) :
    letI := correction QX WX IX qx₀ qx₁ ix₀
    letI := correction QY WY IY qy₀ qy₁ iy₀
    letI := f₁
    e.hom.CommShift ℤ := by
  let ix₁ := correction QX WX IX qx₀ qx₁ ix₀
  let iy₁ := correction QY WY IY qy₀ qy₁ iy₀
  have qzero (n : ℤ) (K : C₁) :
      QY.map ((F.commShiftIso n).hom.app K) ≫
          (shiftIso QY qy₀ n).hom.app (F.obj K) ≫
            (shiftFunctor D₂ n).map (q.hom.app K) =
        q.hom.app (K⟦n⟧) ≫ Fq.map ((shiftIso QX qx₀ n).hom.app K) ≫
          (shiftIso Fq f₀ n).hom.app (QX.obj K) := by
    let := qx₀
    let := qy₀
    let := f₀
    have := hq₀
    simpa only [shiftIso, Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm q.hom n K
  have qone (n : ℤ) (K : C₁) :
      QY.map ((F.commShiftIso n).hom.app K) ≫
          (shiftIso QY qy₁ n).hom.app (F.obj K) ≫
            (shiftFunctor D₂ n).map (q.hom.app K) =
        q.hom.app (K⟦n⟧) ≫ Fq.map ((shiftIso QX qx₁ n).hom.app K) ≫
          (shiftIso Fq f₁ n).hom.app (QX.obj K) := by
    let := qx₁
    let := qy₁
    let := f₁
    have := hq₁
    simpa only [shiftIso, Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm q.hom n K
  have ezero (n : ℤ) (L : D₁) :
      IY.map ((shiftIso Fq f₀ n).hom.app L) ≫
          (shiftIso IY iy₀ n).hom.app (Fq.obj L) ≫
            (shiftFunctor E₂ n).map (e.hom.app L) =
        e.hom.app (L⟦n⟧) ≫ H.map ((shiftIso IX ix₀ n).hom.app L) ≫
          (H.commShiftIso n).hom.app (IX.obj L) := by
    let := ix₀
    let := iy₀
    let := f₀
    have := he₀
    simpa only [shiftIso, Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm e.hom n L
  let := ix₁
  let := iy₁
  let := f₁
  constructor
  intro n
  ext L
  obtain ⟨K, rfl⟩ := hX L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  change IY.map ((shiftIso Fq f₁ n).hom.app (QX.obj K)) ≫
        (shiftIso IY iy₁ n).hom.app (Fq.obj (QX.obj K)) ≫
          (shiftFunctor E₂ n).map (e.hom.app (QX.obj K)) =
      e.hom.app ((QX.obj K)⟦n⟧) ≫
        H.map ((shiftIso IX ix₁ n).hom.app (QX.obj K)) ≫
          (H.commShiftIso n).hom.app (IX.obj (QX.obj K))
  apply (cancel_epi (IY.map (q.hom.app (K⟦n⟧)) ≫
    IY.map (Fq.map ((shiftIso QX qx₁ n).hom.app K)))).1
  have hq0 := congrArg IY.map (qzero n K)
  have hq1 := congrArg IY.map (qone n K)
  simp only [Functor.map_comp] at hq0 hq1
  have hy0 := (shiftIso IY iy₀ n).hom.naturality (q.hom.app K)
  have hy1 := (shiftIso IY iy₁ n).hom.naturality (q.hom.app K)
  have hx0 := e.hom.naturality ((shiftIso QX qx₀ n).hom.app K)
  have hx1 := e.hom.naturality ((shiftIso QX qx₁ n).hom.app K)
  dsimp only [Functor.comp_map] at hy0 hy1 hx0 hx1
  simp only [Category.assoc]
  rw [← reassoc_of% hq1, reassoc_of% hy1,
    reassoc_of% (correction_comp QY WY IY qy₀ qy₁ iy₀ n (F.obj K)),
    ← reassoc_of% hy0, reassoc_of% hq0, ezero,
    reassoc_of% hx0, ← H.map_comp_assoc,
    ← correction_comp QX WX IX qx₀ qx₁ ix₀ n K, H.map_comp, Category.assoc,
    ← reassoc_of% hx1]

private theorem mateShiftExplicit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (adj : F ⊣ G) (adj' : F' ⊣ G')
    [F.CommShift ℤ] [G.CommShift ℤ] [F'.CommShift ℤ] [G'.CommShift ℤ]
    [adj.CommShift ℤ] [adj'.CommShift ℤ]
    (TX : C ⥤ C') (TY : D ⥤ D') [TX.CommShift ℤ] [TY.CommShift ℤ]
    (q : F ⋙ TY ≅ TX ⋙ F') (b : G ⋙ TX ⟶ TY ⋙ G')
    (hq : NatTrans.CommShift q.hom ℤ)
    (hc : ∀ L, q.hom.app (G.obj L) ≫ F'.map (b.app L) ≫
      adj'.counit.app (TY.obj L) = TY.map (adj.counit.app L)) :
    NatTrans.CommShift b ℤ := by
  let := hq
  exact WeilConjectures.ConstructibleExceptionalCoefficients.mate_shift adj adj' TX TY q b hc

end WeilConjectures.ExceptionalShiftCorrection

namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance 2000] Shrink.instField
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
  (P : RationalStageAssembly.{u, v} l Ω D hl A)

private theorem commonIntegralTor (D : FiniteFieldDatum.{w}) (hl : l ≠ D.p)
    (T : Scheme.{w}) [T.Over (Spec (.of D.k))] (E : FieldStage.{w} l) :
    sfIntegralConstructible l E.carrier T = finiteTorConstructibleIntegral l E.carrier T := by
  let : ∀ x : T, Invertible (l : T.residueField x) :=
    sfCompactSupportScalarResidueUnit l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) T
  exact (integral_residue_tor D l hl E.carrier T).2

private def commonRationalizationW (E : FieldStage.{max u v} l)
    (T : Scheme.{max u v}) : MorphismProperty (C.{u, v} l Ω T (.integral E)) :=
  (Rationalization.W (Submonoid.powers
    (Padic.coefficientExtensionUniformizer l E.carrier))
      (sfIntegralConstructibleCategory l E.carrier T)).inverseImage
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier T)

@[instance_reducible] private def normalizedCommonLeftShift (c : Compactification f)
    (E : FieldStage.{max u v} l) :
    (P.operation c E).F.CommShift ℤ := by
  let : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift.{u, v} l Ω X (.integral E)
  let : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift.{u, v} l Ω Y (.integral E)
  let : (A.operation c (.integral E)).F.CommShift ℤ :=
    (A.operation c (.integral E)).leftShift
  let QX := rationalization.{u, v} l Ω E X
  let QY := rationalization.{u, v} l Ω E Y
  let W := commonRationalizationW.{u, v} l Ω E X
  have : QX.IsLocalization W :=
    rationalizationLocalization.{u, v} l Ω E X (commonIntegralTor l D hl X E)
  let : QX.CommShift ℤ := integralRationalizationShift.{u, v} l Ω E X
  let : QY.CommShift ℤ := integralRationalizationShift.{u, v} l Ω E Y
  let : Localization.Lifting QX W ((A.operation c (.integral E)).F ⋙ QY)
      (P.operation c E).F := ⟨(P.localization c E).q.symm⟩
  exact Functor.commShiftOfLocalization QX W ℤ
    ((A.operation c (.integral E)).F ⋙ QY) (P.operation c E).F

private theorem normalizedCommonLocalizationShift (c : Compactification f)
    (E : FieldStage.{max u v} l) :
    letI : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift l Ω X (.integral E)
    letI : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift l Ω Y (.integral E)
    letI : (A.operation c (.integral E)).F.CommShift ℤ :=
      (A.operation c (.integral E)).leftShift
    letI := integralRationalizationShift.{u, v} l Ω E X
    letI := integralRationalizationShift.{u, v} l Ω E Y
    letI : (P.operation c E).F.CommShift ℤ :=
      normalizedCommonLeftShift.{u, v} l Ω D hl A P c E
    (P.localization c E).q.hom.CommShift ℤ := by
  let : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift.{u, v} l Ω X (.integral E)
  let : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift.{u, v} l Ω Y (.integral E)
  let : (A.operation c (.integral E)).F.CommShift ℤ :=
    (A.operation c (.integral E)).leftShift
  let QX := rationalization.{u, v} l Ω E X
  let QY := rationalization.{u, v} l Ω E Y
  let W := commonRationalizationW.{u, v} l Ω E X
  have : QX.IsLocalization W :=
    rationalizationLocalization.{u, v} l Ω E X (commonIntegralTor l D hl X E)
  let : QX.CommShift ℤ := integralRationalizationShift.{u, v} l Ω E X
  let : QY.CommShift ℤ := integralRationalizationShift.{u, v} l Ω E Y
  let : Localization.Lifting QX W ((A.operation c (.integral E)).F ⋙ QY)
      (P.operation c E).F := ⟨(P.localization c E).q.symm⟩
  let : (P.operation c E).F.CommShift ℤ := normalizedCommonLeftShift.{u, v} l Ω D hl A P c E
  have : (P.localization c E).q.symm.hom.CommShift ℤ :=
    NatTrans.commShift_iso_hom_of_localization QX W ℤ
      ((A.operation c (.integral E)).F ⋙ QY) (P.operation c E).F
  exact NatTrans.CommShift.of_iso_inv (P.localization c E).q.symm ℤ

attribute [local irreducible] normalizedCommonLeftShift

private theorem normalizedCommonLeftExact (c : Compactification f)
    (E : FieldStage.{max u v} l) :
    letI := normalizedCommonLeftShift.{u, v} l Ω D hl A P c E
    (P.operation c E).F.IsTriangulated := by
  let : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift.{u, v} l Ω X (.integral E)
  let : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift.{u, v} l Ω Y (.integral E)
  let : (A.operation c (.integral E)).F.CommShift ℤ :=
    (A.operation c (.integral E)).leftShift
  let QX := rationalization.{u, v} l Ω E X
  let QY := rationalization.{u, v} l Ω E Y
  let : QX.CommShift ℤ := integralRationalizationShift.{u, v} l Ω E X
  let : QY.CommShift ℤ := integralRationalizationShift.{u, v} l Ω E Y
  have : QX.IsTriangulated := rationalizationExact.{u, v} l Ω E X
  have : QY.IsTriangulated := rationalizationExact.{u, v} l Ω E Y
  have : QX.mapArrow.EssSurj :=
    rationalizationArrowEssSurj.{u, v} l Ω E X (commonIntegralTor l D hl X E)
  have : (A.operation c (.integral E)).F.IsTriangulated :=
    (A.operation c (.integral E)).leftExact
  let : (P.operation c E).F.CommShift ℤ := normalizedCommonLeftShift.{u, v} l Ω D hl A P c E
  have : (P.localization c E).q.hom.CommShift ℤ :=
    normalizedCommonLocalizationShift.{u, v} l Ω D hl A P c E
  have : (P.localization c E).q.symm.hom.CommShift ℤ := inferInstance
  exact Functor.isTriangulated_of_precomp_iso (P.localization c E).q.symm

include hl in
/-- Every rational object has a literal finite-Tor integral representative.
Source: Zheng, Construction 6.2; residue Tor identifies the two integral predicates
(blueprint: lem-sf-common-rationalization-object-surjective).

Proof: apply integralRepresentative to the underlying integral object. Residue Tor
identifies the constructible and finite-Tor predicates, so this changes only its
membership proof. Rationalization retains the object literally; proof irrelevance
therefore identifies the result with the original rational object. -/
theorem commonRationalizationSurjective (T : Scheme.{max u v})
    [T.Over (Spec (.of D.k))] (E : FieldStage.{max u v} l) :
    Function.Surjective (rationalization.{u, v} l Ω E T).obj := by
  intro K
  exact ⟨(integralRepresentative.{u, v} l Ω E T (commonIntegralTor l D hl T E)).obj K.obj, rfl⟩

@[irreducible] private def normalizedCommonStageShift (c : Compactification f)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ((rationalCommonLeft A P c).Φ i).CommShift ℤ :=
  normalizedCommonLeftShift.{u, v} l Ω D hl A P c (commonField.{u, v} l Ω i)

private theorem normalizedCommonStageLocalizationShift (c : Compactification f)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    let E := commonField.{u, v} l Ω i
    letI : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift l Ω X (.integral E)
    letI : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift l Ω Y (.integral E)
    letI : (A.operation c (.integral E)).F.CommShift ℤ :=
      (A.operation c (.integral E)).leftShift
    letI := integralRationalizationShift.{u, v} l Ω E X
    letI := integralRationalizationShift.{u, v} l Ω E Y
    letI : (P.operation c E).F.CommShift ℤ := normalizedCommonStageShift l Ω D hl A P c i
    (P.localization c E).q.hom.CommShift ℤ := by
  unfold normalizedCommonStageShift
  exact normalizedCommonLocalizationShift.{u, v} l Ω D hl A P c _

private theorem normalizedCommonStageExact (c : Compactification f)
    (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    letI := normalizedCommonStageShift l Ω D hl A P c i
    ((rationalCommonLeft A P c).Φ i).IsTriangulated := by
  unfold normalizedCommonStageShift
  exact normalizedCommonLeftExact.{u, v} l Ω D hl A P c _

private theorem existsCanonicalCommonLeftShift (c : Compactification f) :
    ∃ s : (rationalCommonLeft A P c).functor.CommShift ℤ,
      letI := s
      (rationalCommonLeft A P c).functor.IsTriangulated ∧
        ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
          letI : ((rationalCommonLeft A P c).Φ i).CommShift ℤ :=
            normalizedCommonStageShift.{u, v} l Ω D hl A P c i
          ((rationalCommonLeft A P c).ιCompFunctorIso i).inv.CommShift ℤ := by
  obtain ⟨s, hs⟩ := sfLocalizationShiftDescent.{max u v, v} l Ω (rationalCommonLeft A P c)
    (fun i ↦ normalizedCommonStageShift.{u, v} l Ω D hl A P c i)
    (rational_common_normalized_scalar_shift l Ω D hl A P c
      (fun i ↦ normalizedCommonStageShift.{u, v} l Ω D hl A P c i)
      (fun i ↦ normalizedCommonStageLocalizationShift.{u, v} l Ω D hl A P c i))
  let := s
  refine ⟨s, ?_, ?_⟩
  · constructor
    intro T hT
    obtain ⟨i, K, hK, ⟨e⟩⟩ :=
      (GeneralAlgebraicallyClosedCoefficients.distinguished_iff T).mp hT
    let : ((rationalCommonLeft A P c).Φ i).CommShift ℤ :=
      normalizedCommonStageShift.{u, v} l Ω D hl A P c i
    have := normalizedCommonStageExact.{u, v} l Ω D hl A P c i
    have := hs i
    have : (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i) ⋙
        (rationalCommonLeft A P c).functor).IsTriangulated :=
      Functor.isTriangulated_of_iso ((rationalCommonLeft A P c).ιCompFunctorIso i).symm
    exact Pretriangulated.isomorphic_distinguished _
      ((((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i) ⋙
        (rationalCommonLeft A P c).functor).map_distinguished K hK) _
      ((rationalCommonLeft A P c).functor.mapTriangle.mapIso e ≪≫
        (Functor.mapTriangleCompIso
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i)
          (rationalCommonLeft A P c).functor).symm.app K)
  · intro i
    let : ((rationalCommonLeft A P c).Φ i).CommShift ℤ :=
      normalizedCommonStageShift.{u, v} l Ω D hl A P c i
    have := hs i
    exact NatTrans.CommShift.of_iso_inv ((rationalCommonLeft A P c).ιCompFunctorIso i) ℤ

@[instance_reducible]
private def commonInclusionCorrection (T : Scheme.{max u v})
    [T.Over (Spec (.of D.k))] (i : AlgebraicallyClosedCoefficients.Index l Ω)
    (s : letI : HasShift (C.{u, v} l Ω T (.integral (commonField.{u, v} l Ω i))) ℤ :=
        shift.{u, v} l Ω T (.integral (commonField.{u, v} l Ω i))
      (rationalization.{u, v} l Ω (commonField.{u, v} l Ω i) T).CommShift ℤ) :
    (commonInclusion.{u, v} l Ω T i).CommShift ℤ := by
  let E := commonField.{u, v} l Ω i
  let : HasShift (C.{u, v} l Ω T (.integral E)) ℤ := shift.{u, v} l Ω T (.integral E)
  let Q := rationalization.{u, v} l Ω E T
  let W := commonRationalizationW.{u, v} l Ω E T
  have : Q.IsLocalization W :=
    rationalizationLocalization.{u, v} l Ω E T (commonIntegralTor l D hl T E)
  exact ExceptionalShiftCorrection.correction Q W (commonInclusion.{u, v} l Ω T i)
    (integralRationalizationShift.{u, v} l Ω E T) s
    (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift i)

private theorem commonRestrictionCorrected (c₀ c : Compactification f)
    (i : AlgebraicallyClosedCoefficients.Index l Ω)
    (s : (rationalCommonLeft A P c).functor.CommShift ℤ)
    (hs : letI := s
      letI : ((rationalCommonLeft A P c).Φ i).CommShift ℤ :=
            normalizedCommonStageShift.{u, v} l Ω D hl A P c i
      ((rationalCommonLeft A P c).ιCompFunctorIso i).inv.CommShift ℤ) :
    let E := commonField.{u, v} l Ω i
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i).CommShift ℤ :=
      commonInclusionCorrection.{u, v} l Ω D hl X i (P.localization c₀ E).shiftX
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).CommShift ℤ :=
      commonInclusionCorrection.{u, v} l Ω D hl Y i (P.localization c₀ E).shiftY
    letI := s
    letI : ((rationalCommonLeft A P c).Φ i).CommShift ℤ := (P.operation c E).leftShift
    ((rationalCommonLeft A P c).ιCompFunctorIso i).inv.CommShift ℤ := by
  let E := commonField.{u, v} l Ω i
  let : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift.{u, v} l Ω X (.integral E)
  let : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift.{u, v} l Ω Y (.integral E)
  let : (A.operation c (.integral E)).F.CommShift ℤ :=
    (A.operation c (.integral E)).leftShift
  let QX := rationalization.{u, v} l Ω E X
  let QY := rationalization.{u, v} l Ω E Y
  let WX := commonRationalizationW.{u, v} l Ω E X
  let WY := commonRationalizationW.{u, v} l Ω E Y
  have : QX.IsLocalization WX :=
    rationalizationLocalization.{u, v} l Ω E X (commonIntegralTor l D hl X E)
  have : QY.IsLocalization WY :=
    rationalizationLocalization.{u, v} l Ω E Y (commonIntegralTor l D hl Y E)
  let := s
  apply ExceptionalShiftCorrection.restrictionChange QX QY WX WY
    (commonRationalizationSurjective.{u, v} l Ω D hl X E)
    (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
    (A.operation c (.integral E)).F (P.operation c E).F
    (rationalCommonLeft A P c).functor (P.localization c E).q
    ((rationalCommonLeft A P c).ιCompFunctorIso i).symm
    (integralRationalizationShift.{u, v} l Ω E X) (P.localization c₀ E).shiftX
    (integralRationalizationShift.{u, v} l Ω E Y) (P.localization c₀ E).shiftY
    (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift i)
    (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift i)
    (normalizedCommonStageShift.{u, v} l Ω D hl A P c i) (P.operation c E).leftShift
  · exact normalizedCommonStageLocalizationShift.{u, v} l Ω D hl A P c i
  · have hq' :
        letI : QX.CommShift ℤ := (P.localization c E).shiftX
        letI : QY.CommShift ℤ := (P.localization c E).shiftY
        letI : (P.operation c E).F.CommShift ℤ := (P.operation c E).leftShift
        (P.localization c E).q.hom.CommShift ℤ := by
      let : QX.CommShift ℤ := (P.localization c E).shiftX
      let : QY.CommShift ℤ := (P.localization c E).shiftY
      let : (P.operation c E).F.CommShift ℤ := (P.operation c E).leftShift
      exact (P.localization c E).comparison.qShift
    simpa +instances only [P.shiftX c c₀ E, P.shiftY c c₀ E] using hq'
  · exact hs

end WeilConjectures.ConstructibleExceptionalCoefficients

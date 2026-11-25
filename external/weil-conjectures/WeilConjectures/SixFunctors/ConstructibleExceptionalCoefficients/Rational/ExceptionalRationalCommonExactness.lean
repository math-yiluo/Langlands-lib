/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalCommonCoherence
import all WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalCommonShiftTransport
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Shift normalization after the unshifted common-field adjunction descent

This is solely the exactness and shift part of Zheng, Construction 6.6.
The quotient functors, adjunction, and inclusion maps are already explicitly constructed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category CategoryTheory.ScalarLocalization.composition
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  WeilConjectures.sfRationalScalarExtension WeilConjectures.sfRationalConstructibleLocalization
  WeilConjectures.sfRationalScalarComp
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.scalarAssociator
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
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

/-- Shift and exactness structures on the explicitly constructed pair functors.
There are no functors, adjunctions, comparison maps or transition equations to choose here.
Endpoint inclusion shifts are chosen once for the whole compactification family.
Source: Zheng, Construction 6.6, common-field descent step 4
(blueprint: lem-sf-rational-common-exact-shifts). -/
structure RationalCommonShiftData where
  inclusionX (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (commonInclusion.{u, v} l Ω X i).CommShift ℤ
  inclusionY (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    (commonInclusion.{u, v} l Ω Y i).CommShift ℤ
  leftShift (c : Compactification f) : (rationalCommonLeft A P c).functor.CommShift ℤ
  rightShift (c : Compactification f) : (rationalCommonRight A P c).functor.CommShift ℤ
  leftExact (c : Compactification f) :
    letI := leftShift c
    (rationalCommonLeft A P c).functor.IsTriangulated
  rightExact (c : Compactification f) :
    letI := rightShift c
    (rationalCommonRight A P c).functor.IsTriangulated
  unitShift (c : Compactification f) :
    letI := leftShift c
    letI := rightShift c
    (rationalCommonAdjunction A P c).unit.CommShift ℤ
  counitShift (c : Compactification f) :
    letI := leftShift c
    letI := rightShift c
    (rationalCommonAdjunction A P c).counit.CommShift ℤ
  qShift (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    letI : ((rationalCommonLeft A P c).Φ i).CommShift ℤ :=
      (P.operation c (commonField.{u, v} l Ω i)).leftShift
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i).CommShift ℤ :=
      inclusionX i
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).CommShift ℤ :=
      inclusionY i
    letI := leftShift c
    ((rationalCommonLeft A P c).ιCompFunctorIso i).inv.CommShift ℤ
  bShift (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    letI : ((rationalCommonRight A P c).Φ i).CommShift ℤ :=
      (P.operation c (commonField.{u, v} l Ω i)).rightShift
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i).CommShift ℤ :=
      inclusionX i
    letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).CommShift ℤ :=
      inclusionY i
    letI := rightShift c
    ((rationalCommonRight A P c).ιCompFunctorIso i).inv.CommShift ℤ

/-- Normalize the shifts of the fixed quotient adjunction, retaining the supplied
rational operation structures and using endpoint inclusion shifts independent of c.
This theorem asserts only shift structures and their exactness and compatibility.
Source: Zheng, Construction 6.6, common-field descent step 4
(blueprint: lem-sf-rational-common-exact-shifts).

Proof: localize each integral left shift through the actual localization comparison,
using canonical integral rationalization shifts. Its inverse comparison commutes
with shifts by the localization construction. Exactness follows from exact
rationalization, arrow essential surjectivity, and the exactness criterion for
precomposition with a localization. The finite normalized scalar square gives the
transition hypothesis of sfLocalizationShiftDescent. Apply that theorem to the
actual common left morphism. Every distinguished triangle is isomorphic to an
included finite-stage triangle, so the finite exactness proves common exactness.
Give the actual right adjoint the induced adjoint shift; the adjunction shift and
triangulated-adjunction theorems prove its exactness and the unit/counit squares.

To recover the supplied finite shifts, correct each endpoint inclusion shift by
localizing its composite with canonical rationalization, now using the supplied
rationalization shift. The localization component formula computes the corrected
inclusion shift on integral representatives. Paste the normalized and supplied
localization q shift squares with the normalized stage restriction square. A
naturality calculation gives the restriction square with corrected inclusions and
the supplied finite left shift. Residue Tor supplies integral representatives of
every rational object. P.shiftX and P.shiftY permit evaluating the endpoint
corrections at one compactification, independently of c. Finally the counit
component formula identifies the right restriction with the mate of the left
one, so mate_shift proves its square using the supplied finite right shift. If
there is no compactification, use canonical inclusion shifts and the other fields
are vacuous. The localization and integer CommShift laws include zero and negative
shifts; no new functor, adjunction or comparison is chosen. -/
theorem exists_rational_common_exact_shifts :
    Nonempty (RationalCommonShiftData.{u, v} l Ω D hl A P) := by
  classical
  by_cases h : Nonempty (Compactification f)
  · let c₀ := Classical.choice h
    choose s hs hrestriction using existsCanonicalCommonLeftShift.{u, v} l Ω D hl A P
    let inclusionX (i : AlgebraicallyClosedCoefficients.Index l Ω) :=
      commonInclusionCorrection.{u, v} l Ω D hl X i
        (P.localization c₀ (commonField.{u, v} l Ω i)).shiftX
    let inclusionY (i : AlgebraicallyClosedCoefficients.Index l Ω) :=
      commonInclusionCorrection.{u, v} l Ω D hl Y i
        (P.localization c₀ (commonField.{u, v} l Ω i)).shiftY
    let rightShift (c : Compactification f) :=
      letI := s c
      (rationalCommonAdjunction A P c).rightAdjointCommShift ℤ
    have hright (c : Compactification f) :
        letI := s c
        letI := rightShift c
        (rationalCommonAdjunction A P c).CommShift ℤ := by
      let := s c
      exact (rationalCommonAdjunction A P c).commShift_of_leftAdjoint ℤ
    have hq (c : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω) :
        letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i).CommShift ℤ :=
          inclusionX i
        letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).CommShift ℤ :=
          inclusionY i
        letI := s c
        letI : ((rationalCommonLeft A P c).Φ i).CommShift ℤ :=
          (P.operation c (commonField.{u, v} l Ω i)).leftShift
        ((rationalCommonLeft A P c).ιCompFunctorIso i).inv.CommShift ℤ :=
      commonRestrictionCorrected.{u, v} l Ω D hl A P c₀ c i (s c) (hrestriction c i)
    refine ⟨{
      inclusionX := inclusionX
      inclusionY := inclusionY
      leftShift := s
      rightShift := rightShift
      leftExact := hs
      rightExact := ?_
      unitShift := ?_
      counitShift := ?_
      qShift := hq
      bShift := ?_ }⟩
    · intro c
      let := s c
      let := rightShift c
      have := hright c
      have := hs c
      exact (rationalCommonAdjunction A P c).isTriangulated_rightAdjoint
    · intro c
      let := s c
      let := rightShift c
      have := hright c
      infer_instance
    · intro c
      let := s c
      let := rightShift c
      have := hright c
      infer_instance
    · intro c i
      let : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι i).CommShift ℤ :=
        inclusionX i
      let : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).CommShift ℤ :=
        inclusionY i
      let := s c
      let := rightShift c
      let E := commonField.{u, v} l Ω i
      let : ((rationalCommonLeft A P c).Φ i).CommShift ℤ := (P.operation c E).leftShift
      let : ((rationalCommonRight A P c).Φ i).CommShift ℤ := (P.operation c E).rightShift
      let : (rationalCommonF A P c i).CommShift ℤ := (P.operation c E).leftShift
      let : (rationalCommonG A P c i).CommShift ℤ := (P.operation c E).rightShift
      have : (rationalCommonFiniteAdjunction A P c i).CommShift ℤ :=
        ⟨(P.operation c E).unitShift, (P.operation c E).counitShift⟩
      have := hright c
      let : (commonInclusion.{u, v} l Ω X i).CommShift ℤ := inclusionX i
      let : (commonInclusion.{u, v} l Ω Y i).CommShift ℤ := inclusionY i
      apply ExceptionalShiftCorrection.mateShiftExplicit (rationalCommonFiniteAdjunction A P c i)
        (rationalCommonAdjunction A P c)
        (commonInclusion.{u, v} l Ω X i) (commonInclusion.{u, v} l Ω Y i)
        ((rationalCommonLeft A P c).ιCompFunctorIso i).symm
        ((rationalCommonRight A P c).ιCompFunctorIso i).inv (hq c i)
      intro M
      change 𝟙 _ ≫ (rationalCommonLeft A P c).functor.map (𝟙 _) ≫
          (rationalCommonAdjunction A P c).counit.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).obj M) =
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).map
          ((rationalCommonFiniteAdjunction A P c i).counit.app M)
      erw [(rationalCommonLeft A P c).functor.map_id, Category.id_comp, Category.id_comp]
      exact StageSystem.Morphism.adjunction_counit_app
        (rationalCommonLeft A P c) (rationalCommonRight A P c)
        (fun j ↦ rationalCommonFiniteAdjunction A P c j)
        (rationalCommonUnit A P c) (rationalCommonCounit A P c)
        (fun _ ↦ rfl) (fun _ ↦ rfl)
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι i).obj M)
  · refine ⟨{
      inclusionX := fun i ↦ GeneralAlgebraicallyClosedCoefficients.inclusionCommShift i
      inclusionY := fun i ↦ GeneralAlgebraicallyClosedCoefficients.inclusionCommShift i
      leftShift := fun c ↦ (h ⟨c⟩).elim
      rightShift := fun c ↦ (h ⟨c⟩).elim
      leftExact := fun c ↦ (h ⟨c⟩).elim
      rightExact := fun c ↦ (h ⟨c⟩).elim
      unitShift := fun c ↦ (h ⟨c⟩).elim
      counitShift := fun c ↦ (h ⟨c⟩).elim
      qShift := fun c ↦ (h ⟨c⟩).elim
      bShift := fun c ↦ (h ⟨c⟩).elim }⟩

end WeilConjectures.ConstructibleExceptionalCoefficients

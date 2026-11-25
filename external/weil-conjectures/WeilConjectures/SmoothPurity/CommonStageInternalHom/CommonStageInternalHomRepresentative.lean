/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData
import WeilConjectures.SmoothPurity.CommonStageInternalHom.CommonStageInternalHomCoherence

/-! # Independence of common-stage internal Hom representatives

Source: the common-stage internal-Hom paragraph of prose-03-02,
using the normalized comparisons of lem-pur-integral-operations-scalar-extension.
(blueprint: lem-weil-common-stage-internal-hom-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open Opposite CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedInternalHom sfRationalScalarExtension ScalarLocalization.category
  ObjectProperty.FullSubcategory.category StageSystem.PairCategory.mkHom
  commonStageHomComparison

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  commonStageHomObject commonStageHomPairAtStage

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (W : Scheme.{u})

namespace CommonStageInternalHom

variable (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
  (L : Index l Ω)
  (h : (commonStageHomObject l Ω W P).stage ≤ L)
  (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
  (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
    (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
  (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
    (commonStageHomPairAtStage l Ω W Q L h').obj.2)

/-- The input arrow represented at a common coefficient stage, with reversed first slot.
Source: the common-stage internal-Hom representative formula.
(blueprint: lem-weil-common-stage-internal-hom-representative). -/
def input : P ⟶ Q :=
  ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom
    (StageSystem.PairCategory.mkHom
      (S := stageSystem l Ω W) (X := Q.obj.1.unop) (Y := P.obj.1.unop) L
      (((Padic.finiteCoefficientFields_properties l Ω).1
        Q.obj.1.unop.stage Q.obj.2.stage).1.trans h')
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h) a).op
    (StageSystem.PairCategory.mkHom
      (S := stageSystem l Ω W) (X := P.obj.2) (Y := Q.obj.2) L
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans h)
      (((Padic.finiteCoefficientFields_properties l Ω).1
        Q.obj.1.unop.stage Q.obj.2.stage).2.trans h') b))

/-- The rational Hom map in the coordinates of the extended output objects.
Source: the common-stage internal-Hom representative formula.
(blueprint: lem-weil-common-stage-internal-hom-representative). -/
def value : (commonStageHomObject l Ω W P).toStage h ⟶
    (commonStageHomObject l Ω W Q).toStage h' :=
  (commonStageHomComparison l Ω W P L h).hom ≫
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
      (ObjectProperty.homMk
        (X := commonStageHomPairAtStage l Ω W P L h)
        (Y := commonStageHomPairAtStage l Ω W Q L h') (Prod.mkHom a.op b)) ≫
    (commonStageHomComparison l Ω W Q L h').inv

/-- Conjugate the rational Hom arrow by the prescribed scalar comparisons.
Source: the common-stage internal-Hom representative formula.
(blueprint: lem-weil-common-stage-internal-hom-representative). -/
def output : commonStageHomObject l Ω W P ⟶ commonStageHomObject l Ω W Q :=
  StageSystem.PairCategory.mkHom
    (S := stageSystem l Ω W)
    (X := commonStageHomObject l Ω W P) (Y := commonStageHomObject l Ω W Q) L h h'
    (value l Ω W P Q L h h' a b)

/-- The normalized Hom arrow commutes with one further coefficient extension.
Source: the existing proof plan of commonStageDerivedInternalHom_existsUnique in
DerivedPullbackTensorHom; lem-pur-integral-operations-scalar-extension,
scalarOperationsOrdinary_tower and scalarHomOrdinary_naturality.
(blueprint: lem-weil-common-stage-internal-hom-representative).

Proof: expand StageSystem.tr as conjugation by the output associators. The
ordinary Hom scalar comparison is the transpose of scalar-extended evaluation.
Its naturality equation moves the scalar-extended arrows through this comparison,
with the reversed first arrow. Apply the Hom clause of
scalarOperationsOrdinary_tower to the coefficient fields at each input's
compositum, L and M. Conjugate by the canonical scalarCompletion isomorphisms:
completion naturality moves them through Hom and scalar extension, and adjacent
inverse completion maps cancel. Restrict this equation to the constructible
full subcategories, and localize it. Rational scalar and Hom comparisons are
uniquely normalized localizations of these integral maps, so their defining
component formulas identify the resulting equation. Substitute the recorded
stage transition and associator specifications and the coefficient-inclusion
tower law. For the two input associators, Hom uses the inverse first associator
and the forward second one. Functoriality cancels their adjacent inverses and
gives exactly the two input transports on the right. Both endpoints remain
permitted by commonStageHomPairAtStage_permitted. Repeated fields and identity
inclusions satisfy these same tower identities; zero arrows and empty schemes
require no separate assumption. This is an equation at a single larger stage,
not an assertion about quotient arrows or an already descended functor. -/
theorem value_transport (M : Index l Ω) (k : L ≤ M) :
    (stageSystem l Ω W).tr k (value l Ω W P Q L h h' a b) =
      value l Ω W P Q M (h.trans k) (h'.trans k)
        ((stageSystem l Ω W).tr k a) ((stageSystem l Ω W).tr k b) := by
  have hs := commonStageHomComparison_hom_square l Ω W P Q L h h' a b M k
  dsimp at hs
  unfold value StageSystem.tr
  exact commonStageHomComparison_hom_square l Ω W P Q L h h' a b M k

private theorem output_transport (M : Index l Ω) (k : L ≤ M) :
    output l Ω W P Q M (h.trans k) (h'.trans k)
        ((stageSystem l Ω W).tr k a) ((stageSystem l Ω W).tr k b) =
      output l Ω W P Q L h h' a b := by
  unfold output
  rw [← value_transport]
  exact StageSystem.PairCategory.mkHom_tr k _

/-- Equal input classes give equal conjugated Hom classes, even at different stages.
Source: prose-03-02, common-stage internal-Hom paragraph;
lem-pur-integral-operations-scalar-extension, naturality and coefficient tower laws.
(blueprint: lem-weil-common-stage-internal-hom-representative).

Proof: equality of the two input classes gives eventual equality separately for the
contravariant and covariant representatives, by mkHom_eq_mkHom_iff'. Directedness
puts both equalities above both initial stages at one finite coefficient field.
Transport each output to that field. Expand transport as conjugation by the
recorded stage associators. The coefficient tower identity for the normalized
Hom scalar comparison identifies the transported output comparison with the
direct comparison, followed by the Hom of the two input associators. Naturality
moves those input associators through the rational Hom map. In the first slot the
associator is inverted before taking the opposite, and in the second slot it has
the forward orientation. Adjacent comparison inverses cancel. Thus the
transported output is the direct comparison conjugating Hom of the two
transported input arrows. The eventual input equalities now give equal output
representatives. Apply mkHom_eq_mkHom_iff' once more. Identity field inclusions,
repeated stages, zero arrows and empty schemes obey the same equations. No
faithfulness of scalar extension or additional constructibility assumption is
used: commonStageHomPairAtStage_permitted supplies the latter at each field. -/
theorem output_eq_of_input_eq
    (M : Index l Ω)
    (k : (commonStageHomObject l Ω W P).stage ≤ M)
    (k' : (commonStageHomObject l Ω W Q).stage ≤ M)
    (a' : (commonStageHomPairAtStage l Ω W Q M k').obj.1.unop ⟶
      (commonStageHomPairAtStage l Ω W P M k).obj.1.unop)
    (b' : (commonStageHomPairAtStage l Ω W P M k).obj.2 ⟶
      (commonStageHomPairAtStage l Ω W Q M k').obj.2)
    (he : input l Ω W P Q L h h' a b = input l Ω W P Q M k k' a' b') :
    output l Ω W P Q L h h' a b = output l Ω W P Q M k k' a' b' := by
  have ha := congrArg (fun f : P ⟶ Q ↦ ((commonStageHomPairs l Ω W).ι.map f).1.unop) he
  have hb := congrArg (fun f : P ⟶ Q ↦ ((commonStageHomPairs l Ω W).ι.map f).2) he
  change StageSystem.PairCategory.mkHom L _ _ a =
    StageSystem.PairCategory.mkHom M _ _ a' at ha
  change StageSystem.PairCategory.mkHom L _ _ b =
    StageSystem.PairCategory.mkHom M _ _ b' at hb
  obtain ⟨N, hLN, hMN, ea⟩ := (StageSystem.PairCategory.mkHom_eq_mkHom_iff' a a').1 ha
  obtain ⟨N', hLN', hMN', eb⟩ := (StageSystem.PairCategory.mkHom_eq_mkHom_iff' b b').1 hb
  obtain ⟨T, hNT, hN'T⟩ := exists_ge_ge N N'
  have ea' := StageSystem.PairCategory.Rep.rel_of_eq
    (r := (⟨L,
      (((Padic.finiteCoefficientFields_properties l Ω).1
        Q.obj.1.unop.stage Q.obj.2.stage).1.trans h'),
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h), a⟩ :
      StageSystem.PairCategory.Rep Q.obj.1.unop P.obj.1.unop))
    (s := (⟨M,
      (((Padic.finiteCoefficientFields_properties l Ω).1
        Q.obj.1.unop.stage Q.obj.2.stage).1.trans k'),
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans k), a'⟩ :
      StageSystem.PairCategory.Rep Q.obj.1.unop P.obj.1.unop))
    hLN hMN ea hNT
  have eb' := StageSystem.PairCategory.Rep.rel_of_eq
    (r := (⟨L,
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans h),
      (((Padic.finiteCoefficientFields_properties l Ω).1
        Q.obj.1.unop.stage Q.obj.2.stage).2.trans h'), b⟩ :
      StageSystem.PairCategory.Rep P.obj.2 Q.obj.2))
    (s := (⟨M,
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans k),
      (((Padic.finiteCoefficientFields_properties l Ω).1
        Q.obj.1.unop.stage Q.obj.2.stage).2.trans k'), b'⟩ :
      StageSystem.PairCategory.Rep P.obj.2 Q.obj.2))
    hLN' hMN' eb hN'T
  calc
    output l Ω W P Q L h h' a b =
        output l Ω W P Q T (h.trans (hLN.trans hNT)) (h'.trans (hLN.trans hNT))
          ((stageSystem l Ω W).tr (hLN.trans hNT) a)
          ((stageSystem l Ω W).tr (hLN.trans hNT) b) :=
      (output_transport l Ω W P Q L h h' a b T (hLN.trans hNT)).symm
    _ = output l Ω W P Q T (k.trans (hMN.trans hNT)) (k'.trans (hMN.trans hNT))
          ((stageSystem l Ω W).tr (hMN.trans hNT) a')
          ((stageSystem l Ω W).tr (hMN.trans hNT) b') := by rw [ea', eb']
    _ = output l Ω W P Q M k k' a' b' :=
      output_transport l Ω W P Q M k k' a' b' T (hMN.trans hNT)

end CommonStageInternalHom
end WeilConjectures

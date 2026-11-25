/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CommonStageInternalHom.CommonStageInternalHomRepresentative

/-! # The arrow calculus for descending common-stage internal Hom

The representative equation determines an arrow map preserving identities and composition.
Source: the existing common-stage internal-Hom proof plan.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus).
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
  StageSystem.PairCategory.mkHom commonStageHomComparison

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] commonStageHomObject commonStageHomPairAtStage
  GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local implicit_reducible] catToReflQuiver

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

namespace CommonStageInternalHomDescent
open CommonStageInternalHom

/-- Every permitted input arrow has a representative above any prescribed stage.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
theorem homRepresentative_exists (W : Scheme.{u})
    (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory) (f : P ⟶ Q)
    (N : Index l Ω) :
    ∃ (L : Index l Ω) (_ : N ≤ L)
      (h : (commonStageHomObject l Ω W P).stage ≤ L)
      (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
      (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
        (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
      (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
        (commonStageHomPairAtStage l Ω W Q L h').obj.2),
      f = input l Ω W P Q L h h' a b := by
  obtain ⟨M, hPM, hQM⟩ := exists_ge_ge
    (commonStageHomObject l Ω W P).stage (commonStageHomObject l Ω W Q).stage
  obtain ⟨M', hMM', hNM'⟩ := exists_ge_ge M N
  obtain ⟨L, hM'L, h₁, h₂, h₃, h₄, a, b, ha, hb⟩ :=
    StageSystem.PairCategory.exists_common_stage
      ((commonStageHomPairs l Ω W).ι.map f).1.unop
      ((commonStageHomPairs l Ω W).ι.map f).2 M'
  refine ⟨L, hNM'.trans hM'L, hPM.trans (hMM'.trans hM'L),
    hQM.trans (hMM'.trans hM'L), a, b, ?_⟩
  apply ObjectProperty.hom_ext
  apply Prod.ext
  · exact congrArg Quiver.Hom.op ha
  · exact hb

/-- Further extension leaves the represented input arrow unchanged.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
theorem homInput_transport (W : Scheme.{u})
    (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L M : Index l Ω)
    (h : (commonStageHomObject l Ω W P).stage ≤ L)
    (h' : (commonStageHomObject l Ω W Q).stage ≤ L) (k : L ≤ M)
    (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
      (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
    (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
      (commonStageHomPairAtStage l Ω W Q L h').obj.2) :
    input l Ω W P Q M (h.trans k) (h'.trans k)
        ((stageSystem l Ω W).tr k a) ((stageSystem l Ω W).tr k b) =
      input l Ω W P Q L h h' a b := by
  apply ObjectProperty.hom_ext
  apply Prod.ext
  · exact congrArg Quiver.Hom.op (StageSystem.PairCategory.mkHom_tr k a)
  · exact StageSystem.PairCategory.mkHom_tr k b

/-- Identity representatives give the identity input arrow.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
theorem homInput_id (W : Scheme.{u})
    (P : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    input l Ω W P P L h h (𝟙 _) (𝟙 _) = 𝟙 P := by
  apply ObjectProperty.hom_ext
  apply Prod.ext
  · exact congrArg Quiver.Hom.op
      (StageSystem.PairCategory.id_eq_mkHom P.obj.1.unop _).symm
  · exact (StageSystem.PairCategory.id_eq_mkHom P.obj.2 _).symm

/-- Normalized identity representatives give the identity output arrow.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
theorem homOutput_id (W : Scheme.{u})
    (P : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    output l Ω W P P L h h (𝟙 _) (𝟙 _) = 𝟙 (commonStageHomObject l Ω W P) := by
  unfold output value
  have hi : ObjectProperty.homMk
      (X := commonStageHomPairAtStage l Ω W P L h)
      (Y := commonStageHomPairAtStage l Ω W P L h)
      (Prod.mkHom (𝟙 _).op (𝟙 _)) = 𝟙 _ := rfl
  rw [hi, (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map_id,
    Category.id_comp, Iso.hom_inv_id]
  exact (StageSystem.PairCategory.id_eq_mkHom _ h).symm

/-- Composition of inputs reverses the first representative slot.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
theorem homInput_comp (W : Scheme.{u})
    (P Q R : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω)
    (hP : (commonStageHomObject l Ω W P).stage ≤ L)
    (hQ : (commonStageHomObject l Ω W Q).stage ≤ L)
    (hR : (commonStageHomObject l Ω W R).stage ≤ L)
    (a : (commonStageHomPairAtStage l Ω W Q L hQ).obj.1.unop ⟶
      (commonStageHomPairAtStage l Ω W P L hP).obj.1.unop)
    (b : (commonStageHomPairAtStage l Ω W P L hP).obj.2 ⟶
      (commonStageHomPairAtStage l Ω W Q L hQ).obj.2)
    (a' : (commonStageHomPairAtStage l Ω W R L hR).obj.1.unop ⟶
      (commonStageHomPairAtStage l Ω W Q L hQ).obj.1.unop)
    (b' : (commonStageHomPairAtStage l Ω W Q L hQ).obj.2 ⟶
      (commonStageHomPairAtStage l Ω W R L hR).obj.2) :
    input l Ω W P Q L hP hQ a b ≫ input l Ω W Q R L hQ hR a' b' =
      input l Ω W P R L hP hR (a' ≫ a) (b ≫ b') := by
  apply ObjectProperty.hom_ext
  apply Prod.ext
  · change (StageSystem.PairCategory.mkHom L _ _ a).op ≫
      (StageSystem.PairCategory.mkHom L _ _ a').op =
        (StageSystem.PairCategory.mkHom L _ _ (a' ≫ a)).op
    rw [← op_comp]
    exact congrArg Quiver.Hom.op (StageSystem.PairCategory.mkHom_comp_mkHom a' a)
  · exact StageSystem.PairCategory.mkHom_comp_mkHom b b'

/-- Normalized outputs compose by cancelling the middle comparison.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
theorem homOutput_comp (W : Scheme.{u})
    (P Q R : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω)
    (hP : (commonStageHomObject l Ω W P).stage ≤ L)
    (hQ : (commonStageHomObject l Ω W Q).stage ≤ L)
    (hR : (commonStageHomObject l Ω W R).stage ≤ L)
    (a : (commonStageHomPairAtStage l Ω W Q L hQ).obj.1.unop ⟶
      (commonStageHomPairAtStage l Ω W P L hP).obj.1.unop)
    (b : (commonStageHomPairAtStage l Ω W P L hP).obj.2 ⟶
      (commonStageHomPairAtStage l Ω W Q L hQ).obj.2)
    (a' : (commonStageHomPairAtStage l Ω W R L hR).obj.1.unop ⟶
      (commonStageHomPairAtStage l Ω W Q L hQ).obj.1.unop)
    (b' : (commonStageHomPairAtStage l Ω W Q L hQ).obj.2 ⟶
      (commonStageHomPairAtStage l Ω W R L hR).obj.2) :
    output l Ω W P Q L hP hQ a b ≫ output l Ω W Q R L hQ hR a' b' =
      output l Ω W P R L hP hR (a' ≫ a) (b ≫ b') := by
  unfold output value
  rw [StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  have hc : ObjectProperty.homMk
      (X := commonStageHomPairAtStage l Ω W P L hP)
      (Y := commonStageHomPairAtStage l Ω W Q L hQ) (Prod.mkHom a.op b) ≫
      ObjectProperty.homMk
        (X := commonStageHomPairAtStage l Ω W Q L hQ)
        (Y := commonStageHomPairAtStage l Ω W R L hR) (Prod.mkHom a'.op b') =
      ObjectProperty.homMk
        (X := commonStageHomPairAtStage l Ω W P L hP)
        (Y := commonStageHomPairAtStage l Ω W R L hR)
        (Prod.mkHom (a' ≫ a).op (b ≫ b')) := by
    apply ObjectProperty.hom_ext
    rfl
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, hc]

/-- All representatives of one input arrow specify exactly one output arrow.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
theorem homArrow_existsUnique (W : Scheme.{u})
    (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory) (f : P ⟶ Q) :
    ∃! g : commonStageHomObject l Ω W P ⟶ commonStageHomObject l Ω W Q,
      ∀ (L : Index l Ω)
        (h : (commonStageHomObject l Ω W P).stage ≤ L)
        (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
        (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
          (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
        (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
          (commonStageHomPairAtStage l Ω W Q L h').obj.2),
        f = input l Ω W P Q L h h' a b → g = output l Ω W P Q L h h' a b := by
  obtain ⟨L, -, h, h', a, b, rfl⟩ :=
    homRepresentative_exists l Ω W P Q f (commonStageHomObject l Ω W P).stage
  refine ⟨output l Ω W P Q L h h' a b, ?_, ?_⟩
  · intro M k k' a' b' he
    exact output_eq_of_input_eq l Ω W P Q L h h' a b M k k' a' b' he
  · intro g hg
    exact hg L h h' a b rfl

/-- The output uniquely determined by the proved representative-independence statement.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
def homArrow (W : Scheme.{u})
    {P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory} (f : P ⟶ Q) :=
  (homArrow_existsUnique l Ω W P Q f).exists.choose

/-- The unique output has the prescribed value on every representative.
Source: the common-stage internal-Hom representative proof.
(blueprint: lem-weil-common-stage-internal-hom-descent-calculus). -/
theorem homArrow_spec (W : Scheme.{u})
    (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
    (L : Index l Ω)
    (h : (commonStageHomObject l Ω W P).stage ≤ L)
    (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
    (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
      (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
    (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
      (commonStageHomPairAtStage l Ω W Q L h').obj.2) :
    homArrow l Ω W (input l Ω W P Q L h h' a b) = output l Ω W P Q L h h' a b :=
  (homArrow_existsUnique l Ω W P Q _).exists.choose_spec L h h' a b rfl

end CommonStageInternalHomDescent
end WeilConjectures

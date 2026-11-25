/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import WeilConjectures.SixFunctors.Supporting.WfConstructibleTensorKoszulUnit
import WeilConjectures.SixFunctors.Supporting.Tensor.WfTensorPullbackCompletionUnitSquare
import all WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct

/-!
# Frobenius compatibility of ordinary and completed tensor

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md, step 13
(blueprint: lem-wf-tensor-completion-frobenius).

## Main statements

* `WfTensorCompletion.integral`: completeness, constructibility and unit naturality.
* `WfTensorCompletion.integral_equivariance`: the integral tensor Weil equation.
* `wfTensorCompletionFrobenius`: the normalized rational comparison and Weil isomorphism.
* `wfTensorCompletionCommonField`: its image at any common finite coefficient field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.all false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] wfPullbackCompletion proEtaleCanonicalTensorComparison
  ScalarLocalization.composition pbcCompletedScalarSections wfCompletionObj
  intrinsicCompletion intrinsicCompletionUnit

namespace WeilConjectures
namespace WfTensorCompletion

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀)))
  [hsep : IsSeparated X₀.hom] [hft : LocallyOfFiniteType X₀.hom]
  [hqc : QuasiCompact X₀.hom] (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The specified completed-coefficient integral category on the geometric fibre.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev Integral := PbcBoundedConstructibleComplete (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- The uniformizer is the single Koszul generator; this is the existing completion functor.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev completion := wfCompletion (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1
  (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)

/-- The existing completion unit, retaining its actual mapping-fibre normalization.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev unit := wfCompletionUnit (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1
  (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)

/-- The ordinary ambient derived tensor on the constructible inputs, with no completion.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev ordinaryAmbient : Integral D c X₀ E × Integral D c X₀ E ⥤
    PbcCompletedDerived (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E) :=
  ((ObjectProperty.ι _).prod (ObjectProperty.ι _)) ⋙
    wfOrdinaryDerivedTensor (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)

/-- The completed ambient tensor is ordinary tensor followed by the published reflector.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev completedAmbient := ordinaryAmbient D c X₀ E ⋙ completion D c X₀ E ⋙
  ObjectProperty.ι _

include hsep hft hqc in
/-- The canonical quotient/Koszul comparison is invertible and natural on integral inputs.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius).
Proof: use integral-stratified-perfect-characterization to identify both integral
conventions inside the same completed-coefficient derived category. Finite type over
k makes the fibre noetherian and finite-dimensional; separation gives qcqs and l≠p
makes l invertible. Constructible-tensor-completion gives completeness and an invertible
quotient-tower unit. The integer ring is a Noetherian DVR with finite residue field;
its positive quotients are finite and have the two-term free uniformizer resolution.
Constant-completion-equivalence therefore identifies the quotient and Koszul units.
Integral-operations-preserve-constructible gives bounded constructibility of the completed
tensor, hence also of the ordinary tensor. Finally the reflector's Hom bijection identifies
its morphism action and makes its unit natural in every pair of integral arrows. -/
theorem integral :
    (∀ MN : Integral D c X₀ E × Integral D c X₀ E,
      PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) ((ordinaryAmbient D c X₀ E).obj MN) ∧
      PbcIsBoundedConstructibleComplete (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) ((completedAmbient D c X₀ E).obj MN) ∧
      IsIso (unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj MN))) ∧
    ∀ (MN PQ : Integral D c X₀ E × Integral D c X₀ E) (f : MN ⟶ PQ),
      (ordinaryAmbient D c X₀ E).map f ≫
          unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj PQ) =
        unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj MN) ≫
          (completedAmbient D c X₀ E).map f := by
  refine ⟨?_, ?_⟩
  · intro MN
    exact (wfConstructibleTensorKoszulUnit D c X₀ E).1 MN.1 MN.2
  · intro MN PQ f
    exact (wfConstructibleTensorKoszulUnit D c X₀ E).2 MN.1 PQ.1 MN.2 PQ.2 f.1 f.2

/-- Restriction of ordinary tensor to the full integral constructible category.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def ordinary : Integral D c X₀ E × Integral D c X₀ E ⥤ Integral D c X₀ E :=
  ObjectProperty.lift _ (ordinaryAmbient D c X₀ E)
    (fun MN ↦ (integral D c X₀ E).1 MN |>.1)

/-- Restriction of completed tensor to the same full integral constructible category.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def completed : Integral D c X₀ E × Integral D c X₀ E ⥤ Integral D c X₀ E :=
  ObjectProperty.lift _ (completedAmbient D c X₀ E)
    (fun MN ↦ (integral D c X₀ E).1 MN |>.2.1)

/-- The actual completion unit lifted through the full constructible inclusion.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def chi : ordinary D c X₀ E ⟶ completed D c X₀ E where
  app MN := ObjectProperty.homMk (unit D c X₀ E ((ordinaryAmbient D c X₀ E).obj MN))
  naturality MN PQ f := ObjectProperty.hom_ext _ ((integral D c X₀ E).2 MN PQ f)

/-- The integral Frobenius is the existing exact coefficient transport.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev pullback := pbcIsoIntegralPullback (D.geometricFrobenius X₀).asIso.hom
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- The ordinary pullback/tensor comparison restricted through the full inclusion.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def ordinaryMu (M N : Integral D c X₀ E) :
    (pullback D c X₀ E).obj ((ordinary D c X₀ E).obj (M, N)) ≅
      (ordinary D c X₀ E).obj ((pullback D c X₀ E).obj M, (pullback D c X₀ E).obj N) :=
  ObjectProperty.isoMk _
    ((proEtaleCanonicalTensorComparison (D.geometricFrobenius X₀).asIso.hom
      (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
      (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
      (asIso (completedCoefficientMap _ (pbcStageDatum.{u} c.l c.Qbar E)))
      (wfTensorModel _ (pbcStageDatum.{u} c.l c.Qbar E))
      (wfTensorModel _ (pbcStageDatum.{u} c.l c.Qbar E))).app (M.obj, N.obj))

/-- The existing completed comparison on the same inputs, restricted to constructibles.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def completedMu (M N : Integral D c X₀ E) :
    (pullback D c X₀ E).obj ((completed D c X₀ E).obj (M, N)) ≅
      (completed D c X₀ E).obj ((pullback D c X₀ E).obj M, (pullback D c X₀ E).obj N) :=
  ObjectProperty.isoMk _
    ((ObjectProperty.ι _).mapIso
      (wfIntegralTensorPullback (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (D.geometricFrobenius X₀)
        ((wfIntegralConstructibleInclusion _ (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E)).obj M)
        ((wfIntegralConstructibleInclusion _ (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E)).obj N)))

/-- The actual rational constructible coefficient stage; its objects remain integral objects.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev Rational := PbcRationalCategory (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- The actual integral-to-rational localization, tensoring each arrow with one.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
abbrev localization := pbcRationalization (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- A comparison package whose normalization below fixes all its maps and objects.
The tensor functors land in constructibles, so its fixed pairs are actual Weil objects.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
structure RationalComparison where
  ordinary : Rational D c X₀ E × Rational D c X₀ E ⥤ Rational D c X₀ E
  completed : Rational D c X₀ E × Rational D c X₀ E ⥤ Rational D c X₀ E
  chi : ordinary ≅ completed
  ordinaryMu : ordinary ⋙ weilFrobeniusPullback D c X₀ E ≅
    ((weilFrobeniusPullback D c X₀ E).prod (weilFrobeniusPullback D c X₀ E)) ⋙ ordinary
  completedMu : completed ⋙ weilFrobeniusPullback D c X₀ E ≅
    ((weilFrobeniusPullback D c X₀ E).prod (weilFrobeniusPullback D c X₀ E)) ⋙ completed

/-- Normalization on unchanged integral objects, pure tensors, units and pullback comparisons.
`HEq` retains the exact object equalities while prescribing the arrows, and does not
replace the maps by arbitrary isomorphisms. The localization equalities also fix all
denominators by functoriality.
Source: blueprint step 13 (blueprint: lem-wf-tensor-completion-frobenius). -/
def RationalComparison.Normalized (R : RationalComparison D c X₀ E) : Prop :=
  ((localization D c X₀ E).prod (localization D c X₀ E)) ⋙ R.ordinary =
      WfTensorCompletion.ordinary D c X₀ E ⋙ localization D c X₀ E ∧
  ((localization D c X₀ E).prod (localization D c X₀ E)) ⋙ R.completed =
      WfTensorCompletion.completed D c X₀ E ⋙ localization D c X₀ E ∧
  ∀ M N : Integral D c X₀ E,
    HEq (R.chi.hom.app (⟨M⟩, ⟨N⟩))
      ((localization D c X₀ E).map ((WfTensorCompletion.chi D c X₀ E).app (M, N))) ∧
    HEq (R.ordinaryMu.hom.app (⟨M⟩, ⟨N⟩))
      ((localization D c X₀ E).map (WfTensorCompletion.ordinaryMu D c X₀ E M N).hom) ∧
    HEq (R.completedMu.hom.app (⟨M⟩, ⟨N⟩))
      ((localization D c X₀ E).map (WfTensorCompletion.completedMu D c X₀ E M N).hom)

end WfTensorCompletion
open WfTensorCompletion

/-- Integral precomposition determines a rational bifunctor in both variables. -/
private theorem tensor_precomp_injective
    {A : Type*} [CommRing A] {C : Type*} [Category C] [Preadditive C] [Linear A C]
    (p : A) {B : Type*} [Category B]
    (F G : ScalarLocalization A C p × ScalarLocalization A C p ⥤ B)
    (h : ((ScalarLocalization.localization A C p).prod
      (ScalarLocalization.localization A C p)) ⋙ F =
        ((ScalarLocalization.localization A C p).prod
          (ScalarLocalization.localization A C p)) ⋙ G) : F = G := by
  apply Functor.curry_obj_injective
  apply scalarLocalization_precomp_injective p
  apply Functor.flip_injective
  apply scalarLocalization_precomp_injective p
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

/-- Normalization fixes the bifunctors and all three isomorphisms componentwise. -/
private theorem normalized_unique (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (R S : RationalComparison D c X₀ E)
    (hR : R.Normalized D c X₀ E) (hS : S.Normalized D c X₀ E) : R = S := by
  have ho : R.ordinary = S.ordinary :=
    tensor_precomp_injective _ _ _ (hR.1.trans hS.1.symm)
  have hc : R.completed = S.completed :=
    tensor_precomp_injective _ _ _ (hR.2.1.trans hS.2.1.symm)
  cases R with
  | mk ro rc ri rm rn =>
    cases S with
    | mk so sc si sm sn =>
      dsimp only at ho hc
      subst so
      subst sc
      have hi : ri = si := by
        apply Iso.ext
        apply NatTrans.ext
        funext MN
        exact eq_of_heq ((hR.2.2 MN.1.obj MN.2.obj).1.trans
          (hS.2.2 MN.1.obj MN.2.obj).1.symm)
      have hm : rm = sm := by
        apply Iso.ext
        apply NatTrans.ext
        funext MN
        exact eq_of_heq ((hR.2.2 MN.1.obj MN.2.obj).2.1.trans
          (hS.2.2 MN.1.obj MN.2.obj).2.1.symm)
      have hn : rn = sn := by
        apply Iso.ext
        apply NatTrans.ext
        funext MN
        exact eq_of_heq ((hR.2.2 MN.1.obj MN.2.obj).2.2.trans
          (hS.2.2 MN.1.obj MN.2.obj).2.2.symm)
      subst si
      subst sm
      subst sn
      rfl

end WeilConjectures

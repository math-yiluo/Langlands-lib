/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorConstruction
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality
import WeilConjectures.SmoothPurity.Supporting.Tensor.RestrictionTensorRepresentativeTransport
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Common-stage pullback/tensor comparison

Source: Stacks 07A4, 0941 and the blueprint common-stage coefficient convention.
(blueprint: def-pur-completed-pullback-tensor-comparison)

The integral, rational and finite constructions are re-exported unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

section CoherentSystems
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private theorem pullbackTensorSequenceRing_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = integralComparisonSequenceRingMap l E f := by
  unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
  rfl

end CoherentSystems

private theorem pullbackTensor_conjugate_hom
    {C D : Type*} [Category* C] [Category* D] (F : D × D ⥤ C)
    {A B T Z : C} {U V U' V' : D}
    (a : A ≅ B) (b : B ≅ T) (m : T ≅ F.obj (U, V))
    (p : U' ≅ U) (q : V' ≅ V) (z : Z ≅ F.obj (U', V')) :
    (a ≪≫ b ≪≫ m ≪≫ F.mapIso (Iso.prod p.symm q.symm) ≪≫ z.symm).hom =
      (a ≪≫ b).hom ≫ m.hom ≫ (z ≪≫ F.mapIso (Iso.prod p q)).inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.prod_hom, Iso.prod_inv, Category.assoc]

section CommonComparison
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory StageHom
  commonStagePullbackObject commonStageTensorObject
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5
attribute [local irreducible] ScalarLocalization.category
attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension rationalPullbackScalarComparison rationalTensorScalarComparison
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso
  canonicalRationalPullbackTensor
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The algebraically closed comparison is the actual common-stage class at
EVERY larger finite coefficient stage, so enlargement and scalar extension are fixed.
Source: blueprint common-stage paragraph (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: represent the comparison at the finite compositum by the preceding formula.
The rational scalar-extension square makes the same formula at any larger stage
the transition of that representative. The inverse formula gives the inverse
class. Every allowed stage therefore represents the same arrow. In particular
the compositum formula determines the arrow, hence determines the isomorphism uniquely. -/
theorem canonicalCommonStagePullbackTensor_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃! e : ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj
        (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (P,Q)) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).obj
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj P,
          ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj Q),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω Y P Q).stage ≤ L),
        HEq e.hom
          (ofHom (commonStagePullbackObject l Ω f (commonStageTensorObject l Ω Y P Q))
            (commonStageTensorObject l Ω X
              (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q))
            L h h ((@pullbackTensorAtCommonStage l _ Ω _ _ _ X Y f hX hY) P Q L h).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let A := commonStagePullbackObject l Ω f (commonStageTensorObject l Ω Y P Q)
    let B := commonStageTensorObject l Ω X
      (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q)
    let H := (commonStageTensorObject l Ω Y P Q).stage
    let S := stageSystem l Ω X
    let c (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : H ≤ L) :=
      pullbackTensorAtCommonStage l Ω f P Q L h
    let d : A ≅ B := S.isoToStage A (show A.stage ≤ H from le_rfl) ≪≫
      (S.ι H).mapIso (c H le_rfl) ≪≫
      (S.isoToStage B (show B.stage ≤ H from le_rfl)).symm
    have hA : (commonStageDerivedPullback l Ω f).obj
        ((commonStageDerivedTensor l Ω Y).obj (P,Q)) = A :=
      ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _).trans
        (congrArg (commonStagePullbackObject l Ω f)
          ((commonStageDerivedTensor_existsUnique l Ω Y).exists.choose_spec.1 P Q))
    have hB : (commonStageDerivedTensor l Ω X).obj
        ((commonStageDerivedPullback l Ω f).obj P,
          (commonStageDerivedPullback l Ω f).obj Q) = B := by
      exact ((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 _ _).trans
        (congrArg₂ (commonStageTensorObject l Ω X)
          ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 P)
          ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 Q))
    let e := eqToIso hA ≪≫ d ≪≫ (eqToIso hB).symm
    have hbase : HEq e.hom (ofHom A B H le_rfl le_rfl (c H le_rfl).hom) := by
      have hd : d.hom = ofHom A B H le_rfl le_rfl (c H le_rfl).hom :=
        (StageSystem.mkHom_eq_isoToStage (S := S) (X := A) (Y := B) (n := H)
          le_rfl le_rfl
          (c H le_rfl).hom).symm
      exact ((conj_eqToHom_iff_heq _ d.hom hA hB).mp rfl).trans (heq_of_eq hd)
    let μ (L : AlgebraicallyClosedCoefficients.Index l Ω) :
        rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y ⋙
          rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f ≅
        (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).prod
          (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f) ⋙
          rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X :=
      NatIso.ofComponents
        (fun MN ↦ canonicalRationalPullbackTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f MN.1 MN.2)
        (fun a ↦ canonicalRationalPullbackTensor_naturality l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f a.1 a.2)
    let a (K : AlgebraicallyClosedCoefficients.Index l Ω) (hK : H ≤ K) :=
      commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω Y P Q) K hK ≪≫
        (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K) f).mapIso
          (commonStageTensorComparison l Ω Y P Q K hK)
    let z (K : AlgebraicallyClosedCoefficients.Index l Ω) (hK : H ≤ K) :=
      commonStageTensorComparison l Ω X
        (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q) K hK ≪≫
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K) X).mapIso
          (Iso.prod
            (commonStagePullbackComparison l Ω f P K
              (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans hK))
            (commonStagePullbackComparison l Ω f Q K
              (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans hK)))
    let g (K : AlgebraicallyClosedCoefficients.Index l Ω) (hK : H ≤ K) :=
      (a K hK).hom ≫ (μ K).hom.app
        (P.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans hK),
         Q.toStage (((Padic.finiteCoefficientFields_properties
         l Ω).1 P.stage Q.stage).2.trans hK)) ≫
        (z K hK).inv
    have hc (K : AlgebraicallyClosedCoefficients.Index l Ω) (hK : H ≤ K) :
        (c K hK).hom = g K hK := by
      exact pullbackTensor_conjugate_hom
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K) X)
        (commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω Y P Q) K hK)
        ((rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K) f).mapIso
          (commonStageTensorComparison l Ω Y P Q K hK))
        (canonicalRationalPullbackTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K)
          f _ _)
        (commonStagePullbackComparison l Ω f P K
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans hK))
        (commonStagePullbackComparison l Ω f Q K
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans hK))
        (commonStageTensorComparison l Ω X
          (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q) K hK)
    have he (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : H ≤ L) :
        HEq e.hom (ofHom A B L h h (c L h).hom) := by
      apply hbase.trans
      apply heq_of_eq
      have ht : ofHom A B H le_rfl le_rfl (g H le_rfl) = ofHom A B L h h (g L h) :=
        restrictionTensorRepresentativeTransport l Ω f μ (by
          intro K L h M N
          exact canonicalRationalPullbackTensor_scalar l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K)
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K L h) f M N) P Q L h
      exact (congrArg (ofHom A B H le_rfl le_rfl) (hc H le_rfl)).trans
        (ht.trans (congrArg (ofHom A B L h h) (hc L h).symm))
    refine ⟨e, he, ?_⟩
    intro e' he'
    exact Iso.ext (eq_of_heq ((he' H le_rfl).trans (he H le_rfl).symm))

/-- The stage-independent canonical comparison in the actual colimit Hom group.
Source: blueprint common-stage paragraph (blueprint: def-pur-completed-pullback-tensor-comparison).
-/
def canonicalCommonStagePullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@CommonStagePullbackTensorComparison l _ Ω _ _ _ X Y f hX hY) := fun P Q ↦
  pullbackTensorUniqueChoice
    ((@canonicalCommonStagePullbackTensor_existsUnique l _ Ω _ _ _ X Y f hX hY) P Q)
end CommonComparison

end WeilConjectures

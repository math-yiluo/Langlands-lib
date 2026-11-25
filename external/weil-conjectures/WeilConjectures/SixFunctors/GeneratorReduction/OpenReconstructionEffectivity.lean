/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenReductionMateLocalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenDvrRingedIdentification
import all WeilConjectures.SixFunctors.Open.OpenQuotientKoszulCompleteness
import all WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import all WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
/-! # Effectivity of the specified open reduction and reconstruction

Source: current blueprint fix-prop-coherence, primitive comparisons
(blueprint: lem-sf-open-reconstruction-effectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem complete_of_iso (W : Scheme.{u})
    {A B : DerivedCategory (scalarReductionSource l E W)} (e : A ≅ B)
    (hA : IsDerivedCompleteUnrestricted l E W A) :
    IsDerivedCompleteUnrestricted l E W B := by
  obtain ⟨D, hlD, P, G, q, hq, a, hprod, δ, hδ⟩ := hA
  let := hprod
  refine ⟨D, hlD, P, G, q, hq, a ≪≫ e, hprod,
    δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ _
  refine Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · apply Pi.hom_ext
    intro n
    simp [Category.assoc]
  · simp
  · simp [Category.assoc, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem tensorUnit_complete (W : Scheme.{u}) :
    IsDerivedCompleteUnrestricted l E W
      (IntegralSystemRealization.calculus l E W).integralClosed.monoidal.tensorUnit := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} W
  let S : CoefficientClosedStructure (coefficientIntegralInternalHom.{u, u} l E W) :=
    (IntegralSystemRealization.calculus l E W).integralClosed
  let A : Sheaf (ProEt.topology W) CommRingCat.{u + 1} :=
    completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  obtain ⟨e, _⟩ := @CategoryTheory.RingedKFlatModel.comparison_exists.{u + 1, u, u, u + 2}
    W.ProEt inferInstance (ProEt.topology W) inferInstance inferInstance A
    (integralTowerHasDerivedCategory l E W) S
    (IntegralSystemRealization.calculus l E W).integralTensorModel
  let N : MonoidalCategory (DerivedCategory (scalarReductionSource l E W)) :=
    @CategoryTheory.RingedDerivedNative.monoidal.{u + 1, u, u, u + 2}
      W.ProEt inferInstance (ProEt.topology W) inferInstance inferInstance A
      (integralTowerHasDerivedCategory l E W)
  let a : S.monoidal.tensorUnit ≅ N.tensorUnit :=
    (N.rightUnitor S.monoidal.tensorUnit).symm ≪≫
      e.app (S.monoidal.tensorUnit, N.tensorUnit) ≪≫
      S.monoidal.leftUnitor N.tensorUnit
  let b : N.tensorUnit ≅ integralConstantCoefficientObject l E W :=
    (@CategoryTheory.RingedDerivedNative.unitIso.{u + 1, u, u, u + 2}
      W.ProEt inferInstance (ProEt.topology W) inferInstance inferInstance A
      (integralTowerHasDerivedCategory l E W)) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ (scalarReductionSource l E W) 0).symm.app
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))
  obtain ⟨D, hl⟩ := exists_coefficientTestDatum l
  exact complete_of_iso l E W (a ≪≫ b).symm
    (integralConstantCoefficient_constructible l E W D hl).2.2.1

private theorem fixedOpenReduction_isIso (system : IntegralSystemRealization.Operations l E)
    (realization : IntegralSystemRealization.RealizationModel l E system) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategory (scalarReductionSource l E X)) :
    IsIso ((realization.openReduction l E j).app K) := by
  let L := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (scalarReductionSource l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  let : L.EssSurj := Localization.essSurj L W
  rw [← NatTrans.isIso_app_iff_of_iso _ (L.objObjPreimageIso K)]
  let P := L.objPreimage K
  let : (pullbackTensorOrdinaryReduction l E X).Additive :=
    (pullbackTensorOrdinary_additive l E X).1
  let : (pullbackTensorOrdinaryReduction l E Y).Additive :=
    (pullbackTensorOrdinary_additive l E Y).1
  let : (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).Additive :=
    (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).left_adjoint_additive
  obtain ⟨s, t, _, he⟩ := IntegralSystemRealization.openReduction_mate_localization l E
    system realization j P
  have : ∀ i, IsIso ((realization.ordinary.openReductionComplex l E j
      (system.extension j) P.obj).f i) := fun i ↦
    IntegralSystemRealization.ordinaryOpenReduction_isIso l E realization.ordinary j
      (system.extension j) (P.obj.X i)
  have : IsIso (realization.ordinary.openReductionComplex l E j
      (system.extension j) P.obj) := HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (DerivedCategory.Q.map
      (realization.ordinary.openReductionComplex l E j (system.extension j) P.obj)) :=
    inferInstance
  exact IsIso.of_isIso_fac_right he

/-- Quasi-compact open extension has invertible canonical reduction mate and
reconstruction unit on complete constructible inputs and on the coefficient unit.
Source: current blueprint, fix-prop-coherence.proof.md, open-factor sentence;
Stacks Tags 03DI, 0GL1 and 0941
(blueprint: lem-sf-open-reconstruction-effectivity).

Proof: a finite-Tor constructible input is derived complete; the coefficient
unit is complete because its surjective quotient tower has completed coefficient
sheaf as limit and zero higher limit. The section-normalized open tensor map
commutes with every quotient transition and gives the canonical reduction
comparison on one flat-term K-flat representative. Quasi-compact open extension
preserves completeness. Normalized reconstruction therefore makes the actual
unit at the extension invertible. The inverse open-adjunction mate defining
openReduction is this same section-normalized map, by the representative
normalization of RealizationModel.reductionPull and uniqueness of adjunction
transposition. Thus its components are invertible as whole-system maps. The empty
open and the identity open use the same construction. -/
theorem openReconstructionEffectivity (system : IntegralSystemRealization.Operations l E)
    (realization : IntegralSystemRealization.RealizationModel l E system) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (K : DerivedCategory (scalarReductionSource l E X))
    (_hK : finiteTorConstructibleIntegral l E X K ∨
      K = (IntegralSystemRealization.calculus l E X).integralClosed.monoidal.tensorUnit) :
    IsIso ((realization.openReduction l E j).app K) ∧
      IsIso ((IntegralSystemRealization.calculus l E Y).adjunction.unit.app
        ((IntegralSystemRealization.ringedOpen l E j).obj K)) := by
  refine ⟨fixedOpenReduction_isIso l E system realization j K, ?_⟩
  have hcomplete : IsDerivedCompleteUnrestricted l E X K := by
    rcases _hK with hK | rfl
    · obtain ⟨D, hl⟩ := exists_coefficientTestDatum l
      exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl K).1 hK.1.1⟩
    · exact tensorUnit_complete l E X
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  have hgen : Ideal.span (Set.range (fun _ : Fin 1 ↦
      Padic.coefficientExtensionUniformizer l E)) = d.ideal := by
    simpa only [Set.range_const] using hd.symm
  obtain ⟨C_X⟩ := dvrCoefficientModel_exists l E d hd X
  obtain ⟨C_Y⟩ := dvrCoefficientModel_exists l E d hd Y
  obtain ⟨O⟩ := dvrOpenModel_exists l E j
  have hI := (openDvrIntrinsicCriterion l E d hgen X C_X K).1 hcomplete
  have hJ := openDvrIntrinsicOpenTransport l E d hgen j C_X C_Y O K hI
  have hcompleteJ := (openDvrIntrinsicCriterion l E d hgen Y C_Y (O.jShriek.obj K)).2 hJ
  obtain ⟨e⟩ := IntegralSystemRealization.openDvr_ringed_identification l E j O
  have hactual := complete_of_iso l E Y (e.app K) hcompleteJ
  obtain ⟨M⟩ := dvrCompletionModel_exists l E d hgen Y C_Y (openDvrSystem l E Y)
  exact dvrActualUnit_isIso l E d hgen Y C_Y M _ hactual

end WeilConjectures.GeneratorReduction

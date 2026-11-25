/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SmoothPurity.Common.CommonStageTensorLineCoherenceNaturality
import WeilConjectures.SmoothPurity.Common.CommonStageTensorRightUnitorNaturality
import WeilConjectures.SmoothPurity.Supporting.Coefficient.RegularCoefficientCoherentReduction
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful

/-! # Natural associativity and the coefficient unit for common-stage tensor

Source: Stacks Project, Tags 06YS, 07A4 and 0941; the common-stage paragraph
of the coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-line-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Fixed-right tensor associativity and its degree-zero regular coefficient unit.

Source: Stacks Project, Tags 06YS, 07A4 and 0941; the common-stage paragraph
of the coefficient operations blueprint.
(blueprint: lem-pur-common-stage-tensor-line-coherence).

Proof: specialize naturality of the prescribed common-stage associator to
identity arrows in the two fixed inputs and assemble with NatIso.ofComponents.
The degree-zero integral twist is the regular completed coefficient. Its
coherent reduction is the system tensor unit, as is the reduction of the
reconstructed integral unit. Full faithfulness lifts their isomorphism;
rational localization and inclusion at the least finite coefficient field
identify the specified zero twist with the reconstructed common-stage unit.
Tensor this isomorphism in the second input. Bifunctoriality gives naturality.
Finally assemble the canonical right unitors using their naturality equation
and compose the resulting natural isomorphisms -/
theorem commonStageTensorLineCoherence
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    let C := generalAlgebraicallyClosedConstructibleCategory l Ω X
    let T := commonStageDerivedTensor l Ω X
    let right (L : C) := (𝟭 C).prod' ((Functor.const C).obj L) ⋙ T
    (∀ (L M : C), Nonempty (right L ⋙ right M ≅ right (T.obj (L, M)))) ∧
      Nonempty (right (sfQbarTwistingCoefficient l X Ω 0) ≅ 𝟭 C) := by
  classical
  dsimp only
  let C := generalAlgebraicallyClosedConstructibleCategory l Ω X
  let T := commonStageDerivedTensor l Ω X
  let right (L : C) := (𝟭 C).prod' ((Functor.const C).obj L) ⋙ T
  have hunit : Nonempty (sfQbarTwistingCoefficient l X Ω 0 ≅
      pullbackTensorCommonUnit l Ω X) := by
    let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)
    let R := integralSystemReduction l E X
    have := (integralSystemReduction_fullyFaithful l E X).1
    have := (integralSystemReduction_fullyFaithful l E X).2
    obtain ⟨e⟩ := regularCoefficient_coherentReduction l E X
    let a : R.obj (sfIntegralTwistingCoefficient l E X 0) ≅
        R.obj (pullbackTensorIntegralUnit l E X) :=
      e ≪≫ (pullbackTensorIntegralUnitReduction l E X).symm
    let b := R.preimageIso a
    let c := (sfRationalConstructibleLocalization l E X).mapIso b
    exact ⟨(GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).ι
      (Padic.finiteCoefficientBase l Ω) |>.mapIso c⟩
  refine ⟨?_, ?_⟩
  · intro L M
    refine ⟨NatIso.ofComponents
      (fun K ↦ pullbackTensorCommonAssociator l Ω X K L M) ?_⟩
    intro K K' f
    have h := commonStageTensorAssociator_naturality l X Ω f (𝟙 L) (𝟙 M)
    have hid : T.map (Prod.mkHom (𝟙 L) (𝟙 M)) = 𝟙 (T.obj (L, M)) :=
      T.map_id (L, M)
    change T.map (Prod.mkHom (T.map (Prod.mkHom f (𝟙 L))) (𝟙 M)) ≫ _ =
      _ ≫ T.map (Prod.mkHom f (𝟙 (T.obj (L, M))))
    change T.map (Prod.mkHom (T.map (Prod.mkHom f (𝟙 L))) (𝟙 M)) ≫ _ =
      _ ≫ T.map (Prod.mkHom f (T.map (Prod.mkHom (𝟙 L) (𝟙 M)))) at h
    rw [hid] at h
    exact h
  · obtain ⟨e⟩ := hunit
    let a : right (sfQbarTwistingCoefficient l X Ω 0) ≅
        right (pullbackTensorCommonUnit l Ω X) :=
      NatIso.ofComponents
        (fun K ↦ T.mapIso (Iso.prod (Iso.refl K) e)) (by
          intro K K' f
          change T.map (Prod.mkHom f (𝟙 _)) ≫
              T.map (Prod.mkHom (𝟙 _) e.hom) =
            T.map (Prod.mkHom (𝟙 _) e.hom) ≫ T.map (Prod.mkHom f (𝟙 _))
          rw [← T.map_comp, ← T.map_comp]
          congr 1
          ext <;> simp)
    let b : right (pullbackTensorCommonUnit l Ω X) ≅ 𝟭 C :=
      NatIso.ofComponents (fun K ↦ pullbackTensorCommonRightUnitor l Ω X K)
        (fun f ↦ commonStageTensorRightUnitor_naturality l X Ω f)
    exact ⟨a ≪≫ b⟩

end WeilConjectures

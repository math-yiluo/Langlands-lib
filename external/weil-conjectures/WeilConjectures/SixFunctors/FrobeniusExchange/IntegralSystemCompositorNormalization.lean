/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Normalization of the integral system compositor

The two constructions use the same strict coefficient systems and are identified by
their actual section-normalized direct-image compositors, before exact localization.
(blueprint: lem-weil-integral-system-compositor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.FrobeniusExchange
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev compositorRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
private abbrev compositorQuotient (n : ℕ) :
    compositorRings l E (n + 1) ⟶ compositorRings l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift

attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheafTransition ProEtale.VaryingRing.coefficientTransition
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  integralComparisonSequencePullback
attribute [local irreducible] constantSheaf
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Adjunction.ofIsRightAdjoint Adjunction.leftAdjointCompIso
  conjugateEquiv conjugateIsoEquiv

-- Both compositor constructions are uniquely normalized by the same section map.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem sequenceComposition_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    integralComparisonSequenceComposition l E f g =
      ProEtale.VaryingRing.moduleGComp (compositorRings l E) (compositorQuotient l E) f g := by
  apply (integralComparisonSequenceComposition_existsUnique l E f g).unique
  · exact (integralComparisonSequenceComposition_existsUnique l E f g).exists.choose_spec
  · refine ⟨ProEtale.VaryingRing.modulePComp (compositorRings l E) (compositorQuotient l E) f g,
      ?_, ?_⟩
    · unfold ProEtale.VaryingRing.moduleGComp ProEtale.VaryingRing.moduleAdj
      apply Iso.ext
      erw [conjugateIsoEquiv_apply_hom]
      exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g))
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (f ≫ g)))
        (ProEtale.VaryingRing.modulePComp (compositorRings l E) (compositorQuotient l E) f g)
    · exact (ProEtale.VaryingRing.modulePComp_existsUnique
        (compositorRings l E) (compositorQuotient l E) f g).choose_spec.1

/-- The actual integral system compositor equals the section-normalized varying-ring
compositor at the lifted quotient coefficient rings.
Source: Stacks 0D6D and 03D3; Zheng 4.10
(blueprint: lem-weil-integral-system-compositor-normalization).
Proof: the varying-ring ordinary direct-image compositor satisfies the same section
formula as the integral compositor. Its conjugate is the varying-ring pullback
compositor by the left-adjoint composition identity. Uniqueness identifies the ordinary
pullback compositors. Exact localization with the standard composition comparison
then identifies the displayed derived compositors. -/
theorem integralComparisonSystemComposition_eq_varyingRing
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    integralComparisonSystemComposition l E f g =
      ProEtale.VaryingRing.gComp
        (fun n ↦ CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))
        (fun n ↦ CommRingCat.ofHom
          (Padic.coefficientExtensionTransition l E (n + 1)).ulift) f g := by
  unfold integralComparisonSystemComposition ProEtale.VaryingRing.gComp
  rw [sequenceComposition_eq]
  rfl

private theorem vertical_pushforward_eq
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    [((𝟭 ℕ).prod F).IsContinuous (coefficientSequenceTopology J)
      (coefficientSequenceTopology K)] (n : ℕ)
    [(Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    [(Prod.sectR n D).IsContinuous K (coefficientSequenceTopology K)]
    {A : Sheaf (coefficientSequenceTopology J) RingCat.{u + 1}}
    {B : Sheaf (coefficientSequenceTopology K) RingCat.{u + 1}}
    {S : Sheaf J RingCat.{u + 1}} {T : Sheaf K RingCat.{u + 1}}
    (a : S ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1}
      J (coefficientSequenceTopology J)).obj A)
    (b : T ⟶ ((Prod.sectR n D).sheafPushforwardContinuous RingCat.{u + 1}
      K (coefficientSequenceTopology K)).obj B)
    (φ : A ⟶ (((𝟭 ℕ).prod F).sheafPushforwardContinuous RingCat.{u + 1}
      (coefficientSequenceTopology J) (coefficientSequenceTopology K)).obj B)
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj T)
    (h : ∀ U : Cᵒᵖ, a.hom.app U ≫ φ.hom.app (Opposite.op (n, U.unop)) =
      ψ.hom.app U ≫ b.hom.app (F.op.obj U)) :
    SheafOfModules.pushforward.{u + 1} φ ⋙ SheafOfModules.pushforward a =
      SheafOfModules.pushforward b ⋙ SheafOfModules.pushforward ψ := by
  have := Functor.isContinuous_comp (Prod.sectR n C) ((𝟭 ℕ).prod F)
    J (coefficientSequenceTopology J) (coefficientSequenceTopology K)
  have := Functor.isContinuous_comp F (Prod.sectR n D)
    J K (coefficientSequenceTopology K)
  have he : a ≫ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1}
      J (coefficientSequenceTopology J)).map φ =
      ψ ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map b := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact h U
  change SheafOfModules.pushforward
      (F := (Prod.sectR n C) ⋙ (𝟭 ℕ).prod F)
      (a ≫ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{u + 1}
        J (coefficientSequenceTopology J)).map φ) = _
  exact congrArg (fun θ ↦ SheafOfModules.pushforward
    (F := (Prod.sectR n C) ⋙ (𝟭 ℕ).prod F) θ) he

end WeilConjectures.FrobeniusExchange

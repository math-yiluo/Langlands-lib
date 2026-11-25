/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
import WeilConjectures.CategoryTheory.MonoidalConjugate

/-! # The canonical monoidal structure on condensed module pushforward -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The lax monoidal structure on module direct image induced by its strong monoidal
left adjoint. Source: monoidal adjunction, latest blueprint `prop-kernel-lisse.proof.md`
(blueprint: lem-kernel-condensed-pushforward-monoidal). -/
@[instance_reducible]
def moduleLowerStarMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar Λ f).LaxMonoidal :=
  (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal

attribute [local instance] moduleLowerStarMonoidal

/-- The canonical module inverse/direct image adjunction is monoidal.
Source: monoidal-adjunction construction
(blueprint: lem-kernel-condensed-pushforward-monoidal). -/
instance moduleAdjunctionIsMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarLowerStarAdjunction Λ f).IsMonoidal := by
  change @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
    (upperStarLowerStarAdjunction Λ f) _
    (upperStarLowerStarAdjunction Λ f).rightAdjointLaxMonoidal
  infer_instance

/-- The composition comparison of module direct images is monoidal for their canonical
lax monoidal structures.

Source: latest blueprint `prop-kernel-lisse.proof.md`, multiplication on the pushforward
algebra (blueprint: lem-kernel-condensed-pushforward-monoidal).

Proof. The tensor comparison identity for inverse-image composition makes that natural
isomorphism monoidal, using the comonoidal criterion for a strong monoidal isomorphism.
Both adjunctions are monoidal, including the composite adjunction. Conjugating the
inverse-image comparison gives the direct-image composition comparison, and conjugation
preserves monoidality by the explicit unit/counit formula. -/
theorem moduleLowerStarCompIsMonoidal {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (lowerStarComp Λ f g).hom := by
  have : NatTrans.IsMonoidal (upperStarComp Λ f g).hom :=
    NatTrans.IsMonoidal.of_isIso_of_δ _
      (fun M N ↦ (upperStarComp_hom_app_tensor_δ Λ f g M N).symm)
  have := Adjunction.isMonoidal_comp
    (upperStarLowerStarAdjunction Λ g) (upperStarLowerStarAdjunction Λ f)
  have h := isMonoidal_rightConjugate
    ((upperStarLowerStarAdjunction Λ g).comp (upperStarLowerStarAdjunction Λ f))
    (upperStarLowerStarAdjunction Λ (f ≫ g)) (upperStarComp Λ f g).hom
  rw [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarComp] at h
  exact h

/-- Congruence transport of module direct images is monoidal.
Source: equality transport (blueprint: lem-kernel-condensed-pushforward-monoidal). -/
theorem moduleLowerStarCongrIsMonoidal {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    NatTrans.IsMonoidal (lowerStarCongr Λ h).hom := by
  subst h
  change NatTrans.IsMonoidal (𝟙 (lowerStar Λ f))
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing

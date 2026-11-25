/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization

/-! # Unbounded support projection formulas

This isolates steps 1--7 of the internal Hom calculation, before tensor-Hom adjunction.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The unit-induced open and closed tensor projections are isomorphisms.
Source: Stacks Tags 03EL, 09AA, 09BN, 09AH, 06YS, 0G7D; steps 1--7 of
lem-sfb-open-closed-internal-hom-formulas
(blueprint: lem-sfb-condensed-support-projection-formula).

Proof: use derived open/closed localization and the existing normalized pullback tensor
comparison. Open restriction kills the tensor of a closed image with any object, so the
supported closed unit is invertible. The pullback tensor comparison and the tensor of the
closed counit are invertible, proving the canonical closed projection invertible.
For the open projection, closed restriction has zero source and target. Under open
restriction, its composite with the invertible open unit is its adjunction transpose:
the tensor of the open unit followed by the inverse pullback tensor comparison. Thus the
open restriction is invertible too, and joint detection proves the projection invertible.
The normalized pullback comparison already contains the required K-flat descent, so it is
not constructed again here. Empty strata and zero coefficients are permitted -/
theorem openClosedSupportProjectionFormula {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    let := closedSupport_lowerStarExact Λ i j hij
    (∀ P T, IsIso (closedSupportProjection Λ i P T)) ∧
    (∀ L T, IsIso (openSupportProjection Λ j L T)) := by
  let := closedSupport_lowerStarExact Λ i j hij
  obtain ⟨hu, hc, hs, hio, hjc, hd⟩ := condensedSupportDerivedLocalization Λ i j hij
  let _ := hu
  let _ := hc
  constructor
  · intro P T
    have hz : IsZero ((supportPullback Λ j).mapDerivedCategory.obj
        (((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T)) := by
      exact ((tensorRight ((supportPullback Λ j).mapDerivedCategory.obj T)).map_isZero
        (hjc P)).of_iso
          (supportDerivedTensorComparison Λ j
            ((lowerStar Λ i).mapDerivedCategory.obj P) T)
    have := hs _ hz
    unfold closedSupportProjection
    infer_instance
  · intro L T
    apply hd
    · have hsrc := hio (((derivedTensor Λ U).obj L).obj
        ((supportPullback Λ j).mapDerivedCategory.obj T))
      have htgt : IsZero ((supportPullback Λ i).mapDerivedCategory.obj
          (((derivedTensor Λ X).obj
            ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).obj T)) := by
        exact ((tensorRight ((supportPullback Λ i).mapDerivedCategory.obj T)).map_isZero
          (hio L)).of_iso
            (supportDerivedTensorComparison Λ i
              ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L) T)
      exact isIso_of_source_target_iso_zero _ hsrc.isoZero htgt.isoZero
    · have hh : IsIso ((openSupportDerivedAdjunction Λ j).homEquiv _ _
          (openSupportProjection Λ j L T)) := by
        simp only [openSupportProjection, Equiv.apply_symm_apply]
        infer_instance
      have hcomp : IsIso ((openSupportDerivedAdjunction Λ j).unit.app
          (((derivedTensor Λ U).obj L).obj
            ((supportPullback Λ j).mapDerivedCategory.obj T)) ≫
          (supportPullback Λ j).mapDerivedCategory.map (openSupportProjection Λ j L T)) := by
        rw [← (openSupportDerivedAdjunction Λ j).homEquiv_unit _ _
          (openSupportProjection Λ j L T)]
        infer_instance
      exact IsIso.of_isIso_comp_left
        ((openSupportDerivedAdjunction Λ j).unit.app
          (((derivedTensor Λ U).obj L).obj
            ((supportPullback Λ j).mapDerivedCategory.obj T)))
        ((supportPullback Λ j).mapDerivedCategory.map (openSupportProjection Λ j L T))

end AlgebraicGeometry.ProEtale.CondensedRing

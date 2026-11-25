/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!

# Topological invariance for module objects

Let `Λ` be a commutative condensed ring and `r : X ⟶ Y` a universal homeomorphism of schemes. By
topological invariance of the small pro-étale topos
(`ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism`), the pullback `r^*` of module
objects over `Λ` is an equivalence of categories
(`ProEtale.CondensedRing.isEquivalence_upperStar_of_isUniversalHomeomorphism`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Topological invariance for module objects**: the pullback `r^*` of module objects over `Λ`
along a universal homeomorphism `r` is an equivalence of categories. The lift of the adjunction
`r^* ⊣ r_*` of sheaves to module objects has invertible unit and counit, these being computed on
the underlying sheaves, and the extension of scalars along `α_r` is an equivalence. -/
theorem isEquivalence_upperStar_of_isUniversalHomeomorphism {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsUniversalHomeomorphism r] : (r)^*⟦Λ⟧.IsEquivalence := by
  have := ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism Ab.{u + 1} r
  have := ProEtale.isEquivalence_upperStar_of_isUniversalHomeomorphism Ab.{u + 1} r
  have : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).unit :=
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).unit_isIso_of_L_fully_faithful
  have : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).counit :=
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).counit_isIso_of_R_fully_faithful
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).mapModAdjunction
    (condensedRingObj Λ Y)
  have : IsIso adj.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
    have : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_unit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso adj.counit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
    have : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : ((r)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).IsEquivalence :=
    adj.toEquivalence.isEquivalence_functor
  unfold upperStar
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing

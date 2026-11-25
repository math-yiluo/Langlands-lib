/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# The pushforward along a closed immersion on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `i : Z ⟶ X` a closed immersion. The pushforward
`i_*` on module objects over `Λ` is fully faithful
(`ProEtale.CondensedRing.fullyFaithfulLowerStarOfIsClosedImmersion`), i.e. the counit
`i^* i_* N ⟶ N` of `i^* ⊣ i_*` is an isomorphism
(`ProEtale.CondensedRing.isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion`,
blueprint `proposition-extension-zero-restriction-closed-subscheme--5`).

The adjunction `i^* ⊣ i_*` on module objects is the lift `mapMod(i^*) ⊣ mapMod(i_*)` of the
adjunction on abelian sheaves, whose counit is the counit on underlying sheaves, an isomorphism
(`ProEtale.isIso_upperStarLowerStarAdjunction_counit`), composed with the extension
and restriction of scalars along the isomorphism `α_i`, an equivalence.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The pushforward `i_*` along a closed immersion is fully faithful on module objects over
`Λ`. -/
noncomputable def fullyFaithfulLowerStarOfIsClosedImmersion : ((i)_*⟦Λ⟧).FullyFaithful := by
  have := ProEtale.isIso_upperStarLowerStarAdjunction_counit Ab.{u + 1} i
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
    (condensedRingObj Λ X)
  have : IsIso adj.counit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
    have : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact ((Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).fullyFaithfulFunctor.comp
    adj.fullyFaithfulROfIsIsoCounit).ofIso (comapPullbackHomCompIso Λ i)

instance : ((i)_*⟦Λ⟧).Full := (fullyFaithfulLowerStarOfIsClosedImmersion Λ i).full

instance : ((i)_*⟦Λ⟧).Faithful := (fullyFaithfulLowerStarOfIsClosedImmersion Λ i).faithful

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--5`, for module objects over
`Λ`: the counit `i^* i_* N ⟶ N` of `i^* ⊣ i_*` along a closed immersion is an isomorphism. -/
instance isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion :
    IsIso (upperStarLowerStarAdjunction Λ i).counit :=
  (upperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful

end AlgebraicGeometry.ProEtale.CondensedRing

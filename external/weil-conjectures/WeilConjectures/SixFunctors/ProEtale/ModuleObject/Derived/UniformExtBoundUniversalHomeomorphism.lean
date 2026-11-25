/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.TopologicalInvariance

/-!
# Descent of the uniform `Ext` bound along universal homeomorphisms

Let `r : Y ⟶ X` be a universal homeomorphism. The pullback `r^*` of module objects over a
condensed ring `Λ` is an equivalence of categories
(`ProEtale.CondensedRing.isEquivalence_upperStar_of_isUniversalHomeomorphism`) preserving
constructibility, so the uniform `Ext` bound for constructible `Λ_Y`-modules implies the one for
constructible `Λ_X`-modules
(`ProEtale.CondensedRing.HasUniformConstructibleExtBound.of_isUniversalHomeomorphism`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The uniform `Ext` bound descends along universal homeomorphisms**: the pullback `r^*` is an
exact equivalence preserving constructibility, so it identifies `Hom(M[0], B[n])` with
`Hom((r^* M)[0], (r^* B)[n])`. -/
theorem HasUniformConstructibleExtBound.of_isUniversalHomeomorphism {X Y : Scheme.{u}}
    (r : Y ⟶ X) [IsUniversalHomeomorphism r]
    (h : HasUniformConstructibleExtBound (condensedRingObj Λ Y)) :
    HasUniformConstructibleExtBound (condensedRingObj Λ X) := by
  intro M hM
  let F := (r)^*⟦Λ⟧
  have : F.IsEquivalence := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ r
  obtain ⟨N, hN⟩ := h (F.obj M) (IsConstructibleModuleObject.upperStar Λ r hM)
  refine ⟨N, fun B hB n hn f ↦ F.mapDerivedCategory.map_injective ?_⟩
  have := hN (F.obj B) (IsConstructibleModuleObject.upperStar Λ r hB) n hn
    ((F.mapDerivedCategorySingleFunctor 0).inv.app M ≫ F.mapDerivedCategory.map f ≫
      (F.mapDerivedCategorySingleFunctor n).hom.app B)
  rw [Functor.map_zero, ← cancel_epi ((F.mapDerivedCategorySingleFunctor 0).inv.app M),
    ← cancel_mono ((F.mapDerivedCategorySingleFunctor n).hom.app B)]
  simpa using this

end AlgebraicGeometry.ProEtale.CondensedRing

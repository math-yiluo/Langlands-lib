/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisContinuityGenerated
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerRestrictProjector
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleGenerated

/-!

# Stabilization of nearby cycles along the Galois layers from finiteness, torsion coefficients

Let `N` be a model, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois extension whose finite
subextensions have degrees invertible in a finite discrete ring `T₀`, and `C` a complex whose
restriction to the generic fibre is bounded below of étale origin. If the nearby cycles
`Ψ_{N_Ω} C` of the Galois layer are bounded constructible on the quasi-compact quasi-separated
special fibre, then they *stabilize* at a finite Galois layer: there is a finite Galois
subextension `L'` such that the pullback exchange of the change of Galois layers `N_Ω ⟶ N_{L'}`
is invertible
(`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_of_boundedConstructible`).

The cohomology sheaves of `Ψ_{N_Ω} C` are finitely generated
(`ProEtale.CondensedRing.isGeneratedByFinitelyPresentable_homology_of_boundedConstructible`), so
an open subgroup `Gal(Ω/L')` acts trivially on them by continuity
(`NearbyCyclesModel.exists_forall_mem_finset_homology_galoisLayerAction_eq_id_of_isGenerated`),
and then the nearby cycles of `N_{L'}` are all of `Ψ_{N_Ω} C`
(`NearbyCyclesModel.isIso_pullbackExchange_galoisLayerRestrict_of_homology`). This replaces the
noetherianity hypothesis of
`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_of_isNoetherianObject`,
which does not hold for pro-étale sheaves in general.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]
  (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]

/-- **Nearby cycles stabilize at a finite Galois layer** (torsion coefficients): if
`Ψ_{N_Ω} (L(𝟙)^* C)` is bounded constructible on the quasi-compact quasi-separated special fibre,
there is a finite Galois subextension `L'` of `Ω/L` such that the pullback exchange of the change
of Galois layers `N_Ω ⟶ N_{L'}` is invertible at `L(𝟙)^* C`. -/
theorem exists_isIso_pullbackExchange_galoisLayerRestrict_of_boundedConstructible
    [QuasiCompact N.j] [QuasiSeparated N.j] [CompactSpace X'] [QuasiSeparatedSpace X']
    (hp : ∀ M : IntermediateField L Ω, FiniteDimensional L M →
      IsUnit ((Module.finrank L M : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (hΨ : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T₀) X')
      (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω,
      IsIso (((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
        (Profinite.continuousMapRingObj T₀)).app
          (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) := by
  obtain ⟨⟨a, b, hzero⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 hΨ
  obtain ⟨L', hL'⟩ := N.exists_forall_mem_finset_homology_galoisLayerAction_eq_id_of_isGenerated
    h Ω T₀ C hC (Finset.Icc a b) fun q _ ↦
      isGeneratedByFinitelyPresentable_homology_of_boundedConstructible T₀ hΨ q
  refine ⟨L', N.isIso_pullbackExchange_galoisLayerRestrict_of_homology h Ω
    L'.toIntermediateField T₀ hp C hC fun q σ hσ ↦ ?_⟩
  by_cases hq : q ∈ Finset.Icc a b
  · exact hL' q hq σ fun x ↦
      (IntermediateField.mem_fixingSubgroup_iff L'.toIntermediateField σ).1 hσ x x.2
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hq
    exact (hzero q (hq.imp id id)).eq_of_src _ _

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

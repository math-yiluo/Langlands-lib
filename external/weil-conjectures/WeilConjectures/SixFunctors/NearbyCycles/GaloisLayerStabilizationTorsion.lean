/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisContinuityNoetherian
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerRestrictProjector

/-!

# Stabilization of nearby cycles along the Galois layers, torsion coefficients

Let `N` be a model, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois extension whose finite
subextensions have degrees invertible in a finite discrete ring `T₀`, and `C` a complex whose
restriction to the generic fibre is bounded below of étale origin. If the cohomology sheaves of
the nearby cycles `Ψ_{N_Ω} C` of the Galois layer are noetherian and vanish outside a finite
range of degrees (which holds when `Ψ_{N_Ω} C` is bounded constructible), then the nearby cycles
*stabilize* at a finite Galois layer: there is a finite Galois subextension `L'` such that the
pullback exchange of the change of Galois layers `N_Ω ⟶ N_{L'}` is invertible
(`NearbyCyclesModel.exists_isIso_pullbackExchange_galoisLayerRestrict_of_isNoetherianObject`).

This is the stabilization input of
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_isIso`: an open subgroup
`Gal(Ω/L')` acts trivially on the cohomology sheaves by continuity
(`NearbyCyclesModel.exists_forall_mem_finset_homology_galoisLayerAction_eq_id`), and then the
nearby cycles of `N_{L'}` are all of `Ψ_{N_Ω} C`
(`NearbyCyclesModel.isIso_pullbackExchange_galoisLayerRestrict_of_homology`).

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

/-- **Nearby cycles stabilize at a finite Galois layer** (torsion coefficients): if the
cohomology sheaves of `Ψ_{N_Ω} (L(𝟙)^* C)` are noetherian and vanish outside `[a, b]`, there is a
finite Galois subextension `L'` of `Ω/L` such that the pullback exchange of the change of Galois
layers `N_Ω ⟶ N_{L'}` is invertible at `L(𝟙)^* C`. -/
theorem exists_isIso_pullbackExchange_galoisLayerRestrict_of_isNoetherianObject
    [QuasiCompact N.j] [QuasiSeparated N.j]
    (hp : ∀ M : IntermediateField L Ω, FiniteDimensional L M →
      IsUnit ((Module.finrank L M : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (a b : ℤ) (hzero : ∀ q, q < a ∨ b < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))))
    (hnoeth : ∀ q, IsNoetherianObject ((DerivedCategory.homologyFunctor _ q).obj
      (((N.galoisLayer h Ω).nearbyCycles (Profinite.continuousMapRingObj T₀)).obj
        (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))) :
    ∃ L' : FiniteGaloisIntermediateField L Ω,
      IsIso (((N.galoisLayerRestrict h Ω L'.toIntermediateField).pullbackExchange
        (Profinite.continuousMapRingObj T₀)).app
          (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)) := by
  obtain ⟨L', hL'⟩ := N.exists_forall_mem_finset_homology_galoisLayerAction_eq_id h Ω T₀ C hC
    (Finset.Icc a b) fun q _ ↦ hnoeth q
  refine ⟨L', N.isIso_pullbackExchange_galoisLayerRestrict_of_homology h Ω
    L'.toIntermediateField T₀ hp C hC fun q σ hσ ↦ ?_⟩
  by_cases hq : q ∈ Finset.Icc a b
  · exact hL' q hq σ fun x ↦
      (IntermediateField.mem_fixingSubgroup_iff L'.toIntermediateField σ).1 hσ x x.2
  · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hq
    exact (hzero q (hq.imp id id)).eq_of_src _ _

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

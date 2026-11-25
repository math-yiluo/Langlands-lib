/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitExists
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUnramified
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelWeaklyEtale
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeFiniteCoefficient

/-!

# The slice step of Deligne's induction with finite coefficients

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic exponent `p`, and `T` a finite
discrete ring in which `p` is invertible. For a complex `C` of `T̲`-modules on `𝔸ⁿ⁺¹_S` which is
bounded below of étale origin and a coordinate `i`, the pullback exchange
`α : Lhᵢ,ₛ^* Ψ C ⟶ Ψ_K (Lhᵢ^* C)` of the morphism of geometric models over the coordinate generic
slice (`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite`; SGA 4½,
[Th. finitude], Lemme 3.3). As for `ℚ̄_ℓ`-coefficients
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`), the slice factors
through a generic slice trait `S'` (`AlgebraicGeometry.nonempty_genericSliceTrait`): the change of
trait `Spec K⟦t⟧ ⟶ S'` has invertible exchange by Th. finitude 3.7 with finite coefficients
(`ProEtale.CondensedRing.isIso_pullbackExchange_app_of_isPullback_trait_finite`), and the slice
over `S' ⟶ S` has split exchange: weakly étale base change, then the averaging (M2) with finite
coefficients
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom_of_finite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

/-- A natural number vanishing in the residue field of a generic slice trait vanishes in `k'`:
the residue field embeds into `K = k'(x)^alg`, an extension of `k'`. -/
lemma natCast_eq_zero_of_residueField (m : ℕ) (hm : (m : IsLocalRing.ResidueField D.R) = 0) :
    (m : k') = 0 := by
  have h₁ : (m : D.R) ∈ IsLocalRing.maximalIdeal D.R := by
    rwa [← map_natCast (IsLocalRing.residue D.R), IsLocalRing.residue_eq_zero_iff] at hm
  have h₂ : D.b m = 0 := by rwa [← RingHom.mem_ker, D.ker_b]
  have h₃ : (m : traitSliceField k') = 0 := by
    rw [← map_natCast D.κK, ← map_natCast D.b, h₂, map_zero]
  exact (algebraMap k' (traitSliceField k')).injective (by rw [map_natCast, h₃, map_zero])

end AlgebraicGeometry.GenericSliceTrait

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] [IsSepClosed k']
  (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

omit [IsSepClosed k'] in
/-- **Change of trait to the generic slice trait, finite coefficients** (SGA 4½, [Th. finitude],
3.7): the pullback exchange of the change of strictly henselian trait
`τ : (𝔸ⁿ_{K⟦t⟧} over Spec K⟦t⟧) ⟶ (𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S' over S')` is an isomorphism at the pullback
of a complex `C` on `𝔸ⁿ⁺¹_S` bounded below of étale origin, with coefficients a finite ring in
which the characteristic exponent `p` of `k'` is invertible. -/
theorem isIso_pullbackExchange_app_genericSliceTraitChangeHom_of_finite
    (D : GenericSliceTrait k') (n : ℕ) (i : Fin (n + 1)) {p : ℕ} [Fact p.Prime]
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
        (affineSpaceModel k' (n + 1)).total))}
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T))
      (affineSpaceModel k' (n + 1)).total
      ((finiteCoefficientDerivedEquivalence (affineSpaceModel k' (n + 1)).total T).functor.obj
        C)) :
    IsIso (((genericSliceTraitChangeHom D n i).pullbackExchange
      (Profinite.continuousMapRingObj T)).app
        ((L((genericSliceTraitProj D n i)^*⟦Profinite.continuousMapRingObj T⟧)).obj C)) := by
  have hC' := plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
    (genericSliceTraitModel D n i).ε
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T
      (genericSliceTraitProj D n i) hC)
  have hNj : IsPullback (genericSliceTraitModel D n i).j (pullback.snd _ _)
      (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.a)) :=
    IsPullback.of_hasPullback _ _
  have hMj : IsPullback (affineSpaceModel (traitSliceField k') n).geometric.j (pullback.snd _ _)
      (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k'))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (PowerSeries (traitSliceField k'))
          (traitGenericField (traitSliceField k'))))) :=
    IsPullback.of_hasPullback _ _
  have hMi : IsPullback (affineSpaceModel (traitSliceField k') n).geometric.i (pullback.snd _ _)
      (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘ trait (traitSliceField k'))
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := traitSliceField k')))) :=
    IsPullback.of_hasPullback _ _
  have hφ := isPullback_genericSliceTraitChangeTotal D n i
  have hgen : (genericSliceTraitChangeHom D n i).generic ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωK) := pullback.lift_snd _ _ _
  have hp' (m : ℕ) (hm : (m : IsLocalRing.ResidueField D.R) = 0) : p ∣ m :=
    hp m (D.natCast_eq_zero_of_residueField m hm)
  have h := isIso_pullbackExchange_app_of_isPullback_trait_finite T (ι := D.ι) (a₁ := D.a)
    (a₂ := algebraMap _ _) (c := D.ωK) (b₂ := PowerSeries.constantCoeff)
    D.injective_ι D.maximalIdeal_eq_map_ι p hp' hpT D.injective_a
    (algebraMap_traitGenericField_injective _) D.isAlgebraic_a
    (isAlgebraic_traitGenericField _) D.ωK_comp_a
    PowerSeries.ker_coeff_eq_max_ideal (genericSliceTraitChangeHom D n i)
    (genericSliceTraitStructure D n i) _ hNj _ _ hMj _ hMi hφ hgen _
    (by exact_mod_proofs hC')
  exact_mod_proofs h

/-- **Slicing over the generic slice trait, finite coefficients** (SGA 4½, [Th. finitude],
Lemme 3.4): the pullback exchange of `σ : (𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S' over S') ⟶ (𝔸ⁿ⁺¹_S over S)` is a split
monomorphism at a complex bounded below of étale origin: its cartesian factor is weakly étale base
change, and its change of generic fibres is split by averaging over the pro-`p` kernel (M2). -/
theorem isSplitMono_pullbackExchange_app_genericSliceTraitHom_of_finite (D : GenericSliceTrait k')
    (n : ℕ) (i : Fin (n + 1)) {p : ℕ} [Fact p.Prime] (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m)
    (hpT : IsUnit (p : T))
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
        (affineSpaceModel k' (n + 1)).total))}
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T))
      (affineSpaceModel k' (n + 1)).total
      ((finiteCoefficientDerivedEquivalence (affineSpaceModel k' (n + 1)).total T).functor.obj
        C)) :
    IsSplitMono (((genericSliceTraitHom D n i).pullbackExchange
      (Profinite.continuousMapRingObj T)).app C) := by
  have := (genericSliceTraitHom D n i).isIso_pullbackExchange_fromCartesian_of_weaklyEtale
    (Profinite.continuousMapRingObj T)
  have h₂ := isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom_of_finite D n i hp
    T hpT C hC
  have h := Hom.isSplitMono_pullbackExchange_app_of_cartesian (genericSliceTraitHom D n i)
    (Profinite.continuousMapRingObj T) C inferInstance (by exact_mod_proofs h₂)
  exact_mod_proofs h

/-- **Nearby cycles on the coordinate generic slices, finite coefficients** (SGA 4½,
[Th. finitude], Lemme 3.3 and 3.7): for a complex `C` on `𝔸ⁿ⁺¹_S` bounded below of étale origin,
with coefficients a finite ring in which the characteristic exponent `p` of `k'` is invertible,
and a coordinate `i`, the pullback exchange `α : Lhᵢ,ₛ^* Ψ C ⟶ Ψ_K (Lhᵢ^* C)` of the morphism of
models over the slice (`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite (n : ℕ) (i : Fin (n + 1))
    {p : ℕ} [Fact p.Prime] (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
        (affineSpaceModel k' (n + 1)).total))}
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T))
      (affineSpaceModel k' (n + 1)).total
      ((finiteCoefficientDerivedEquivalence (affineSpaceModel k' (n + 1)).total T).functor.obj
        C)) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.continuousMapRingObj T)).app C) := by
  obtain ⟨D⟩ := nonempty_genericSliceTrait k'
  have h₁ := isIso_pullbackExchange_app_genericSliceTraitChangeHom_of_finite T D n i hp hpT hC
  have h₂ := isSplitMono_pullbackExchange_app_genericSliceTraitHom_of_finite T D n i hp hpT hC
  have htot : (genericSliceTraitChangeHom D n i).total ≫ (genericSliceTraitHom D n i).total =
      (affineSpaceSliceHom k' n i).total := genericSliceTraitChangeTotal_comp D n i
  have hgen : (genericSliceTraitChangeHom D n i).generic ≫ (genericSliceTraitHom D n i).generic =
      (affineSpaceSliceHom k' n i).generic := genericSliceTraitChangeGeneric_comp D n i
  have key := Hom.isSplitMono_pullbackExchange_app_of_comp (Profinite.continuousMapRingObj T)
    (genericSliceTraitChangeHom D n i) (genericSliceTraitHom D n i) (affineSpaceSliceHom k' n i)
    (genericSliceTraitChangeTotal_comp D n i) (genericSliceTraitChangeSpecial_comp D n i)
    htot hgen C
  have := key (by exact_mod_proofs h₁) (by exact_mod_proofs h₂)
  exact_mod_proofs this

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

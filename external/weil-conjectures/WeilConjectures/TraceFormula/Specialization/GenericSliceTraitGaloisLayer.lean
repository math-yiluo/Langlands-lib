/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.SliceTraitGaloisLayer

/-!

# The slice over a generic slice trait in Galois-layer form

Let `D` be a generic slice trait of `𝔸¹_S`, `S = Spec k'⟦t⟧` with `k'` separably closed
(`AlgebraicGeometry.GenericSliceTrait`), and `σ = NearbyCyclesModel.genericSliceTraitHom D n i`
the morphism of models from `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} S'` over `S'` to `𝔸ⁿ⁺¹_S` over `S`. As `D` is a slice
trait over `S` (`AlgebraicGeometry.GenericSliceTrait.toSliceTrait`), the change of geometric
generic fibres `σ.toCartesian` is, up to universal homeomorphisms, the projection of the Galois
layer of the pro-`p` extension `L^sep / L`, `L = Ω·Frac R ⊆ Ω'`
(`NearbyCyclesModel.Hom.traitChangeModel`). Hence its pullback exchange is a split monomorphism
with finite coefficients in which `p` is invertible
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom_of_finite`):
this is (M2) with torsion coefficients (SGA 4½, [Th. finitude], Lemme 3.4).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] [IsSepClosed k'] (D : GenericSliceTrait k') (n : ℕ)
  (i : Fin (n + 1))

/-- **(M2) with torsion coefficients** (SGA 4½, [Th. finitude], Lemme 3.4): for a generic slice
trait `D` and a finite discrete ring `T₀` in which a prime `p` is invertible, every natural number
vanishing in `k'` being divisible by `p`, the pullback exchange of the cartesian part
`σ.toCartesian` of the slice `σ = genericSliceTraitHom D n i` is a split monomorphism at every
complex on `𝔸ⁿ⁺¹_S` which is bounded below of étale origin. -/
theorem isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom_of_finite
    {p : ℕ} [Fact p.Prime] (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m)
    (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
    [Finite T₀] (hpT : IsUnit (p : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T₀)
        (affineSpaceModel k' (n + 1)).total)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀))
      (affineSpaceModel k' (n + 1)).total
      ((finiteCoefficientDerivedEquivalence (affineSpaceModel k' (n + 1)).total T₀).functor.obj
        C)) :
    IsSplitMono (((genericSliceTraitHom D n i).toCartesian.pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app C) := by
  have hp' : ∀ m : ℕ, (m : ResidueField (PowerSeries k')) = 0 → p ∣ m := fun m hm ↦
    hp m ((PowerSeries.residueFieldEquiv k').injective (by rw [map_natCast, hm, map_zero]))
  refine Hom.isSplitMono_toCartesian_pullbackExchange_app_of_sliceTrait D.toSliceTrait
    (algebraMap_traitGenericField_injective k') (isAlgebraic_traitGenericField k')
    (genericSliceTraitHom D n i) (N := (affineSpaceModel k' (n + 1)).geometric)
    (q := genericSliceTraitStructure D n i) (g := pullback.snd _ _)
    (q₁ := 𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k') (g₁ := pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _) ?_ ?_ hp' T₀ hpT C hC
  · change genericSliceTraitProj D n i ≫ _ = _
    rw [genericSliceTraitProj, genericSliceTrait_fst_comp_over]
    exact congrArg (genericSliceTraitStructure D n i ≫ ·) D.spec_φ.symm
  · exact pullback.lift_snd _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

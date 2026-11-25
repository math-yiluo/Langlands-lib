/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariants
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.FieldTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginUpperStar

/-!

# Nearby cycles of an intermediate field are the invariants, torsion coefficients

Let `N` be a model of `X` with special fibre `X'`, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois
extension (possibly infinite) whose finite Galois subextensions have degrees invertible in a finite
discrete commutative ring `T₀` (for instance `Ω/L` pro-`p` and `T₀ = 𝒪_E/ϖⁿ` with `p ≠ ℓ`), and
`Λ = C(-, T₀)`. For `C ∈ D(Mod_{Λ_X})` whose restriction to the generic fibre is bounded below of
étale origin, the pullback exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the projection from the Galois layer
`N_Ω` (generic fibre `N.generic ×_L Ω`) is a split monomorphism, with a retraction whose idempotent
is fixed by the action of `Gal(Ω/L)` on both sides
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin`): `α` is
the inclusion of the `Gal(Ω/L)`-invariant direct summand of `Ψ_{N_Ω} C`.

For a model over a strictly henselian trait whose generic fibre lies over the generic point
`η = Spec L` and `Ω` the separable closure of `L`, the group `Gal(Ω/L)` is the inertia group `I`,
and for a closed subgroup `P ⊆ I` with fixed field `L_P = Ω^P`, `N_{L_P}` is the model with generic
fibre over `L_P`; applied to `Ω/L_P` this gives `Ψ_{N_{L_P}} = (Ψ_{N_Ω})^P` (SGA 4½, [Th. finitude],
Lemme 3.4; blueprint `proposition-external-kunneth-formula-nearby-cycles`, identification (2)), for
pro-`p` `P`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω] [IsGalois L Ω]

-- matching the derived functors of the Galois layer with those of the field tower
/-- **The nearby cycles of `N` are the `Gal(Ω/L)`-invariants of those of the Galois layer `N_Ω`**
(torsion coefficients in which the degrees of the finite Galois subextensions of `Ω/L` are
invertible). If the restriction `Lε^* C` of `C` to the generic fibre is bounded below of étale
origin, the pullback exchange `α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_Ω} (L(𝟙)^* C)` of the projection
`N_Ω ⟶ N` has a retraction `r` whose idempotent `r ≫ α` is fixed by the action of every
`σ ∈ Gal(Ω/L)` on both sides. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) :
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ≫
        r = 𝟙 _ ∧
      ∀ σ : Ω ≃ₐ[L] Ω,
        N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
            (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) ≫
            (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
              (Profinite.continuousMapRingObj T₀)).app C) =
          r ≫ ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C ∧
        (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange (Profinite.continuousMapRingObj T₀)).app C) ≫
            N.galoisLayerAction (Profinite.continuousMapRingObj T₀) h Ω σ
              (L((𝟙 X)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) =
          r ≫ ((N.galoisLayerHom h Ω).pullbackExchange
            (Profinite.continuousMapRingObj T₀)).app C := by
  obtain ⟨R, hR₁, hR₂⟩ := exists_invariant_retraction_derivedUnit_galois h T₀ hp _ hC
  exact N.exists_retraction_pullbackExchange_galoisLayerHom_of_invariant _ h Ω C R hR₁ hR₂

/-- **Split injectivity of the exchange of a Galois layer**, torsion coefficients: the pullback
exchange `Ψ_N C ⟶ Ψ_{N_Ω} C` is a split monomorphism when `Lε^* C` is bounded below of étale
origin. -/
theorem isSplitMono_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T₀).functor.obj
        (L((N.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) :
    IsSplitMono (((N.galoisLayerHom h Ω).pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app C) := by
  obtain ⟨r, hr, -⟩ :=
    exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin T₀ N h Ω hp C hC
  exact IsSplitMono.mk' ⟨r, hr⟩

/-- `NearbyCyclesModel.isSplitMono_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin` for a
complex `C` on `X` which is bounded below of étale origin (its restriction to the generic fibre is
then of étale origin as well). -/
theorem isSplitMono_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin'
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) X
      ((finiteCoefficientDerivedEquivalence X T₀).functor.obj C)) :
    IsSplitMono (((N.galoisLayerHom h Ω).pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app C) :=
  isSplitMono_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin T₀ N h Ω hp C
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀ N.ε hC)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

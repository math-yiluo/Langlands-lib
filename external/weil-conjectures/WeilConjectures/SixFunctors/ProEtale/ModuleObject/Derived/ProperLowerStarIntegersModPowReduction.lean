/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionPullCompatible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionRestrictConstructibleProof
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstructibleDictionary
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek

/-!
# The proper pushforward followed by reduction modulo `ℓⁿ` is a left adjoint

For a proper morphism `p : Z ⟶ Y` of separated schemes of finite type over a field `k`, the
composite `Rp_* ⋙ red_Y : Dᵇc(Z)⟦𝒪_E⟧ ⥤ Dᵇc(Y)⟦𝒪_E ⧸ ℓⁿ⟧` of the pushforward with
`𝒪_E`-coefficients and the reduction modulo `ℓⁿ` has a right adjoint
(`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_comp_integersModPowReduction`).
Indeed reduction modulo `ℓⁿ` commutes with the pushforward, `Rp_* ⋙ red_Y ≅ red_Z ⋙ Rp_*^{(n)}`,
and both `red_Z` (right adjoint the restriction of scalars) and the finite-coefficient pushforward
`Rp_*^{(n)}` (right adjoint the finite-coefficient `Rp^!`) are left adjoints.

As a consequence, for `M : Dᵇc(Y)⟦𝒪_E ⧸ ℓⁿ⟧` the functor `Hom(Rp_* -, Res M)` on `Dᵇc(Z)⟦𝒪_E⟧`
is representable
(`exists_bijective_boundedConstructibleLowerStar_comp_integersModPowRestriction`).

This file does not depend on the exceptional inverse image with `𝒪_E`-coefficients.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : Z ⟶ Y) [IsProper p.left]

/-- **The proper pushforward followed by reduction modulo `ℓⁿ` is a left adjoint**: on bounded
constructible complexes, `Rp_* ⋙ red_Y : Dᵇc(Z)⟦𝒪_E⟧ ⥤ Dᵇc(Y)⟦𝒪_E ⧸ ℓⁿ⟧` has a right adjoint.
It is isomorphic to `red_Z ⋙ Rp_*^{(n)}`, a composite of left adjoints. -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_comp_integersModPowReduction :
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p ⋙
      boundedConstructibleIntegersModPowReduction Y.left ℓ E n).IsLeftAdjoint := by
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E n p
    (integersModPowPullUnitCompatible ℓ E n p.left) (integersModPowPullδCompatible ℓ E n p.left)
  obtain ⟨H', adjH', -⟩ := hasEtaleReadingUpperShriekComparison_of_etaleOrigin p
    (etaleOriginReading ℓ E n Z) (etaleOriginReading ℓ E n Y) (boundedConstructibleOfEtale ℓ E n Z)
  have := ((boundedConstructibleIntegersModPowAdjunction
    (restrictScalarsIntegersModPowBoundedConstructible ℓ E n Z.left)).comp adjH').isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso
    (asIso (boundedConstructibleLowerStarIntegersModPowReduction ℓ E n p)).symm

/-- **`Hom(Rp_* -, Res M)` is representable** on `Dᵇc(Z)⟦𝒪_E⟧`, for a proper `p` and
`M : Dᵇc(Y)⟦𝒪_E ⧸ ℓⁿ⟧`: there are `T : Dᵇc(Z)⟦𝒪_E⟧` and `ε : Rp_* T ⟶ Res M` such that every
morphism `Rp_* A ⟶ Res M` factors uniquely as `Rp_* f ≫ ε`. Here `T` is the value at `M` of the
right adjoint of `Rp_* ⋙ red_Y`, using `red_Y ⊣ Res`. -/
theorem exists_bijective_boundedConstructibleLowerStar_comp_integersModPowRestriction
    (hY : RestrictScalarsIntegersModPowBoundedConstructible ℓ E n Y.left)
    (M : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    ∃ (T : Dᵇc(Z.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)
      (ε : (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p).obj T ⟶
        (boundedConstructibleIntegersModPowRestriction hY).obj M),
      ∀ A, Function.Bijective
        (fun f : A ⟶ T ↦ (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p).map f ≫ ε) := by
  have := isLeftAdjoint_boundedConstructibleLowerStar_comp_integersModPowReduction ℓ E n p
  let adj := Adjunction.ofIsLeftAdjoint
    (PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E p ⋙
      boundedConstructibleIntegersModPowReduction Y.left ℓ E n)
  let adjY := boundedConstructibleIntegersModPowAdjunction hY
  refine ⟨_, adjY.homEquiv _ _ (adj.counit.app M), fun A ↦ ?_⟩
  convert ((adj.homEquiv A M).symm.trans (adjY.homEquiv _ M)).bijective using 1
  funext f
  rw [Equiv.trans_apply, adj.homEquiv_counit, Functor.comp_map]
  exact (adjY.homEquiv_naturality_left _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing

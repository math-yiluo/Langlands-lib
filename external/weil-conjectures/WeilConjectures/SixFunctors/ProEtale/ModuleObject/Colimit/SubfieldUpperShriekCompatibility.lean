/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Center.Linear
public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldBiproductUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive

/-!
# Extension of scalars along finite subextensions commutes with `g^!` for proper `g`

Let `E ≤ F` be finite subextensions of `ℚ̄_ℓ / ℚ_ℓ` and `g : Z ⟶ Y` a proper morphism of separated
`k`-schemes of finite type. The (Push) comparison
`ProEtale.CondensedRing.boundedConstructibleLowerStarExtendScalarsSubfield`
`Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^F` is an isomorphism; we show that its mate
`Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_F` under the adjunctions `Rg_* ⊣ Rg^!` is an isomorphism as well
(`ProEtale.CondensedRing.isIso_mateEquiv_boundedConstructibleLowerStarExtendScalarsSubfield`).
This is the finite-stage `f^!` clause of blueprint `proposition-six-operations-change-coefficients`
for proper morphisms.

The proof uses that the monads `Res ∘ T` are biproduct powers `K ↦ K ^ d`, via an `E`-basis of
`F` (`ProEtale.CondensedRing.exists_isIso_biproductDesc_unit_smul`), compatibly with `Rg_*`,
which is `F`-linear; see
`CategoryTheory.Adjunction.isIso_mateEquiv_inv_of_isIso_biproductDesc_unit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y)

/-- **`g^!` commutes with extension of scalars along `E ≤ F`**, for a proper morphism `g`: the
mate `Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_F` of the inverse of (Push) under the adjunctions
`Rg_* ⊣ Rg^!` is an isomorphism. -/
theorem isIso_mateEquiv_boundedConstructibleLowerStarExtendScalarsSubfield [IsProper g.left]
    [(ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint]
    [(ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g).IsLeftAdjoint] :
    IsIso (mateEquiv
      (Adjunction.ofIsLeftAdjoint
        (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g))
      (Adjunction.ofIsLeftAdjoint
        (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g))
      (TwoSquare.mk (boundedConstructibleExtendScalarsSubfield Z.left ℓ h)
        (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g)
        (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g)
        (boundedConstructibleExtendScalarsSubfield Y.left ℓ h)
        (inv (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g)))) := by
  have := noetherianSpace_left_of_over Z
  have := noetherianSpace_left_of_over Y
  have hex := exists_isIso_biproductDesc_unit_smul.{u} ℓ h
  obtain ⟨d, hex⟩ := hex
  obtain ⟨b, hb⟩ := hex
  have := (Adjunction.ofIsLeftAdjoint
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g)).right_adjoint_additive
  have hμ (i : Fin d) (K : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj F⟧) :=
    boundedConstructibleLowerStar_map_smul_id ℓ F g (b i) K
  have hZ (K : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj E⟧) := hb Z.left K
  have hY (K : Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧) := hb Y.left K
  have H := Adjunction.isIso_mateEquiv_inv_of_isIso_biproductDesc_unit
    (boundedConstructibleExtendRestrictScalarsSubfieldAdjunction Z.left ℓ h)
    (boundedConstructibleExtendRestrictScalarsSubfieldAdjunction Y.left ℓ h)
    (Adjunction.ofIsLeftAdjoint
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g))
    (Adjunction.ofIsLeftAdjoint
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ F g))
    (boundedConstructibleLowerStarRestrictScalarsSubfieldIso ℓ h g)
    (TwoSquare.mk _ _ _ _ (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g))
    (Equiv.apply_symm_apply _ _)
    (fun i ↦ (Linear.toCatCenter F _ (b i)).asHom)
    (fun i ↦ (Linear.toCatCenter F _ (b i)).asHom)
    hμ hZ hY
  with_reducible exact H

end AlgebraicGeometry.ProEtale.CondensedRing

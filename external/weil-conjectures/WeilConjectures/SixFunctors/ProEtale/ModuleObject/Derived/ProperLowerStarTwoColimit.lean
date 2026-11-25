/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimitAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldPushCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldUpperShriekCompatibility

/-!
# The proper direct image on `Dᵇc(-)⟦ℚ̄_ℓ⟧` is a left adjoint if it is so over each `E`

Let `ℓ` be a prime, `k` a field in which `ℓ` is invertible and `g : Z ⟶ Y` a proper morphism of
separated `k`-schemes of finite type. If for every finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` the
derived pushforward `Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` is a left adjoint, then so is
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`
(`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_forall`).
This is the proof of blueprint `theorem-exceptional-inverse-image--17`:

* `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is the filtered 2-colimit of the categories `Dᵇc(-)⟦E̲⟧`
  (`lemma-descent-finite-coefficient-field`,
  `ProEtale.CondensedRing.boundedConstructibleCocone_isFilteredTwoColimit`);
* `Rg_*` commutes with the extensions of scalars, compatibly with the structure isomorphisms of
  the cocones (`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso_hom_app_eq`);
* the right adjoints `Rg^!_E` commute with the extensions of scalars `F̲ ⊗ᴸ_{E̲} -` for `E ≤ F`
  (`ProEtale.CondensedRing.isIso_mateEquiv_boundedConstructibleLowerStarExtendScalarsSubfield`);

so `Rg_*` over `ℚ̄_ℓ` is a left adjoint
(`CategoryTheory.CategoryCocone.LevelwiseLeftAdjoint.isLeftAdjoint_of_isFilteredTwoColimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  [∀ E : FiniteIntermediateField ℓ,
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).IsLeftAdjoint]

/-- For a proper `g`, the derived pushforward `Rg_*` over `ℚ̄_ℓ` is induced, on the 2-colimit
`Dᵇc(-)⟦ℚ̲̄_ℓ⟧` of the categories `Dᵇc(-)⟦E̲⟧`, by the left adjoints `Rg_*` over the finite
subextensions `E`, whose right adjoints commute with the extensions of scalars. -/
noncomputable def boundedConstructibleLowerStarLevelwiseLeftAdjoint :
    CategoryCocone.LevelwiseLeftAdjoint (boundedConstructibleCocone Z.left ℓ)
      (boundedConstructibleCocone Y.left ℓ) (boundedConstructibleLowerStar ℓ g) :=
  .ofIso (fun E ↦ ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g)
    (fun E ↦ (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E g).rightAdjoint)
    (fun _ ↦ Adjunction.ofIsLeftAdjoint _)
    (fun E ↦ boundedConstructibleLowerStarToPadicAlgClIso ℓ E g)
    (fun h ↦ asIso (boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g))
    (fun h x ↦ boundedConstructibleLowerStarToPadicAlgClIso_hom_app_eq ℓ h g x)
    fun h ↦ by
      dsimp only [boundedConstructibleCocone, asIso_inv]
      with_reducible exact
        isIso_mateEquiv_boundedConstructibleLowerStarExtendScalarsSubfield ℓ h g

/-- Blueprint `theorem-exceptional-inverse-image--17`, from the case of the finite
subextensions: if for every finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` the derived pushforward
`Rg_* : Dᵇc(Z)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` along a proper `g` is a left adjoint, then so is
`Rg_* : Dᵇc(Z)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`. -/
theorem isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj_of_forall :
    (boundedConstructibleLowerStar ℓ g).IsLeftAdjoint :=
  have := noetherianSpace_left_of_over Z
  have := noetherianSpace_left_of_over Y
  (boundedConstructibleLowerStarLevelwiseLeftAdjoint ℓ g).isLeftAdjoint_of_isFilteredTwoColimit
    (boundedConstructibleCocone_isFilteredTwoColimit Z.left ℓ)
    (boundedConstructibleCocone_isFilteredTwoColimit Y.left ℓ)

end AlgebraicGeometry.ProEtale.CondensedRing

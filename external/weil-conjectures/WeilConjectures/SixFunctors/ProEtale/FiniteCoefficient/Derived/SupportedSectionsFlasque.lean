/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion

/-!
# Supported sections and flasque sheaves on the pro-étale site

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : U ⟶ X`. On
pro-étale sheaves of modules, the sheaf of sections supported on `Z` is
`𝒢_Z M = ker (M ⟶ j_* j^* M)` (`AlgebraicGeometry.ProEtale.sectionsWithSupport`), and
`i^! M = i^* 𝒢_Z M` (`AlgebraicGeometry.ProEtale.closedUpperShriek`). This file records that
`i_* i^! M ≅ 𝒢_Z M` and defines the sheaves which are *flasque for the pair*: those for which
`I ⟶ j_* j^* I` is an epimorphism. These are the pro-étale forms of blueprint
`definition-local-cohomology`, whose étale forms are in
`WeilConjectures.SixFunctors.OpenClosed.SupportedSections`.

## Main definitions

- `AlgebraicGeometry.ProEtale.closedUpperShriekCompLowerStarIso`: `i_* i^! ≅ 𝒢_Z`.
- `AlgebraicGeometry.ProEtale.IsFlasqueFor`: flasque sheaves for the pair.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Flasque

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {U X : Scheme.{u}} (j : U ⟶ X)

/-- Blueprint `definition-local-cohomology`: Supported sections and flasque objects

A pro-étale sheaf `I` on `X` is *flasque for the pair* `(Z, U)` if the restriction
`I ⟶ j_* j^* I` to the open part `j : U ⟶ X` is an epimorphism; then
`0 ⟶ 𝒢_Z I ⟶ I ⟶ j_* j^* I ⟶ 0` is exact, `𝒢_Z I` being the kernel
(`AlgebraicGeometry.ProEtale.sectionsWithSupport`). -/
def IsFlasqueFor (I : Sheaf (ProEt.topology X) A) : Prop :=
  Epi ((upperStarLowerStarAdjunction A j).unit.app I)

end Flasque

variable {R : Type (u + 1)} [Ring R] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- Blueprint `definition-local-cohomology`: Supported sections and flasque objects

For a closed immersion `i : Z ⟶ X` with quasi-compact open complement `j`, the pushforward of
`i^! M = i^* 𝒢_Z M` is the sheaf of supported sections: `i_* i^! M ≅ 𝒢_Z M`, through the unit of
`i^* ⊣ i_*`, which is invertible on sheaves vanishing on `U`
(`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`). -/
noncomputable def closedUpperShriekCompLowerStarIso
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    closedUpperShriek (ModuleCat.{u + 1} R) i j ⋙ (i)_*[ModuleCat.{u + 1} R] ≅
      sectionsWithSupport (ModuleCat.{u + 1} R) j :=
  NatIso.ofComponents (fun M ↦
    haveI := isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl i j hij _
      (isZero_upperStar_sectionsWithSupport _ j M)
    (asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app
      ((sectionsWithSupport (ModuleCat.{u + 1} R) j).obj M))).symm)
    (fun f ↦ by
      dsimp [closedUpperShriek]
      rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
      exact ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.naturality _).symm)

end ProEtale

end AlgebraicGeometry

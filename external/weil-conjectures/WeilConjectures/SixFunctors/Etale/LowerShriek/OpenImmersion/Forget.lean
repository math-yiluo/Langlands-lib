/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology

/-!
# Extension by zero commutes with forgetting the module structure

For an open immersion `j : U ⟶ X`, the extension by zero `j_!` of étale sheaves of `Λ`-modules
and of abelian groups are compatible with the forgetful functor from `Λ`-modules to abelian
groups (blueprint `lemma-cohomology-near-two-transverse-divisors--1`, forgetting `Λ`).

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekSheafForget₂Iso`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The extension by zero along an open immersion commutes with forgetting the
`Λ`-module structure: both composites are left adjoint to the functor sending an abelian
sheaf `G` on `X` to the coinduced sheaf of `Λ`-modules `Hom_ℤ(Λ, j^* G)` on `U`, as
restriction along `j` commutes with postcomposition. -/
noncomputable def openImmersionLowerShriekSheafForget₂Iso :
    (j)_!open[ModuleCat.{u + 1} Λ] ⋙ sheafForget₂ Λ X ≅
      sheafForget₂ Λ U ⋙ (j)_!open[AddCommGrpCat.{u + 1}] :=
  ((openImmersionLowerShriekAdjunction _ j).comp
    (Sheaf.forget₂CoinduceAdj X.smallEtaleTopology Λ)).leftAdjointUniq
    (((Sheaf.forget₂CoinduceAdj U.smallEtaleTopology Λ).comp
      (openImmersionLowerShriekAdjunction _ j)).ofNatIsoRight (Iso.refl _))

end AlgebraicGeometry.Etale

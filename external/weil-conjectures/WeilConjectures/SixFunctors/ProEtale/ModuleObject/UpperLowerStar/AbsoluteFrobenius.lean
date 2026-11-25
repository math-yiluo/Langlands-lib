/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.AbsoluteFrobeniusMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FrobeniusPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UpperStarIsoId

/-!
# The absolute Frobenius acts trivially on module objects

Let `X` be a scheme in which the prime `p` vanishes, `F_X` its `p ^ n`-power absolute Frobenius
and `Λ` a commutative condensed ring. The trivialization `F_X^* ≅ 𝟭` of the pullback of abelian
pro-étale sheaves (`AlgebraicGeometry.ProEtale.upperStarIterateFrobeniusIso`, blueprint
`lemma-scheme-frobenius-geometric-frobenius--1`) is monoidal
(`AlgebraicGeometry.ProEtale.isMonoidal_upperStarIterateFrobeniusIso_hom`) and is the canonical
comparison on the sheaves pulled back from the condensed point
(`AlgebraicGeometry.ProEtale.upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint`), in
particular on the coefficient ring `Λ_X`. Hence it induces a trivialization of the pullback
`F_X^*` of `Λ_X`-modules (`ProEtale.CondensedRing.upperStarIsoIdOfIsoId`).

## Main definitions

- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarIterateFrobeniusIso`: the trivialization
  `F_X^* ≅ 𝟭` of the pullback of `Λ_X`-modules along the absolute Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

/-- The trivialization `F_X^* ≅ 𝟭` of the pullback of `Λ_X`-modules along the `p ^ n`-power
absolute Frobenius `F_X`: the trivialization of the pullback of abelian sheaves
(`ProEtale.upperStarIterateFrobeniusIso`), which is monoidal and fixes the coefficient ring
`Λ_X`, on the underlying sheaves. -/
noncomputable def upperStarIterateFrobeniusIso :
    (X.iterateFrobenius hp hX n)^*⟦Λ⟧ ≅ 𝟭 _ :=
  upperStarIsoIdOfIsoId Λ _ (ProEtale.upperStarIterateFrobeniusIso Ab.{u + 1} hp hX n)
    (ProEtale.upperStarIterateFrobeniusIso_hom_app_upperStarFromPoint hp hX n Λ)

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The Künneth formula with one proper factor

Let `k` be a separably closed field and `Λ` a finite ring.
For a proper `k`-scheme `X` and a `k`-scheme `Y` of finite type, the Künneth formula
`RΓ(X, E) ⊗ᴸ RΓ(Y, K) ≅ RΓ(X ×_k Y, Lp₁^* E ⊗ᴸ Lp₂^* K)` follows from the projection formula
and proper base change for the proper projection `p₂ : X ×_k Y ⟶ Y`, and from the tensor
product with a constant complex on `Y` (Stacks, Lemma 0F14).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kunneth_of_isProper`
(`proposition-ordinary-external-kunneth--1`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- Blueprint `proposition-ordinary-external-kunneth--1`: the Künneth formula with one proper
factor.

Let `k` be separably closed, `Λ` a finite ring, `X` a
proper `k`-scheme and `Y` a `k`-scheme of finite type. For a cartesian square

```
  W --p₂--> Y
  |         |
  p₁        a_Y
  v         v
  X --a_X-> Spec k
```

and all `E ∈ D(X_ét, Λ)`, `K ∈ D(Y_ét, Λ)`, unbounded,

`RΓ(X, E) ⊗ᴸ RΓ(Y, K) ≅ RΓ(W, Lp₁^* E ⊗ᴸ Lp₂^* K)`.

Following the blueprint: by the Leray isomorphism for `p₂`, the projection formula for the
proper morphism `p₂` (`proposition-proper-direct-image-constructible-complexes--9`) and proper base
change `La_Y^* Ra_{X*} E ≅ Rp₂_* Lp₁^* E` (`theorem-results-from-etale-theory--1`), the right-hand
side is `RΓ(Y, La_Y^* Ra_{X*} E ⊗ᴸ K)`; the tensor product with a constant complex
(`proposition-open-direct-image-preserves-finite`) and the symmetry of `⊗ᴸ` identify it with the
left-hand side. -/
theorem nonempty_iso_kunneth_of_isProper {X Y W : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [IsProper aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (p₁ : W ⟶ X) (p₂ : W ⟶ Y) (sq : IsPullback p₁ p₂ aX aY)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
            ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) := by
  have : IsProper p₂ := MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
  -- projection formula for `p₂` and proper base change for the square
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ isAddTorsion_of_finite p₂
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
  let pf : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj ((R((p₂)_*[ModuleCat.{u + 1} Λ])).obj
          ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E))).obj K) ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj
        ((R((p₂)_*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
          ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
            ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) :=
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).mapIso
      (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) p₂).app
        ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).app K))
  let bc : (L((aY)^*[ModuleCat.{u + 1} Λ])).obj ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj E) ≅
      (R((p₂)_*[ModuleCat.{u + 1} Λ])).obj ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E) :=
    asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app E)
  obtain ⟨σ⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) Y
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedGlobalSections_derivedTensor_leftDerivedUpperStar Λ aY
    K ((R((aX)_*[ModuleCat.{u + 1} Λ])).obj E)
  obtain ⟨β⟩ := DerivedCategory.nonempty_braidedCategory (ModuleCat.{u + 1} Λ)
  exact ⟨β_ _ _ ≪≫ whiskerLeftIso _
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aX).app E).symm ≪≫ e₁ ≪≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).mapIso ((σ.app K).app _ ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).mapIso bc).app K) ≪≫ pf ≪≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ p₂).app _⟩

end Etale

end AlgebraicGeometry

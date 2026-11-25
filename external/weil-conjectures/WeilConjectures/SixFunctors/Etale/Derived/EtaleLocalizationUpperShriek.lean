/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-!
# Étale localization of the exceptional inverse image

For an étale morphism `u : U ⟶ X` and `f : X ⟶ Y` admitting compactifications, the exceptional
inverse image localizes along `u`: `Lu^* Rf^! ≅ R(u ≫ f)^!` (blueprint
`lemma-affine-space-etale-localization--4`, a node of the blueprint subsection `sk-prop-sf-cbc`).

The extension by zero `u_!` is left adjoint to `u^*`, and its derived functor `De_!` agrees with
the derived lower shriek `Ru_!` (`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`).
So `Ru_! ⊣ Lu^*`, and composing with `Rf_! ⊣ Rf^!` and `R(u ≫ f)_! ≅ Ru_! ⋙ Rf_!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) gives the isomorphism by
uniqueness of right adjoints.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lemma-affine-space-etale-localization--4`: Étale localization of the ambient adjoint.

For a separated étale morphism `u : U ⟶ X` of finite type, and `f : X ⟶ Y` such that `f` and
`h = u ≫ f` admit compactifications, the exceptional inverse image localizes along `u`:

`Lu^* Rf^! K ≅ R(u ≫ f)^! K`,

naturally in `K`. The blueprint also records that the extension by zero `u_!` along `u` is
exact and left adjoint to `u^*`. The isomorphism is the uniqueness of right adjoints for
`R(u ≫ f)_! ≅ Ru_! ⋙ Rf_! ⊣ Rf^! ⋙ Lu^*`, where `Ru_! ⊣ Lu^*` is the adjunction
`De_! ⊣ Le^*` of the extension by zero `u_!`, transported along the comparison isomorphism
`De_! ≅ Ru_!` (`AlgebraicGeometry.Etale.isIso_compactificationEtaleComparison`); only its
existence is recorded.

This is a node of the blueprint subsection `lemma-affine-space-etale-localization--4`. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale
    {U X Y : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
    (f : X ⟶ Y) (h : U ⟶ Y) (w : u ≫ f = h) [HasCompactification f]
    [HasCompactification h] :
    Nonempty (R(f)^![Λ] ⋙ L((u)^*[ModuleCat.{u + 1} Λ]) ≅
      R(h)^![Λ]) := by
  subst h
  let c := HasCompactification.compactification (u ≫ f)
  let a : U ⟶ pullback c.g f := pullback.lift c.i u c.comm.symm
  have : IsImmersion (a ≫ pullback.fst c.g f) := by
    change IsImmersion ((pullback.lift c.i u c.comm.symm) ≫ pullback.fst c.g f)
    rw [pullback.lift_fst]
    infer_instance
  have : IsImmersion a := IsImmersion.of_comp a (pullback.fst c.g f)
  have : HasCompactification u :=
    HasCompactification.of_isImmersion a (pullback.snd c.g f) (pullback.lift_snd _ _ _)
  let cu := HasCompactification.compactification u
  have := isIso_compactificationEtaleComparison Λ u cu
  let e : R(u)_![ModuleCat.{u + 1} Λ] ≅
      (etaleLowerShriek (ModuleCat.{u + 1} Λ) u inferInstance).mapDerivedCategory :=
    (asIso (compactificationEtaleComparison Λ u cu)).symm
  let adj :=
    ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) u
      inferInstance).mapDerivedCategoryAdjunction).ofNatIsoLeft e.symm
  obtain ⟨ec⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ u f
  exact ⟨Functor.isoWhiskerLeft _
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) u) ≪≫
      (adj.comp (rightDerivedUpperShriekAdjunction Λ f)).rightAdjointUniq
        ((rightDerivedUpperShriekAdjunction Λ (u ≫ f)).ofNatIsoLeft ec)⟩

end Etale

end AlgebraicGeometry

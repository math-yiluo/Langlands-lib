/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveUnit
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Étale sheaves of modules on the spectrum of a separably closed field

This is the étale counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.AlgClosedField`. Let `X` be a scheme
isomorphic to `Spec K` for a separably closed field `K` (for instance an
algebraically closed one), and let `Λ` be a commutative ring. Taking sections over `X` is exact
on étale sheaves of `Λ`-modules
(`AlgebraicGeometry.Scheme.preservesEpimorphisms_sheafSections_of_iso`), so the constant sheaf
`Λ_X`, the monoidal unit, is projective, and there are no nonzero morphisms `Λ_X ⟶ Λ_X[1]` in
the derived category, that is, `H¹(X_ét, Λ) = 0`.

## Main results

- `AlgebraicGeometry.Etale.projective_unit_of_iso`: the unit `Λ_X` is projective.
- `AlgebraicGeometry.Etale.DerivedCategory.unit_hom_shift_one_eq_zero_of_iso`: every morphism
  `Λ_X ⟶ Λ_X[1]` in `D(X_ét, Λ)` is zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

variable {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The monoidal unit `Λ_X` of étale sheaves of `Λ`-modules on a scheme `X` isomorphic to the
spectrum of a separably closed field is projective: it is the constant sheaf `Λ`
(`AlgebraicGeometry.Scheme.projective_constantSheaf_moduleCat_of_iso`). -/
lemma projective_unit_of_iso (e : X ≅ Spec (.of K)) :
    Projective (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  have := Scheme.projective_constantSheaf_moduleCat_of_iso e Λ
  Projective.of_iso (Functor.Monoidal.εIso (presheafToSheaf X.smallEtaleTopology _)).symm this

/-- On a scheme `X` isomorphic to the spectrum of a separably closed field, every morphism
`Λ_X ⟶ Λ_X[1]` in the derived category of étale sheaves of `Λ`-modules is zero, the unit `Λ_X`
being projective (`AlgebraicGeometry.Etale.projective_unit_of_iso`): this is the vanishing of
`H¹(X_ét, Λ)`. -/
lemma DerivedCategory.unit_hom_shift_one_eq_zero_of_iso (e : X ≅ Spec (.of K))
    (φ : 𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ⟶
      (𝟙_ _)⟦(1 : ℤ)⟧) : φ = 0 :=
  have := projective_unit_of_iso Λ e
  _root_.DerivedCategory.unit_hom_shift_eq_zero_of_projective 1 one_pos φ

end AlgebraicGeometry.Etale

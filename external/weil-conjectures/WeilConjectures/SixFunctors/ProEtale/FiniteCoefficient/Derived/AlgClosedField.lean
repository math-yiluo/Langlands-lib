/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveUnit
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-!
# Pro-étale sheaves of modules on the spectrum of an algebraically closed field

Let `X` be a scheme isomorphic to `Spec K` for an algebraically closed field `K`, and let `Λ`
be a commutative ring. Taking sections over `X` is exact on pro-étale sheaves of `Λ`-modules
(`AlgebraicGeometry.ProEtale.preservesEpimorphisms_sheafSections_of_iso`), so the constant
sheaf `Λ_X`, the monoidal unit, is a projective object: it corepresents sections over `X`. As a
consequence there are no nonzero morphisms `Λ_X ⟶ Λ_X[1]` in the derived category, that is,
`H¹(X_proét, Λ) = 0`.

## Main results

- `AlgebraicGeometry.ProEtale.projective_unit_of_iso`: the unit `Λ_X` is projective.
- `AlgebraicGeometry.ProEtale.DerivedCategory.unit_hom_shift_one_eq_zero_of_iso`: every
  morphism `Λ_X ⟶ Λ_X[1]` in `D(X_proét, Λ)` is zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The monoidal unit `Λ_X` of pro-étale sheaves of `Λ`-modules on a scheme `X` isomorphic to
the spectrum of an algebraically closed field is projective: it is the constant sheaf on the
projective module `Λ`, and the constant sheaf functor is left adjoint to taking sections over
the terminal object `X`, which preserves epimorphisms. -/
lemma projective_unit_of_iso (e : X ≅ Spec (.of K)) :
    Projective (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) := by
  have := preservesEpimorphisms_sheafSections_of_iso (A := ModuleCat.{u + 1} Λ) e
  have hP : Projective ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
      (𝟙_ (ModuleCat.{u + 1} Λ))) :=
    (constantSheafAdj _ _ (Scheme.ProEt.isTerminalMkId X)).map_projective _
      (ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of Λ Λ))
  exact Projective.of_iso
    (Functor.Monoidal.εIso (presheafToSheaf (Scheme.ProEt.topology X) _)).symm hP

/-- On a scheme `X` isomorphic to the spectrum of an algebraically closed field, every morphism
`Λ_X ⟶ Λ_X[1]` in the derived category of pro-étale sheaves of `Λ`-modules is zero, the unit
`Λ_X` being projective (`AlgebraicGeometry.ProEtale.projective_unit_of_iso`): this is the
vanishing of `H¹(X_proét, Λ)`. -/
lemma DerivedCategory.unit_hom_shift_one_eq_zero_of_iso (e : X ≅ Spec (.of K))
    (φ : 𝟙_ (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) ⟶
      (𝟙_ _)⟦(1 : ℤ)⟧) : φ = 0 :=
  have := projective_unit_of_iso Λ e
  _root_.DerivedCategory.unit_hom_shift_eq_zero_of_projective 1 one_pos φ

end AlgebraicGeometry.ProEtale

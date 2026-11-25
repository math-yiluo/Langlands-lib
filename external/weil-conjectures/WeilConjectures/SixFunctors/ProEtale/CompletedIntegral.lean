/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# The completed integral coefficient sheaf on the pro-étale site

Let `Λ` be a commutative ring with an ideal `I` (the intended case is `Λ = 𝒪_E`, `I = 𝔪_E`, so
that `Λ ⧸ Iⁿ = A_{E,n}`). This file defines the completed coefficient sheaf on the small
pro-étale site of a scheme `Y`,

`𝒪̂_{E,Y} = lim_n (A_{E,n})_Y`,

as a limit in the category of sheaves of rings, the category `Sh(Y_proét, 𝒪_E)` of modules over
it, the derived category `D(Y_proét, 𝒪_E)`, and, for every `n`, the restriction of scalars
`Res_n` along `𝒪̂_{E,Y} ⟶ (A_{E,n})_Y`.

On the pro-étale site the constant sheaf of rings with value a discrete ring `A` is the sheaf of
continuous (that is, locally constant) functions `U ↦ C(U, A)` (Bhatt–Scholze, Lemma 4.2.12);
on the small étale site this is `AlgebraicGeometry.Scheme.Etale.constantSheafIsoContinuousMapSheaf`.
We take this as the definition of `(A_{E,n})_Y` as a sheaf of rings
(`AlgebraicGeometry.ProEtale.reductionRingSheaf`), using the sheaf of rings
`AlgebraicGeometry.ProEtale.continuousMapRingSheaf` of continuous maps into a topological ring.

## Main definitions

- `AlgebraicGeometry.ProEtale.reductionRingSheaf`: the sheaf of rings `(Λ ⧸ Iⁿ)_Y`.
- `AlgebraicGeometry.ProEtale.reductionRingSheafMap`: the reduction `(Λ ⧸ Iⁿ⁺¹)_Y ⟶ (Λ ⧸ Iⁿ)_Y`.
- `AlgebraicGeometry.ProEtale.completedIntegralSheaf`: `𝒪̂_{E,Y} = lim_n (Λ ⧸ Iⁿ)_Y`.
- `AlgebraicGeometry.ProEtale.CompletedIntegralModule`: the abelian category of
  `𝒪̂_{E,Y}`-modules.
- `AlgebraicGeometry.ProEtale.CompletedIntegralDerivedCategory`: `D(Y_proét, 𝒪_E)`.
- `AlgebraicGeometry.ProEtale.restrictScalarsReduction`: `Res_n`.

## Implementation notes

The derived category of `𝒪̂_{E,Y}`-modules is Mathlib's standard localization at the
quasi-isomorphisms (`HasDerivedCategory.standard`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Y : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

/-- The discrete topology on `Λ ⧸ Iⁿ`. -/
abbrev reductionTopology (n : ℕ) : TopologicalSpace (Λ ⧸ I ^ n) := ⊥

lemma discreteTopology_reductionTopology (n : ℕ) :
    @DiscreteTopology (Λ ⧸ I ^ n) (reductionTopology I n) :=
  @DiscreteTopology.mk _ (reductionTopology I n) rfl

/-- The constant sheaf of rings `(Λ ⧸ Iⁿ)_Y` on the small pro-étale site of `Y` (for
`Λ = 𝒪_E`, `I = 𝔪_E`, the finite-torsion coefficients `(A_{E,n})_Y` of blueprint
`definition-constructible-sheaves`): the sheaf of locally constant functions
`U ↦ C(U, Λ ⧸ Iⁿ)` for the discrete topology. -/
noncomputable def reductionRingSheaf (n : ℕ) : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1} :=
  @continuousMapRingSheaf Y (Λ ⧸ I ^ n) (reductionTopology I n) _
    (@DiscreteTopology.topologicalRing _ (reductionTopology I n) _
      (discreteTopology_reductionTopology I n))

/-- The reduction map `(Λ ⧸ Iⁿ⁺¹)_Y ⟶ (Λ ⧸ Iⁿ)_Y` of sheaves of rings, induced by
`Λ ⧸ Iⁿ⁺¹ ↠ Λ ⧸ Iⁿ`. -/
noncomputable def reductionRingSheafMap (n : ℕ) :
    reductionRingSheaf Y I (n + 1) ⟶ reductionRingSheaf Y I n :=
  @continuousMapRingSheafMap Y (Λ ⧸ I ^ (n + 1)) (reductionTopology I (n + 1)) _
    (@DiscreteTopology.topologicalRing _ (reductionTopology I (n + 1)) _
      (discreteTopology_reductionTopology I (n + 1)))
    (Λ ⧸ I ^ n) (reductionTopology I n) _
    (@DiscreteTopology.topologicalRing _ (reductionTopology I n) _
      (discreteTopology_reductionTopology I n))
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))
    (by
      let _ := reductionTopology I (n + 1)
      let _ := reductionTopology I n
      have := discreteTopology_reductionTopology I (n + 1)
      exact continuous_of_discreteTopology)

/-- The inverse system `n ↦ (Λ ⧸ Iⁿ)_Y` of sheaves of rings, with the reduction maps. -/
noncomputable def reductionRingSheafSystem :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1} :=
  Functor.ofOpSequence (reductionRingSheafMap Y I)

/-- Completed integral coefficient sheaf.

The completed coefficient sheaf `𝒪̂_{E,Y} = lim_n (A_{E,n})_Y` on the small pro-étale site of
`Y`, the limit of the reductions `(Λ ⧸ Iⁿ)_Y` in the category of sheaves of rings. -/
noncomputable def completedIntegralSheaf : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1} :=
  limit (reductionRingSheafSystem Y I)

/-- The projection `𝒪̂_{E,Y} ⟶ (A_{E,n})_Y`. -/
noncomputable def completedIntegralSheafπ (n : ℕ) :
    completedIntegralSheaf Y I ⟶ reductionRingSheaf Y I n :=
  limit.π (reductionRingSheafSystem Y I) (op n)

/-- The projections are compatible with the reduction maps. -/
@[reassoc (attr := simp)]
lemma completedIntegralSheafπ_reductionRingSheafMap (n : ℕ) :
    completedIntegralSheafπ Y I (n + 1) ≫ reductionRingSheafMap Y I n =
      completedIntegralSheafπ Y I n := by
  have := limit.w (reductionRingSheafSystem Y I) (homOfLE n.le_succ).op
  simpa [completedIntegralSheafπ, reductionRingSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
    using this

/-- The category `Sh(Y_proét, 𝒪_E)` of sheaves of modules over the completed coefficient sheaf
`𝒪̂_{E,Y}` (blueprint `situation-conventions`, Mathlib's `SheafOfModules`). It is
abelian. -/
abbrev CompletedIntegralModule : Type _ :=
  SheafOfModules.{u + 1} (completedIntegralSheaf Y I)

/-- The category of `𝒪̂_{E,Y}`-modules is abelian. -/
noncomputable example : Abelian (CompletedIntegralModule Y I) := inferInstance

attribute [local instance] HasDerivedCategory.standard in
/-- The derived category `D(Y_proét, 𝒪_E)` of `𝒪̂_{E,Y}`-modules: the localization of the
category of complexes at the quasi-isomorphisms. Its cohomology sheaves are the homology
functors `DerivedCategory.homologyFunctor`. -/
abbrev CompletedIntegralDerivedCategory : Type _ :=
  DerivedCategory (CompletedIntegralModule Y I)

/-- The restriction of scalars `Res_n : Sh(Y_proét, A_{E,n}) ⥤ Sh(Y_proét, 𝒪_E)` along the
projection `𝒪̂_{E,Y} ↠ (A_{E,n})_Y`, which makes every `A_{E,n}`-module an
`𝒪̂_{E,Y}`-module. -/
noncomputable def restrictScalarsReduction (n : ℕ) :
    SheafOfModules.{u + 1} (reductionRingSheaf Y I n) ⥤ CompletedIntegralModule Y I :=
  SheafOfModules.restrictScalars (completedIntegralSheafπ Y I n)

/-- The restriction of scalars along the reduction map `(A_{E,n+1})_Y ⟶ (A_{E,n})_Y`. -/
noncomputable def restrictScalarsReductionMap (n : ℕ) :
    SheafOfModules.{u + 1} (reductionRingSheaf Y I n) ⥤
      SheafOfModules.{u + 1} (reductionRingSheaf Y I (n + 1)) :=
  SheafOfModules.restrictScalars (reductionRingSheafMap Y I n)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme SheafOfModules

variable (Y : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) (n : ℕ)

instance additive_restrictScalarsReduction : (restrictScalarsReduction Y I n).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars _).Additive

/-- The restriction of scalars `Res_n` does not change the underlying sheaves of abelian groups:
`Res_n` followed by the forgetful functor to abelian sheaves is the forgetful functor. -/
noncomputable def restrictScalarsReductionCompToSheafIso :
    restrictScalarsReduction Y I n ⋙ toSheaf.{u + 1} (completedIntegralSheaf Y I) ≅
      toSheaf.{u + 1} (reductionRingSheaf Y I n) :=
  Iso.refl _

/-- Exactness of restriction of scalars, the left exactness half. `Res_n` preserves finite
limits: it is the identity on the underlying sheaves of abelian groups
(`restrictScalarsReductionCompToSheafIso`), and the forgetful functor `SheafOfModules.toSheaf` to
abelian sheaves preserves finite limits and reflects isomorphisms, hence reflects finite
limits. -/
instance preservesFiniteLimits_restrictScalarsReduction :
    PreservesFiniteLimits (restrictScalarsReduction Y I n) where
  preservesFiniteLimits J _ _ := by
    have : PreservesLimitsOfShape J
        (restrictScalarsReduction Y I n ⋙ toSheaf.{u + 1} (completedIntegralSheaf Y I)) :=
      preservesLimitsOfShape_of_natIso (restrictScalarsReductionCompToSheafIso Y I n).symm
    have : ReflectsLimitsOfShape J (toSheaf.{u + 1} (completedIntegralSheaf Y I)) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact preservesLimitsOfShape_of_reflects_of_preserves _
      (toSheaf.{u + 1} (completedIntegralSheaf Y I))

/-- Exactness of restriction of scalars, the right exactness half. `Res_n` preserves finite
colimits: it is the identity on the underlying sheaves of abelian groups
(`restrictScalarsReductionCompToSheafIso`), and the forgetful functor `SheafOfModules.toSheaf` to
abelian sheaves preserves finite colimits and reflects isomorphisms, hence reflects finite
colimits. -/
instance preservesFiniteColimits_restrictScalarsReduction :
    PreservesFiniteColimits (restrictScalarsReduction Y I n) where
  preservesFiniteColimits J _ _ := by
    have : PreservesColimitsOfShape J
        (restrictScalarsReduction Y I n ⋙ toSheaf.{u + 1} (completedIntegralSheaf Y I)) :=
      preservesColimitsOfShape_of_natIso (restrictScalarsReductionCompToSheafIso Y I n).symm
    have : ReflectsColimitsOfShape J (toSheaf.{u + 1} (completedIntegralSheaf Y I)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves _
      (toSheaf.{u + 1} (completedIntegralSheaf Y I))

/-- Exactness of restriction of scalars. `Res_n : Sh(Y_proét, A_{E,n}) ⥤ Sh(Y_proét, 𝒪_E)` is
exact: it preserves finite limits and finite colimits
(`preservesFiniteLimits_restrictScalarsReduction`,
`preservesFiniteColimits_restrictScalarsReduction`), so it sends short exact sequences to short
exact sequences. -/
theorem restrictScalarsReduction_exact :
    PreservesFiniteLimits (restrictScalarsReduction Y I n) ∧
      PreservesFiniteColimits (restrictScalarsReduction Y I n) :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale

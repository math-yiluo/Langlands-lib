/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison

/-!

# The derived comparison functors

The comparison functor `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` of
`WeilConjectures.SixFunctors.ProEtale.Comparison.Defs` is exact, so it induces functors
`D(ν^*) : D(X_ét) ⥤ D(X_proét)` and `D⁺(ν^*) : D⁺(X_ét) ⥤ D⁺(X_proét)` by applying it termwise
to complexes. As for the pullback in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`, these functors and
the right derived functor `R⁺ν_*` are not given definitions of their own:
they are the generic constructions `D(-)`, `D+(-)` and `R+(-)` of the folder
`WeilConjectures.CategoryTheory.DerivedCategory`, recorded below as `example`s.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus`: the adjunction
  `D+(ν^*(X)[A]) ⊣ R+(ν_*(X)[A])` between the bounded below derived categories of étale and
  pro-étale sheaves.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`: the unit
  `M ⟶ Rν_* ν^* M` is an isomorphism for bounded below `M`. On a bounded below complex `I` of
  injectives it is the unit of `ν^* ⊣ ν_*` on `I`, which is invertible, followed by the unit
  `ν_* ν^* I ⟶ R⁺ν_* ν^* I`, which is invertible because `ν^*` sends injectives to
  `ν_*`-acyclic objects
  (`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`).

-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

/-- The functor `D(ν^*) : D(X_ét) ⥤ D(X_proét)` induced by the exact functor `ν^*`. -/
noncomputable example :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  D(ν^*(X)[A])

/-- The functor `D⁺(ν^*) : D⁺(X_ét) ⥤ D⁺(X_proét)` induced by the exact functor `ν^*`. -/
noncomputable example :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) :=
  D+(ν^*(X)[A])

/-- The right derived functor `R⁺ν_* : D⁺(X_proét) ⥤ D⁺(X_ét)` of the restriction `ν_*`. -/
noncomputable example :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
  R+(ν_*(X)[A])

/-- An object of the derived category of pro-étale sheaves is *bounded below of étale origin*
if it is isomorphic to `D(ν^*) K'` for a bounded below complex `K'` of étale sheaves. This is the
class of objects on which the exceptional adjunction of blueprint
`theorem-existence-exceptional-inverse-image` (c) holds. -/
def DerivedCategory.plusEtaleOrigin :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedCategory.TStructure.t.plus.map D(ν^*(X)[A])

variable {A X} in
/-- `D(ν^*) K'` is bounded below of étale origin for a bounded below `K'`. -/
lemma DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK' : DerivedCategory.TStructure.t.plus K') :
    DerivedCategory.plusEtaleOrigin A X (D(ν^*(X)[A]).obj K') :=
  ObjectProperty.prop_map_obj _ _ hK'

instance : (DerivedCategory.plusEtaleOrigin A X).IsClosedUnderIsomorphisms :=
  inferInstanceAs (DerivedCategory.TStructure.t.plus.map _).IsClosedUnderIsomorphisms

variable {A X} in
/-- An object bounded below of étale origin is bounded below. -/
lemma DerivedCategory.plusEtaleOrigin.plus
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.plusEtaleOrigin A X K) : DerivedCategory.TStructure.t.plus K := by
  obtain ⟨K', ⟨n, hn⟩, ⟨e⟩⟩ := hK
  exact DerivedCategory.TStructure.t.plus.prop_of_iso e
    ⟨n, (ν^*(X)[A]).isGE_mapDerivedCategory_obj K' n⟩

section Adjunction

/- The closed symmetric preadditive monoidal structure and the functorial flat resolutions on
the coefficient category, as in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`:
the adjunction is obtained from the unbounded derived adjunction, whose left adjoint is
derived via K-flat resolutions of étale sheaves. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The adjunction `D⁺(ν^*) ⊣ R⁺ν_*` between the bounded below derived categories of étale and
pro-étale sheaves, induced by the adjunction `ν^* ⊣ ν_*`. -/
noncomputable def derivedComparisonAdjunctionPlus : D+(ν^*(X)[A]) ⊣ R+(ν_*(X)[A]) :=
  (comparisonAdjunction A X).derivedAdjunctionPlus

/-- The adjunction `D(ν^*) ⊣ Rν_*` between the unbounded derived categories of étale and
pro-étale sheaves, induced by the adjunction `ν^* ⊣ ν_*`: the derived adjunction
`Lν^* ⊣ Rν_*`, read through the identification `Lν^* ≅ D(ν^*)` of the left derived functor of
the exact functor `ν^*`. -/
noncomputable def derivedComparisonAdjunction : D(ν^*(X)[A]) ⊣ R(ν_*(X)[A]) :=
  (comparisonAdjunction A X).derivedAdjunction.ofNatIsoLeft
    (ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory

/-- Blueprint `theorem-bounded-below-cohomology-comparison`: The pro-étale comparison

*Full faithfulness on `D⁺`.* For a bounded below complex `M` of étale sheaves, the unit
`M ⟶ Rν_* ν^* M` of the comparison adjunction is an isomorphism: this is the assertion
`id ≅ Rν_{T*} ν_T^*` on `D⁺(T_ét)` of the blueprint (Bhatt–Scholze, *The pro-étale topology for
schemes*, Corollary 5.1.6), which makes `ν^* : D⁺(X_ét) ⥤ D(X_proét)` fully faithful. -/
theorem isIso_derivedComparisonAdjunction_unit_app
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hM : DerivedCategory.TStructure.t.plus M) :
    IsIso ((derivedComparisonAdjunction A X).unit.app M) := by
  -- the unit of the bounded below adjunction is invertible: `ν^*` is exact, the unit of
  -- `ν^* ⊣ ν_*` is invertible and `ν^*` sends injectives to `ν_*`-acyclic objects
  have := isIso_comparisonAdjunction_unit A X
  have hplus := (comparisonAdjunction A X).isIso_derivedPlus_unit_app_of_rightAcyclic
    (fun _ _ ↦ inferInstance) (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective A X I)
    ⟨M, hM⟩
  rw [← (comparisonAdjunction A X).derivedAdjunctionPlus_eq_derivedPlus] at hplus
  -- it is the restriction of the unbounded unit along the inclusion of `D⁺`
  have h := (derivedComparisonAdjunction A X).map_restrictFullyFaithful_unit_app
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ν^*(X)[A]).mapDerivedCategoryPlusCompatibility.symm
    (ν_*(X)[A]).rightDerivedFunctorPlusCompatibility.symm ⟨M, hM⟩
  change DerivedCategory.Plus.ι.map
    ((comparisonAdjunction A X).derivedAdjunctionPlus.unit.app ⟨M, hM⟩) = _ at h
  have : IsIso (DerivedCategory.Plus.ι.map
      ((comparisonAdjunction A X).derivedAdjunctionPlus.unit.app ⟨M, hM⟩)) := inferInstance
  rw [h] at this
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ _ this

variable {A X} in
/-- `D(ν^*)` is fully faithful on bounded below complexes: for `K` and `M` in `D⁺(X_ét)`,
`D(ν^*)` induces a bijection `Hom(K, M) ≃ Hom(ν^* K, ν^* M)`. It is the composite of the
bijection `Hom(K, M) ≃ Hom(K, Rν_* ν^* M)` given by the unit, which is invertible at the bounded
below `M` (`isIso_derivedComparisonAdjunction_unit_app`), and the adjunction
`D(ν^*) ⊣ Rν_*`. Only `M` needs to be bounded below. -/
lemma bijective_comparisonUpperStar_mapDerivedCategory_map
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hM : DerivedCategory.TStructure.t.plus M) :
    Function.Bijective (fun g : K ⟶ M ↦ D(ν^*(X)[A]).map g) := by
  have := isIso_derivedComparisonAdjunction_unit_app A X M hM
  have h : (fun g : K ⟶ M ↦ D(ν^*(X)[A]).map g) = fun g ↦
      ((derivedComparisonAdjunction A X).homEquiv K _).symm
        (g ≫ (derivedComparisonAdjunction A X).unit.app M) := by
    ext g
    simp [Adjunction.homEquiv_counit]
  rw [h]
  exact ((derivedComparisonAdjunction A X).homEquiv K _).symm.bijective.comp
    ((asIso ((derivedComparisonAdjunction A X).unit.app M)).homToEquiv.bijective)

end Adjunction

end AlgebraicGeometry.ProEtale

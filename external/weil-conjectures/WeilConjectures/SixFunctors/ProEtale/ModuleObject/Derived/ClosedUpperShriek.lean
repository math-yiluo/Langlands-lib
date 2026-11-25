/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedUpperShriek

/-!
# The derived exceptional inverse image along a closed immersion on module objects

For a closed immersion `i : Z ⟶ X` with open complement `j`, the pushforward `i_*` of module
objects over `Λ_X` is exact and left adjoint to `i^!₀ = i^* Γ_Z`
(`ProEtale.CondensedRing.lowerStarClosedUpperShriekAdjunction`), so the levelwise functor `D(i_*)`
is left adjoint to the total right derived functor `Ri^!₀` on the unbounded derived categories
(`ProEtale.CondensedRing.derivedLowerStarClosedUpperShriekAdjunction`). This is the module-object
form of the adjunction `i_* ⊣ Ri^!` of blueprint `lemma-sections-support-closed-subscheme`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j]

/-- The adjunction `D(i_*) ⊣ Ri^!₀` on the unbounded derived categories of module objects, for a
closed immersion `i` with quasi-compact open complement `j` (`i_*` is then exact,
`ProEtale.CondensedRing.preservesFiniteColimits_lowerStar_of_isCompl`). -/
noncomputable def derivedLowerStarClosedUpperShriekAdjunction
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) [PreservesFiniteColimits (i)_*⟦Λ⟧] :
    ((i)_*⟦Λ⟧).mapDerivedCategory ⊣ (closedUpperShriek Λ i j).rightDerivedFunctor :=
  (lowerStarClosedUpperShriekAdjunction Λ i j hij).mapDerivedCategoryRightDerivedAdjunction

end AlgebraicGeometry.ProEtale.CondensedRing

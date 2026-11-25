/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# Complexes supported on a finite set of points

The last step of the proof of blueprint `theorem-verdier-biduality--1`: the cone `Δ` of the
double-dual map is supported on a finite set of closed points, and its direct image to the base
field vanishes, so `Δ = 0`. Here this is the following statement: if `K ∈ D(X_ét, Λ)` restricts to
zero on the complement of a closed subscheme `i : Z ⟶ X` which is finite over the base `S`, and
`Ra_* K = 0` for the structure morphism `a : X ⟶ S`, then `K = 0`
(`AlgebraicGeometry.Etale.isZero_of_isZero_rightDerivedLowerStar_of_isFinite`). Indeed
`K ≅ Ri_* i^* K` by the open–closed triangle, `Ra_* Ri_* ≅ R(i ≫ a)_*`, and the direct image
along the finite `i ≫ a` is exact and detects zero objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The derived direct image along a finite morphism detects zero objects: `f_*` is exact and
detects zero sheaves (`AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj_of_isFinite`). -/
theorem isZero_of_isZero_rightDerivedLowerStar_obj_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] {N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : IsZero ((R((f)_*[ModuleCat.{u + 1} Λ])).obj N)) : IsZero N := by
  have h₁ : IsZero (((f)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj N) :=
    hN.of_iso ((Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory _ f).app N).symm
  refine _root_.DerivedCategory.isZero_of_forall_isZero_homology _ fun q ↦ ?_
  refine isZero_of_isZero_lowerStar_obj_of_isFinite Λ f ?_
  exact ((_root_.DerivedCategory.homologyFunctor _ q).map_isZero h₁).of_iso
    ((((f)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app N)

/-- Blueprint `theorem-verdier-biduality--1`, the final step: let `a : X ⟶ S`, let
`i : Z ⟶ X` be a closed immersion with `i ≫ a` finite and `j : U ⟶ X` the open complement. If
`K ∈ D(X_ét, Λ)` restricts to zero on `U` and `Ra_* K = 0`, then `K = 0`. -/
theorem isZero_of_isZero_rightDerivedLowerStar_of_isFinite {X S Z U : Scheme.{u}} (a : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ a)] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hj : IsZero (D((j)^*[ModuleCat.{u + 1} Λ]).obj K))
    (ha : IsZero ((R((a)_*[ModuleCat.{u + 1} Λ])).obj K)) : IsZero K := by
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij K
  have hi : IsIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K) :=
    (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ hw).1 (Functor.map_isZero _ hj)
  let N := D((i)^*[ModuleCat.{u + 1} Λ]).obj K
  have hN : IsZero ((R((i ≫ a)_*[ModuleCat.{u + 1} Λ])).obj N) :=
    (ha.of_iso ((R((a)_*[ModuleCat.{u + 1} Λ])).mapIso (asIso
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K)).symm)).of_iso
      ((rightDerivedLowerStarComp _ i a).app N).symm
  exact (Functor.map_isZero _ (isZero_of_isZero_rightDerivedLowerStar_obj_of_isFinite Λ
    (i ≫ a) hN)).of_iso (asIso
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app K))

end Etale

end AlgebraicGeometry

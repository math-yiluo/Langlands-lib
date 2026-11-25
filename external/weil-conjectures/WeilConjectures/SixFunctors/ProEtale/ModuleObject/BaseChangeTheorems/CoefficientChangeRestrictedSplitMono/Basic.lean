/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted.Basic

/-!
# Split restricted base change maps under flat coefficient change

For a commutative square `sq : g' ≫ p' = p ≫ g` and `i : Z ⟶ Y'`, flat extension of scalars
along `a : Λ ⟶ Λ'` carries the restricted base change map
`Li^* BC_sq(K) : Li^* Lg^* Rp_* K ⟶ Li^* Rp'_* Lg'^* K`, if it is a split monomorphism, to a split
monomorphism (`ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_derivedExtendScalars`),
through the arrow isomorphisms
`ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Flat

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Flat extension of scalars and split restricted base change maps**: if the restricted base
change map with coefficients `Λ` is a split monomorphism at `K` and the comparisons
`derivedPushHom a` are invertible at `K` and `Lg'^* K`, the one with coefficients `Λ'` is a split
monomorphism at `T K`. -/
theorem isSplitMono_map_baseChangeMap_app_derivedExtendScalars
    (H : DerivedPullIsoCompCoherence a) (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a p).app K))
    (h₂ : IsIso ((derivedPushHom a p').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K)))
    (hK : IsSplitMono ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) :
    IsSplitMono ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  Arrow.isSplitMono_of_iso
    (nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat a H sq i K h₁
      h₂).some.symm

end Flat

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.EtaleDescent
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Complexes étale-locally concentrated in one degree

Let `u : U ⟶ T` be surjective and étale and let `K ∈ D(T_ét, Λ)`. If `Lu^* K` is a finite
locally constant sheaf placed in degree `r`, then so is `K`: the cohomology sheaves of `K` vanish
outside degree `r` (`AlgebraicGeometry.Etale.isZero_homology_of_leftDerivedUpperStar_iso`) and
`H^r(K)` is finite locally constant
(`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_homology_of_leftDerivedUpperStar_iso`).
Together with `DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj` this is the
blueprint lemma `lem-pur-concentrated-complex-shift`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_homology_of_leftDerivedUpperStar_iso`,
  `AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_homology_of_leftDerivedUpperStar_iso`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {U T : Scheme.{u}} (u : U ⟶ T) [Etale u] [Surjective u]
  {K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {r : ℤ}
  {L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

omit [Etale u] in
/-- Blueprint `lem-pur-concentrated-complex-shift`: Complexes with cohomology in a single degree

*Vanishing detected on an étale cover.* Let `u : U ⟶ T` be surjective (for instance a surjective
étale cover). If
`Lu^* K ≅ L[-r]` for a sheaf `L` on `U`, then `H^i(K) = 0` for every `i ≠ r`: pullback is exact,
so `u^* H^i(K) ≅ H^i(Lu^* K) = 0`, and `u^*` reflects vanishing, `u` being surjective. -/
theorem isZero_homology_of_leftDerivedUpperStar_iso
    (e : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (DerivedCategory.singleFunctor _ r).obj L)
    (i : ℤ) (hi : i ≠ r) : IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
  have hL : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ r).obj L)) := by
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ r i hi
    · exact DerivedCategory.isZero_of_isLE _ r i hi
  have hu : IsZero (((u)^*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.homologyFunctor _ i).obj K)) :=
    hL.of_iso ((leftDerivedUpperStarHomologyFunctorIso _ u i).app K ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e)
  have := Etale.faithful_upperStar_of_surjective Λ u u.surjective
  rw [IsZero.iff_id_eq_zero]
  exact ((u)^*[ModuleCat.{u + 1} Λ]).map_injective (by simpa using hu.eq_of_src _ _)

/-- Blueprint `lem-pur-concentrated-complex-shift`: Complexes with cohomology in a single degree

*Local constancy detected on an étale cover.* Let `u : U ⟶ T` be surjective and étale. If
`Lu^* K ≅ L[-r]` for a finite locally constant sheaf `L` on `U`, then `H^r(K)` is finite
locally constant on `T`: its pullback `u^* H^r(K) ≅ H^r(Lu^* K) ≅ L` is, and local constancy
and finiteness of the stalks descend along `u`. -/
theorem isFiniteLocallyConstantSheaf_homology_of_leftDerivedUpperStar_iso
    [IsFiniteLocallyConstantSheaf L]
    (e : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ≅ (DerivedCategory.singleFunctor _ r).obj L) :
    IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ r).obj K) := by
  have : IsFiniteLocallyConstantSheaf (((u)^*[ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.homologyFunctor _ r).obj K)) :=
    IsFiniteLocallyConstantSheaf.of_iso (F := L)
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso _ r).app L).symm ≪≫
        (DerivedCategory.homologyFunctor _ r).mapIso e.symm ≪≫
        ((leftDerivedUpperStarHomologyFunctorIso _ u r).app K).symm)
  exact IsFiniteLocallyConstantSheaf.of_upperStar_of_etale u _

end Etale

end AlgebraicGeometry

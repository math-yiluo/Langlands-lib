/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity

/-!

# Restricting the unit of a proper pushforward along a universally homeomorphic fibre

Consider a cartesian square of schemes separated and of finite type over a field `k'`
```
F --e'--> W
|         |
q         ν
v         v
Z --e---> D
```
with `ν` proper and `q` a finite universal homeomorphism. Then the restriction along `e` of the
unit `Λ_D ⟶ Rν_* Lν^* Λ_D` of `Lν^* ⊣ Rν_*` is an isomorphism, for `Λ = ℚ̲̄_ℓ`
(`ProEtale.CondensedRing.isIso_leftDerivedUpperStar_map_unit_app_unit_of_isPullback`).

By proper base change, `Le^*(η_ν)` composed with the base-change morphism is the unit `η_q`
followed by `Rq_*` of the pullback comparison; the base-change morphism is invertible by proper
base change, and so is `η_q` by topological invariance.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {W D Z F : Over (Spec (.of k'))}
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  {ν : W ⟶ D} {e : Z ⟶ D} {e' : F ⟶ W} {q : F ⟶ Z}

/-- On bounded constructible complexes, the restriction `Le^*(η_ν)` of the unit of `Lν^* ⊣ Rν_*`
along `e` is an isomorphism, for a cartesian square with `ν` proper and `q` a finite universal
homeomorphism. -/
theorem isIso_boundedConstructibleUpperStar_map_unit_app_of_isPullback (sq : IsPullback e' q ν e)
    [IsProper ν.left] [IsFinite q.left] [IsUniversalHomeomorphism q.left]
    (K : Dᵇc(D.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ ν).unit.app K)) := by
  have hBC := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
  rw [boundedConstructibleBaseChange_eq_exchangeRight] at hBC
  have hη := isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction ℓ q
  have : IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ ν).unit.app K) ≫
      (Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ ν)
        (boundedConstructibleUpperStarLowerStarAdjunction ℓ q)
        (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
          sq.toCommSq)).app _) := by
    rw [Adjunction.map_unit_app_comp_exchangeRight_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Adjunction.exchangeRight (boundedConstructibleUpperStarLowerStarAdjunction ℓ ν)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ q)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq)).app _)

/-- **The restricted unit of a proper pushforward**: for a cartesian square of schemes
`e' ≫ ν = q ≫ e` with `ν` proper and `q` a finite universal homeomorphism, the restriction
`Le^*(η_ν) : Le^* Λ_D ⟶ Le^* Rν_* Lν^* Λ_D` of the unit of `Lν^* ⊣ Rν_*` at `Λ_D = ℚ̲̄_ℓ` is an
isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_unit_app_unit_of_isPullback (sq : IsPullback e' q ν e)
    [IsProper ν.left] [IsFinite q.left] [IsUniversalHomeomorphism q.left] :
    IsIso (L((e.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
      ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ν.left).unit.app
        (𝟙_ _))) := by
  have := isIso_boundedConstructibleUpperStar_map_unit_app_of_isPullback ℓ sq
    ⟨𝟙_ _, (boundedConstructible _).prop_unit⟩
  have hunit := boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom ℓ ν
    ⟨𝟙_ _, (boundedConstructible _).prop_unit⟩
  dsimp only at hunit
  rw [← hunit]
  exact Functor.map_isIso
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)).ι
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e).map
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ ν).unit.app
        ⟨𝟙_ _, (boundedConstructible _).prop_unit⟩))

end AlgebraicGeometry.ProEtale.CondensedRing

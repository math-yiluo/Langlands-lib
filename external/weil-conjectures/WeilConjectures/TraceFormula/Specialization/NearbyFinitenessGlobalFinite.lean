/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFinitenessFinite
public import WeilConjectures.TraceFormula.Specialization.TraitModelEmbedding
public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchangeFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedPointsFiniteness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStarProperBoundedConstructible

/-!

# The global step of Deligne's finiteness theorem, finite coefficients

Let `S = Spec k'⟦t⟧` with `k'` separably closed, `T` a finite discrete ring whose exponent is
invertible in `k'`, and `q : P ⟶ S` proper, with special fibre `p : P_s ⟶ Spec k'`. For a
bounded constructible complex `B` of `T̲`-modules on `P`:

* the cohomology `Rp_* Ψ_P B` of the geometric nearby cycles of the standard model of `P` is
  bounded constructible
  (`boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper_of_finite`):
  by the proper exchange
  (`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient`)
  it is `Ψ_S (Rq_* B)`, where `Rq_* B` is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj_of_isProper_of_finite`)
  and so are the nearby cycles of the trait
  (`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel_of_finite`);
* hence `Ψ_P B` is bounded constructible as soon as its pullbacks along finitely many morphisms
  `hᵢ : Wᵢ ⟶ P_s` from Noetherian schemes, whose images contain the non-closed points, are
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_finite`), by Deligne's
  criterion at closed points
  (`boundedConstructible_of_leftDerivedUpperStar_of_rightDerivedLowerStar_of_isProper`).

This is the global step of Deligne's proof (SGA 4½, [Th. finitude], proof of 3.2).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The nearby cycles of a model with quasi-compact quasi-separated `j` preserve the complexes
bounded below of étale origin, with finite coefficients. -/
lemma plusEtaleOrigin_nearbyCycles_obj_of_finite {X X' : Scheme.{u}}
    (M : NearbyCyclesModel X X') [QuasiCompact M.j] [QuasiSeparated M.j]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj K)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X'
      ((finiteCoefficientDerivedEquivalence X' T).functor.obj
        ((M.nearbyCycles (Profinite.continuousMapRingObj T)).obj K)) :=
  plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T M.i
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_rightDerivedLowerStar_obj T M.j
      (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T M.ε hK))

variable {k' : Type u} [Field k'] [IsSepClosed k']
  [HasInvertibleExponent (ULift.{u + 1} T) (Spec (.of k'))]

/-- **Cohomology of the nearby cycles of a proper scheme over the trait, finite coefficients**
(SGA 4½, [Th. finitude], proof of 3.2): for a proper `q : P ⟶ S` and a bounded constructible
complex `B` of `T̲`-modules on `P`, the cohomology `RΓ(P_s, Ψ_P B)` of the geometric nearby
cycles is bounded constructible on `Spec k'`: by the proper exchange it is `Ψ_S (Rq_* B)`. -/
theorem boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper_of_finite
    {P : Scheme.{u}} (q : P ⟶ trait k') [IsProper q]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) P))}
    (hB : boundedConstructible _ B) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) (Spec (.of k')))
      ((R(((traitStdSpecialFibre q).hom)_*⟦Profinite.continuousMapRingObj T⟧)).obj
        (((traitStdModel q).geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj B)) := by
  let M := traitStdModel q
  let ψ : M.geometric.Hom (traitSelfModel k').geometric q
      (pullback.snd q (traitClosedPoint k')) :=
    { total := q
      generic := pullback.snd q (traitGenericPoint k')
      comm_j := pullback.condition.symm
      comm_i := pullback.condition.symm
      comm_ε := pullback.condition.symm }
  have : IsProper ψ.total := inferInstanceAs (IsProper q)
  have : QuasiCompact M.geometric.j :=
    inferInstanceAs (QuasiCompact (pullback.fst q (traitGenericPoint k')))
  have : QuasiSeparated M.geometric.j :=
    inferInstanceAs (QuasiSeparated (pullback.fst q (traitGenericPoint k')))
  have hiso := Hom.isIso_pushforwardExchange_app_of_isProper_finiteCoefficient T ψ
    (IsPullback.of_hasPullback q (traitClosedPoint k'))
    (IsPullback.of_hasPullback q (traitGenericPoint k')) B
    (boundedConstructible_iff_of_finite T B |>.1 hB).plusEtaleOrigin
  have := (isTraitModel_traitSelfModel k').isNoetherian_total
  have h₁ := preservesBoundedConstructible_traitSelfModel_of_finite k' T _
    (boundedConstructible_rightDerivedLowerStar_obj_of_isProper_of_finite T (traitToBase k' k')
      q hB)
  exact (boundedConstructible _).prop_of_iso (@asIso _ _ _ _ _ hiso) h₁

/-- **Deligne's finiteness criterion for the nearby cycles of a proper scheme over the trait,
finite coefficients** (SGA 4½, [Th. finitude], proof of 3.2): let `q : P ⟶ S` be proper, `B` a
bounded constructible complex of `T̲`-modules on `P` and `hᵢ : Wᵢ ⟶ P_s` finitely many morphisms
from Noetherian schemes whose images contain the non-closed points of the special fibre. If the
pullbacks `Lhᵢ^* Ψ_P B` are bounded constructible, then so is `Ψ_P B`. -/
theorem boundedConstructible_nearbyCycles_traitStdModel_of_finite {P : Scheme.{u}}
    (q : P ⟶ trait k') [IsProper q] {ι : Type*} [Finite ι] {W : ι → Scheme.{u}}
    [∀ i, IsNoetherian (W i)] (h : ∀ i, W i ⟶ (traitStdSpecialFibre q).left)
    (hcov : ∀ x ∉ closedPoints (traitStdSpecialFibre q).left, ∃ (i : ι) (w : W i), h i w = x)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) P))}
    (hB : boundedConstructible _ B)
    (hW : ∀ i, boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) (W i))
      ((L(CondensedRing.upperStar (Profinite.continuousMapRingObj T) (h i))).obj
        (((traitStdModel q).geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj B))) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (traitStdSpecialFibre q).left)
      (((traitStdModel q).geometric.nearbyCycles (Profinite.continuousMapRingObj T)).obj B) := by
  have : IsProper (traitStdSpecialFibre q).hom :=
    inferInstanceAs (IsProper (pullback.snd q (traitClosedPoint k')))
  have : QuasiCompact (traitStdModel q).geometric.j :=
    inferInstanceAs (QuasiCompact (pullback.fst q (traitGenericPoint k')))
  have : QuasiSeparated (traitStdModel q).geometric.j :=
    inferInstanceAs (QuasiSeparated (pullback.fst q (traitGenericPoint k')))
  exact boundedConstructible_of_leftDerivedUpperStar_of_rightDerivedLowerStar_of_isProper T
    (traitStdSpecialFibre q).hom h hcov _
    (plusEtaleOrigin_nearbyCycles_obj_of_finite T _
      (boundedConstructible_iff_of_finite T B |>.1 hB).plusEtaleOrigin) hW
    (boundedConstructible_lowerStar_nearbyCycles_traitStdModel_of_isProper_of_finite T q hB)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

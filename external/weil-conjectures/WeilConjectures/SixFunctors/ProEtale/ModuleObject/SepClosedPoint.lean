/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!

# The pullback from the point to a separably closed point

Let `Ω` be a separably closed field. The functor `S ↦ Spec C(S, Ω)` identifies profinite sets
with a dense subsite of the pro-étale site of `Spec Ω`
(`AlgebraicGeometry.ProEtale.geometricFieldProfiniteDenseSubsite`, Bhatt–Scholze, Example
4.1.10), so the pullback `p^* : Sh(*_proét, Ab) ⥤ Sh((Spec Ω)_proét, Ab)` from condensed abelian
groups is an equivalence. Its right adjoint `p_*` is lax monoidal and the adjunction `p^* ⊣ p_*`
is monoidal, so `p^*` also induces an equivalence `Mod_Λ ⥤ Mod_{p^* Λ}` on module objects over
any condensed ring `Λ` (blueprint `proposition-pro-etale-site-separably-closed`).

## Main results

- `AlgebraicGeometry.ProEtale.isEquivalence_upperStarFromPoint`: for `Ω` separably closed,
  `p^* : Sh(*_proét, Ab) ⥤ Sh((Spec Ω)_proét, Ab)` is an equivalence.
- `AlgebraicGeometry.ProEtale.isEquivalence_mapMod_upperStarFromPoint`: for `Ω` separably
  closed and a condensed ring `Λ`, the pullback `Mod_Λ ⥤ Mod_{p^* Λ}` of module objects is an
  equivalence.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- For `Ω` separably closed, the direct image `p_{Spec Ω *}` to condensed abelian groups is an
equivalence: it is restriction along the dense subsite `S ↦ Spec C(S, Ω)`
(`geometricFieldProfiniteDenseSubsite`). -/
instance isEquivalence_lowerStar_comp_pointLowerStar :
    ((toSpecZ (Spec (.of Ω)))_*[Ab.{u + 1}] ⋙ pointLowerStar).IsEquivalence := by
  have := geometricFieldProfiniteDenseSubsite Ω
  exact inferInstanceAs ((profiniteToProEtOf (Spec (.of Ω))).sheafPushforwardContinuous Ab.{u + 1}
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology (Spec (.of Ω)))).IsEquivalence

/-- For `Ω` separably closed, the pullback `p^* : Sh(*_proét, Ab) ⥤ Sh((Spec Ω)_proét, Ab)`
from condensed abelian groups is an equivalence (Bhatt–Scholze, Example 4.1.10): its right
adjoint `p_* = π_* ⋙ pointLowerStar` is one. -/
instance isEquivalence_upperStarFromPoint : (upperStarFromPoint (Spec (.of Ω))).IsEquivalence :=
  (pointUpperStarLowerStarAdjunction.comp (upperStarLowerStarAdjunction Ab.{u + 1}
    (toSpecZ (Spec (.of Ω))))).isEquivalence_left_of_isEquivalence_right

/-- For `Ω` separably closed and a condensed ring `Λ`, the pullback `Mod_Λ ⥤ Mod_{p^* Λ}` from
condensed `Λ`-modules to module objects over `p^* Λ` on `(Spec Ω)_proét` is an equivalence: the
adjunction `p^* ⊣ p_*`, composite of `p^* ⊣ p_*` from the point to `Spec ℤ` and
`π^* ⊣ π_*`, is monoidal, and its module version has invertible unit and counit, these being
computed on the underlying sheaves (blueprint `proposition-pro-etale-site-separably-closed`). -/
instance isEquivalence_mapMod_upperStarFromPoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    ((upperStarFromPoint (Spec (.of Ω))).mapMod Λ).IsEquivalence := by
  let adj : upperStarFromPoint (Spec (.of Ω)) ⊣ _ :=
    pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (Spec (.of Ω))))
  have : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (Spec (.of Ω))))
      Functor.Monoidal.toOplaxMonoidal _ :=
    isMonoidal_upperStarLowerStarAdjunction _ _
  have : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _ pointUpperStarLowerStarAdjunction.{u}
      Functor.Monoidal.toOplaxMonoidal _ :=
    inferInstanceAs (@Adjunction.IsMonoidal _ _ _ _ _ _ _ _ pointUpperStarLowerStarAdjunction.{u}
      pointUpperStarLowerStarAdjunction.leftAdjointOplaxMonoidal _)
  have : adj.IsMonoidal := Adjunction.isMonoidal_comp _ _
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  let adjMod := adj.mapModAdjunction Λ
  have : IsIso adjMod.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
    have : IsIso ((Mod.forget _).map (adjMod.unit.app M)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_unit_app_hom]
      exact NatIso.isIso_app_of_isIso adj.unit M.X
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso adjMod.counit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
    have : IsIso ((Mod.forget _).map (adjMod.counit.app N)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_counit_app_hom]
      exact NatIso.isIso_app_of_isIso adj.counit N.X
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact adjMod.toEquivalence.isEquivalence_functor

end AlgebraicGeometry.ProEtale

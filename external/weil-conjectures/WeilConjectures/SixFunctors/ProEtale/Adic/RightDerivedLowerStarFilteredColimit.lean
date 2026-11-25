/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.LowerStarFilteredColimit

/-!
# Higher direct images commute with filtered colimits and direct sums

For a quasi-compact quasi-separated morphism of schemes `f : X ⟶ Y`, the pushforward `f_*` and
the higher direct images `Rᵠf_*` of abelian sheaves on the small pro-étale sites commute with
filtered colimits indexed by essentially `u + 1`-small categories
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_lowerStar`,
`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`), and with direct
sums (`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_lowerStar`,
`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_lowerStar`). This is
the complement of the blueprint node `corollary-continuity-cohomology` (for the constant ring sheaf
`ℤ`), in the case of complexes concentrated in degree `0` of the blueprint node
`corollary-continuity-cohomology--2`. In degree `0` this is
`AlgebraicGeometry.ProEtale.isColimit_lowerStar_mapCocone`; the induction step
`CategoryTheory.Functor.preservesColimitsOfShape_rightDerived_succ` uses that filtered colimits
of injective sheaves are `f_*`-acyclic
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit_of_injective`).

We deduce that filtered colimits and direct sums of `f_*`-acyclic sheaves are `f_*`-acyclic
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit`,
`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit_discrete`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- For a quasi-compact quasi-separated morphism `f`, the pushforward `f_*` of abelian sheaves on
the small pro-étale sites commutes with filtered colimits indexed by essentially `u + 1`-small
categories (`AlgebraicGeometry.ProEtale.isColimit_lowerStar_mapCocone`). -/
theorem preservesColimitsOfShape_lowerStar (J : Type v) [Category.{w} J]
    [EssentiallySmall.{u + 1} J] [IsFiltered J] :
    PreservesColimitsOfShape J (f)_*[Ab.{u + 1}] := by
  have : IsFiltered (SmallModel.{u + 1} J) := IsFiltered.of_equivalence (equivSmallModel J)
  have : PreservesColimitsOfShape (SmallModel.{u + 1} J) (f)_*[Ab.{u + 1}] :=
    ⟨fun {_} ↦ ⟨fun hc ↦ ⟨(isColimit_lowerStar_mapCocone f hc).some⟩⟩⟩
  exact preservesColimitsOfShape_of_equiv (equivSmallModel J).symm _

/-- **Higher direct images commute with filtered colimits** (blueprint
`corollary-continuity-cohomology--2`, sub-node of `corollary-continuity-cohomology`, in the case
of complexes concentrated in degree `0` and of the ring sheaf `ℤ`; [Stacks 0739] on the
pro-étale site): for a quasi-compact quasi-separated morphism `f` and a filtered diagram `(Kᵢ)`
of abelian sheaves on `X_proét` indexed by an essentially `u + 1`-small category, the canonical
map `colim Rᵠf_* Kᵢ ⟶ Rᵠf_* (colim Kᵢ)` is an isomorphism. In degree `0` this is
`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_lowerStar`; the induction step
`CategoryTheory.Functor.preservesColimitsOfShape_rightDerived_succ` needs filtered colimits of
injective sheaves to be `f_*`-acyclic
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isColimit_of_injective`). -/
theorem preservesColimitsOfShape_rightDerived_lowerStar (J : Type v) [Category.{w} J]
    [EssentiallySmall.{u + 1} J] [IsFiltered J] (q : ℕ) :
    PreservesColimitsOfShape J (((f)_*[Ab.{u + 1}]).rightDerived q) := by
  have : IsFiltered (SmallModel.{u + 1} J) := IsFiltered.of_equivalence (equivSmallModel J)
  suffices PreservesColimitsOfShape (SmallModel.{u + 1} J) (((f)_*[Ab.{u + 1}]).rightDerived q) from
    preservesColimitsOfShape_of_equiv (equivSmallModel J).symm _
  induction q with
  | zero =>
    have := preservesColimitsOfShape_lowerStar f (SmallModel.{u + 1} J)
    exact preservesColimitsOfShape_of_natIso ((f)_*[Ab.{u + 1}]).rightDerivedZeroIsoSelf.symm
  | succ q ih =>
    exact Functor.preservesColimitsOfShape_rightDerived_succ _ _ q fun D hD ↦
      have := hD
      rightAcyclic_lowerStar_of_isColimit_of_injective f (colimit.isColimit D) q

/-- **Higher direct images commute with direct sums**: for a quasi-compact
quasi-separated morphism `f`, each `Rᵠf_*` on abelian sheaves on `X_proét` commutes with direct
sums: a direct sum is the filtered colimit of its finite subsums, and `Rᵠf_*` preserves
finite direct sums, being additive, and filtered colimits
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_rightDerived_lowerStar`). -/
theorem preservesColimitsOfShape_discrete_rightDerived_lowerStar (B : Type) (q : ℕ) :
    PreservesColimitsOfShape (Discrete B) (((f)_*[Ab.{u + 1}]).rightDerived q) :=
  have := preservesColimitsOfShape_rightDerived_lowerStar f (Finset (Discrete B)) q
  preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts _

/-- For a quasi-compact quasi-separated morphism `f`, the pushforward `f_*` of abelian sheaves on
the small pro-étale sites commutes with direct sums. -/
theorem preservesColimitsOfShape_discrete_lowerStar (B : Type) :
    PreservesColimitsOfShape (Discrete B) (f)_*[Ab.{u + 1}] :=
  have := preservesColimitsOfShape_discrete_rightDerived_lowerStar f B 0
  preservesColimitsOfShape_of_natIso ((f)_*[Ab.{u + 1}]).rightDerivedZeroIsoSelf

/-- For a quasi-compact quasi-separated morphism `f`, a direct sum of `f_*`-acyclic abelian
sheaves is `f_*`-acyclic. -/
lemma rightAcyclic_lowerStar_of_isColimit_discrete {B : Type}
    {D : Discrete B ⥤ Sheaf (ProEt.topology X) Ab.{u + 1}} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, ((f)_*[Ab.{u + 1}]).rightAcyclic (D.obj j)) :
    ((f)_*[Ab.{u + 1}]).rightAcyclic c.pt := fun q ↦
  have := preservesColimitsOfShape_discrete_rightDerived_lowerStar f B (q + 1)
  (isColimitOfPreserves (((f)_*[Ab.{u + 1}]).rightDerived (q + 1)) hc).isZero_pt
    (Functor.isZero _ fun j ↦ hD j q)

/-- For a quasi-compact quasi-separated morphism `f`, a filtered colimit of `f_*`-acyclic abelian
sheaves is `f_*`-acyclic. -/
lemma rightAcyclic_lowerStar_of_isColimit {J : Type} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ Sheaf (ProEt.topology X) Ab.{u + 1}} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, ((f)_*[Ab.{u + 1}]).rightAcyclic (D.obj j)) :
    ((f)_*[Ab.{u + 1}]).rightAcyclic c.pt := fun q ↦
  have := preservesColimitsOfShape_rightDerived_lowerStar f J (q + 1)
  (isColimitOfPreserves (((f)_*[Ab.{u + 1}]).rightDerived (q + 1)) hc).isZero_pt
    (Functor.isZero _ fun j ↦ hD j q)

end AlgebraicGeometry.ProEtale

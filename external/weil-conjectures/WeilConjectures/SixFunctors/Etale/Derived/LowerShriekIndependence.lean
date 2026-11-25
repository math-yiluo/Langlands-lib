/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!

# Independence of the derived lower shriek of the compactification

Let `f : X ⟶ Y` be a quasi-compact morphism of schemes and let `c`, `d` be two
compactifications of `f`. This file constructs an isomorphism `Rf_!(c)[A]+ ≅ Rf_!(d)[A]+`
of the bounded below derived lower shrieks attached to `c` and `d`. It passes through the
common refinement `e = Compactification.inf c d`, the closure of the graph of `X` in
`c.Z ×_Y d.Z`:

`Rf_!(c)[A]+ ≅ Rf_!(e)[A]+ ≅ Rf_!(d)[A]+`,

where both isomorphisms are comparisons along a refinement with cartesian square over `X`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`). Such a
comparison is an isomorphism by proper base change. This is not proved yet and is stated
here as an instance.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso`: the isomorphism
  `Rf_!(c)[A]+ ≅ Rf_!(d)[A]+`;
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusιIso`: its
  unbounded counterpart on bounded below objects, an isomorphism
  `Plus.ι ⋙ Rf_!(c)[A] ≅ Plus.ι ⋙ Rf_!(d)[A]`.

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationPlusComparison`:
  the comparison along a refinement with cartesian square over `X` is an isomorphism
  (blueprint: `BA43-RHO`). Not proved yet.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **The unit of `D⁺(q^*) ⊣ R⁺q_*` at an extension by zero is an isomorphism**, for torsion
coefficients. Let `r : c.Refinement d` be a refinement of compactifications whose square over
`X` is cartesian, and write `q = r.hom : c.Z ⟶ d.Z` and `j = d.i`. Then the unit
`j_! K ⟶ R⁺q_* q^* j_! K` is an isomorphism for every bounded below `K`. It is checked after
the inclusion into the unbounded derived category, on the open `X` and on its closed
complement `i : W ⟶ d.Z`:

* over `X`, `q^* j_! = (c.i)_!` is fully faithful, so the unit is invisible to `j^*`
  (`CategoryTheory.Adjunction.isIso_map_unit_app_obj`);
* over `W`, both sides vanish: `i^* j_! K = 0`, and by proper base change for the proper `q`
  (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`),
  `i^* R⁺q_* q^* j_! K` is computed on `q⁻¹(W)`, which does not meet `X`. -/
theorem isIso_derivedPlus_unit_app_openImmersionLowerShriek {c d : Compactification f}
    (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    haveI : ((r.hom)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (Etale.upperStarLowerStarAdjunction _ r.hom)
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit.app
      (D+((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)) := by
  have : ((r.hom)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction _ r.hom)
  have hdisj : Disjoint (Set.range d.i.closedComplement.base) (Set.range d.i.base) := by
    rw [d.i.range_closedComplement]
    exact disjoint_compl_left
  -- full faithfulness of the extensions by zero on the bounded below derived categories
  have hff : ∀ {Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j],
      D+((j)_!open[ModuleCat.{u + 1} Λ]).Full ∧ D+((j)_!open[ModuleCat.{u + 1} Λ]).Faithful := by
    intro Z j _
    let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
    have := adj.fullyFaithfulLOfIsIsoUnit.full
    have := adj.fullyFaithfulLOfIsIsoUnit.faithful
    have : (D+((j)_!open[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.ι).Full :=
      Functor.Full.of_iso ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.symm
    have : (D+((j)_!open[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.ι).Faithful :=
      Functor.Faithful.of_iso
        ((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusCompatibility.symm
    exact ⟨Functor.Full.of_comp_faithful _ DerivedCategory.Plus.ι,
      Functor.Faithful.of_comp _ DerivedCategory.Plus.ι⟩
  have := (hff d.i).1
  have := (hff d.i).2
  have := (hff c.i).1
  have := (hff c.i).2
  have : (D+((d.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ D+((r.hom)^*[ModuleCat.{u + 1} Λ])).Full :=
    Functor.Full.of_iso (refinementLowerShriekBaseChangeDerivedPlusIso _ r hcart)
  have : (D+((d.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ D+((r.hom)^*[ModuleCat.{u + 1} Λ])).Faithful :=
    Functor.Faithful.of_iso (refinementLowerShriekBaseChangeDerivedPlusIso _ r hcart)
  have hopen := Adjunction.isIso_map_unit_app_obj
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).derivedPlus
    (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat.{u + 1} Λ) d.i) K
  -- the closed part: source and target vanish
  have hι : ∀ {Z : Scheme.{u}}
      (M : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      IsZero (DerivedCategory.Plus.ι.obj M) → IsZero M :=
    fun M hM ↦ IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι M hM
  let sq := IsPullback.of_hasPullback r.hom d.i.closedComplement
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  have hsource : IsZero (D+((d.i.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj
      (D+((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)) :=
    hι _ (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ d.i
      d.i.closedComplement hdisj (DerivedCategory.Plus.ι.obj K))
  have hN : IsZero (D+((pullback.fst r.hom d.i.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj
      (D+((r.hom)^*[ModuleCat.{u + 1} Λ]).obj (D+((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K))) := by
    refine hι _ (IsZero.of_iso ?_
      ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp _
        (pullback.fst r.hom d.i.closedComplement) r.hom) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).app _).symm)
    refine isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _
      d.i _ (hdisj.mono_left ?_) _
    rw [pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  have htarget : IsZero (D+((d.i.closedComplement)^*[ModuleCat.{u + 1} Λ]).obj
      ((r.hom)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        (D+((r.hom)^*[ModuleCat.{u + 1} Λ]).obj (D+((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)))) :=
    IsZero.of_iso
      (((pullback.snd r.hom d.i.closedComplement)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus
        |>.map_isZero hN)
      (asIso ((Etale.derivedBaseChangeMapPlus _ sq.toCommSq).app _))
  -- conclude by open–closed conservativity, after the inclusion into `D`
  suffices IsIso (DerivedCategory.Plus.ι.map ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit.app
        (D+((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K))) from
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  refine isIso_of_isIso_mapDerivedCategoryUpperStar_map _ d.i d.i.closedComplement
    d.i.range_closedComplement _ ?_ ?_
  · exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map
      (D+((d.i)^*[ModuleCat.{u + 1} Λ]).map ((Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit.app
          (D+((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)))))
  · have := isIso_of_source_target_iso_zero (D+((d.i.closedComplement)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit.app
        (D+((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K))) hsource.isoZero htarget.isoZero
    exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map
      (D+((d.i.closedComplement)^*[ModuleCat.{u + 1} Λ]).map ((Etale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit.app
          (D+((d.i)_!open[ModuleCat.{u + 1} Λ]).obj K)))))

/-- **The comparison of derived lower shrieks along a refinement is an isomorphism**, for
torsion coefficients: for a refinement `r : c.Refinement d` whose square over `X` is cartesian,
the comparison `Rf_!(d)[Λ]+ ⟶ Rf_!(c)[Λ]+` is an isomorphism. This is the isomorphism
property of `(BA43-RHO)` in the blueprint. Its composition and base change factors are
isomorphisms, and so is its unit factor by
`isIso_derivedPlus_unit_app_openImmersionLowerShriek`, which rests on proper base change for
`r.hom`. -/
instance isIso_rightDerivedLowerShriekOfCompactificationPlusComparison
    {c d : Compactification f} (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    IsIso (rightDerivedLowerShriekOfCompactificationPlusComparison (ModuleCat.{u + 1} Λ) r
      hcart) := by
  have : ((r.hom)_*[ModuleCat.{u + 1} Λ]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction _ r.hom)
  have : ∀ K, IsIso ((Functor.whiskerLeft D+((d.i)_!open[ModuleCat.{u + 1} Λ])
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit).app K) :=
    fun K ↦ isIso_derivedPlus_unit_app_openImmersionLowerShriek Λ r hcart K
  have : IsIso (Functor.whiskerLeft D+((d.i)_!open[ModuleCat.{u + 1} Λ])
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r.hom).derivedPlus.unit) :=
    NatIso.isIso_of_isIso_app _
  unfold rightDerivedLowerShriekOfCompactificationPlusComparison
  infer_instance

end Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [QuasiCompact f]

/-- **The bounded below derived lower shriek does not depend on the compactification**: for
two compactifications `c` and `d` of a quasi-compact morphism `f`, the isomorphism
`Rf_!(c)[A]+ ≅ Rf_!(d)[A]+` obtained by comparing both with the common refinement
`Compactification.inf c d`: the comparison along `Compactification.infFst c d` followed by
the inverse of the comparison along `Compactification.infSnd c d`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusIso
    (c d : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ]+ ≅ Rf_!(d)[ModuleCat.{u + 1} Λ]+ :=
  asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _
      (Compactification.infFst c d) (Compactification.isPullback_infFst c d)) ≪≫
    (asIso (rightDerivedLowerShriekOfCompactificationPlusComparison _
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).symm

/-- The unbounded derived lower shrieks attached to two compactifications `c` and `d` of a
quasi-compact morphism `f` agree on bounded below objects: the isomorphism
`Plus.ι ⋙ Rf_!(c)[A] ≅ Plus.ι ⋙ Rf_!(d)[A]` induced by
`rightDerivedLowerShriekOfCompactificationPlusIso` through the compatibilities
`rightDerivedLowerShriekOfCompactificationPlusCompatibility` of the bounded below and the
unbounded derived lower shrieks. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusιIso
    (c d : Compactification f) :
    DerivedCategory.Plus.ι ⋙ Rf_!(c)[ModuleCat.{u + 1} Λ] ≅
      DerivedCategory.Plus.ι ⋙ Rf_!(d)[ModuleCat.{u + 1} Λ] :=
  (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ c).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekOfCompactificationPlusIso Λ c d)
      DerivedCategory.Plus.ι ≪≫
    rightDerivedLowerShriekOfCompactificationPlusCompatibility _ d

end Etale

end AlgebraicGeometry


/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.Defs

/-!
# The proper-open comparison map is an isomorphism

Let `u : T₁ ⟶ T₂` be proper and `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂` open immersions with
`j₁ ≫ u = j₂` (`AlgebraicGeometry.ProperOpenDatum`). For a finite coefficient ring `Λ` the
comparison map `α_u : j₂! K ⟶ Ru_* j₁! K` of
`WeilConjectures.SixFunctors.Etale.Derived.ProperOpenComparison.Defs` is an isomorphism on
`D⁺(X_ét, Λ)` (blueprint `proposition-construction-independence-rf-shriek--7`).

The proof checks it after restriction to the open `j₂(X)` and to its closed complement
`i : Z ⟶ T₂`:

* on `j₂(X)`, `j₂^* α_u` is, up to the unit of `j₂! ⊣ j₂^*`, the inverse of the restriction
  isomorphism `θ_u` (`AlgebraicGeometry.ProperOpenDatum.homEquiv_comparison_app`);
* on `Z`, both sides vanish: `i^* j₂! K = 0`, and by proper base change for `u`
  (`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`),
  `i^* Ru_* j₁! K` is computed on `T₁ ×_{T₂} Z`, which does not meet `j₁(X)`.

## Main statements

- `AlgebraicGeometry.ProperOpenDatum.isIso_comparison_app`
- `AlgebraicGeometry.ProperOpenDatum.comparisonIso`
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

attribute [local instance] Etale.preservesInjectiveObjects_lowerStar

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace ProperOpenDatum

variable {X : Scheme.{u}} (D : ProperOpenDatum X)

/-- `j₂^*` of `α_u` is an isomorphism: its transpose under `D⁺j₂! ⊣ D⁺j₂^*` is the inverse of
the restriction isomorphism `θ_u`, and the unit of `D⁺j₂! ⊣ D⁺j₂^*` is an isomorphism. -/
instance isIso_upperStar_map_comparison_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map ((D.comparison Λ).app K)) := by
  have h := D.homEquiv_comparison_app Λ K
  rw [Adjunction.homEquiv_unit] at h
  have : IsIso ((D.adj₂ Λ).unit.app K ≫
      D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map ((D.comparison Λ).app K)) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left ((D.adj₂ Λ).unit.app K) _

/-- The fibre product `T₁ ×_{T₂} Z` over the closed complement `Z` of `j₂(X)` does not meet
`j₁(X)`. -/
lemma disjoint_range_pullback_fst_closedComplement :
    Disjoint (Set.range (pullback.fst D.u D.j₂.closedComplement).base)
      (Set.range D.j₁.base) := by
  rw [Set.disjoint_iff]
  rintro _ ⟨⟨w, rfl⟩, ⟨x, hx⟩⟩
  have hw : D.j₂.closedComplement.base (pullback.snd D.u D.j₂.closedComplement |>.base w) ∈
      (Set.range D.j₂.base)ᶜ := by
    rw [← D.j₂.range_closedComplement]; exact Set.mem_range_self _
  apply hw
  refine ⟨x, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ← hx,
    ← Scheme.Hom.comp_apply, D.comm]

variable [Finite Λ]

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: Proper pushforward of extension
by zero. For a finite coefficient ring `Λ`, the comparison map
`α_{u,K} : j₂! K ⟶ Ru_* j₁! K` is an isomorphism for every `K ∈ D⁺(X_ét, Λ)`. It is checked on
the open `j₂(X)`, where `j₂^* α_u` is adjoint to `θ_u⁻¹`
(`isIso_upperStar_map_comparison_app`), and on its closed complement `Z`, where both sides
vanish: `j₂! K` because `Z` does not meet `j₂(X)`, and `Ru_* j₁! K` by proper base change, the
fibre product `T₁ ×_{T₂} Z` not meeting `j₁(X)`. -/
instance isIso_comparison_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((D.comparison Λ).app K) := by
  set α := (D.comparison Λ).app K
  set i := D.j₂.closedComplement
  have hι : ∀ {Z : Scheme.{u}}
      (M : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      IsZero (DerivedCategory.Plus.ι.obj M) → IsZero M :=
    fun M hM ↦ IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι M hM
  have hdisj : Disjoint (Set.range i.base) (Set.range D.j₂.base) := by
    rw [D.j₂.range_closedComplement]
    exact disjoint_compl_left
  -- the source vanishes on `Z`
  have hsource : IsZero (D+((i)^*[ModuleCat.{u + 1} Λ]).obj
      (D+((D.j₂)_!open[ModuleCat.{u + 1} Λ]).obj K)) :=
    hι _ (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _
      D.j₂ i hdisj (DerivedCategory.Plus.ι.obj K))
  -- the target vanishes on `Z`, by proper base change
  let sq := IsPullback.of_hasPullback D.u i
  have := Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite sq
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
  have hN : IsZero (D+((pullback.fst D.u i)^*[ModuleCat.{u + 1} Λ]).obj
      (D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]).obj K)) :=
    hι _ (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _
      D.j₁ _ D.disjoint_range_pullback_fst_closedComplement (DerivedCategory.Plus.ι.obj K))
  have htarget : IsZero (D+((i)^*[ModuleCat.{u + 1} Λ]).obj
      (((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj
        (D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]).obj K))) :=
    IsZero.of_iso
      (((pullback.snd D.u i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map_isZero hN)
      (asIso ((Etale.derivedBaseChangeMapPlus _ sq.toCommSq).app _))
  -- conclude by open–closed conservativity, after the inclusion into `D`
  suffices IsIso (DerivedCategory.Plus.ι.map α) from
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  refine isIso_of_isIso_mapDerivedCategoryUpperStar_map _ D.j₂ i
    D.j₂.range_closedComplement _ ?_ ?_
  · exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map
      (D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map α)))
  · have := isIso_of_source_target_iso_zero (D+((i)^*[ModuleCat.{u + 1} Λ]).map α)
      hsource.isoZero htarget.isoZero
    exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map
      (D+((i)^*[ModuleCat.{u + 1} Λ]).map α)))

instance isIso_comparison : IsIso (D.comparison Λ) :=
  NatIso.isIso_of_isIso_app _

/-- The comparison isomorphism `α_u : j₂! ≅ Ru_* ∘ j₁!` on `D⁺(X_ét, Λ)`, for a finite
coefficient ring `Λ`. -/
noncomputable def comparisonIso :
    D+((D.j₂)_!open[ModuleCat.{u + 1} Λ]) ≅
      D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]) ⋙
        ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus :=
  asIso (D.comparison Λ)

@[simp]
lemma comparisonIso_hom : (D.comparisonIso Λ).hom = D.comparison Λ := rfl

end ProperOpenDatum

end AlgebraicGeometry

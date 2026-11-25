/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.ProperOpenSection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence

/-!
# The comparison map for a proper map fixing an open

Let `u : T₁ ⟶ T₂` be a proper morphism and `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂` open immersions with
`j₁ ≫ u = j₂` (`AlgebraicGeometry.ProperOpenDatum`). For a finite coefficient ring `Λ` this file
constructs the comparison map

`α_{u,K} : j₂! K ⟶ Ru_* j₁! K`

on the bounded below derived categories of étale sheaves of `Λ`-modules
(blueprint `proposition-construction-independence-rf-shriek--7`).

## The construction

For an open immersion `j` write `ι_j : j_! ⟶ Rj_*` for the canonical map of the adjoint triple
`j_! ⊣ j^* ⊣ Rj_*` (`AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStarPlus`). The map
`α_u` is characterised by

`Ru_* (ι_{j₁}) ∘ α_u = ι_{j₂}`   (modulo `Ru_* Rj₁_* ≅ Rj₂_*`)

(`AlgebraicGeometry.ProperOpenDatum.comparison_toLowerStar`). Such a map exists and is unique
because `j₂^* Ru_* (ι_{j₁})` is an isomorphism
(`AlgebraicGeometry.ProperOpenDatum.isIso_upperStar_map_toLowerStar_app`): by étale base change
along the open immersion `j₂` it is `Rp_*` of `b^* (ι_{j₁})`, and `b^* (ι_{j₁})` is an isomorphism
on `V = T₁ ×_{T₂} X`, being so on the clopen piece `s(X) = j₁(X)` (where `ι_{j₁}` restricts to an
isomorphism) and on its complement (where both sides vanish).

Correspondingly the restriction isomorphism `θ_u : j₂^* Ru_* j₁! K ≅ K` is `j₂^*` of
`Ru_* (ι_{j₁})`, followed by the counit `j₂^* Rj₂_* ≅ 𝟭`; `α_u` is adjoint to its inverse
(`AlgebraicGeometry.ProperOpenDatum.homEquiv_comparison_app`).

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStarPlus`: `ι_j : D⁺j_! ⟶ R⁺j_*`.
- `AlgebraicGeometry.ProperOpenDatum.toLowerStar`: `Ru_* (ι_{j₁})` followed by
  `Ru_* Rj₁_* ≅ Rj₂_*`.
- `AlgebraicGeometry.ProperOpenDatum.comparison`: the comparison map `α_u`.
- `AlgebraicGeometry.ProperOpenDatum.restrictionIso`: the isomorphism `θ_u`.

## Main statements

- `AlgebraicGeometry.ProperOpenDatum.isIso_upperStar_map_toLowerStar_app`
- `AlgebraicGeometry.ProperOpenDatum.comparison_toLowerStar` and
  `AlgebraicGeometry.ProperOpenDatum.comparison_ext`: the characterisation of `α_u`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

attribute [local instance] Etale.preservesInjectiveObjects_lowerStar

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace Etale

section Iota

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

/-- The canonical map `ι_j : D⁺j_! ⟶ R⁺j_*` for an open immersion `j`, attached to the adjoint
triple `D⁺j_! ⊣ D⁺j^* ⊣ R⁺j_*`: the unit of `D⁺j^* ⊣ R⁺j_*` at `j_! K` followed by `R⁺j_*` of
the inverse of the unit `K ≅ j^* j_! K` of `D⁺j_! ⊣ D⁺j^*`. -/
noncomputable def openImmersionLowerShriekToLowerStarPlus :
    D+((j)_!open[ModuleCat.{u + 1} Λ]) ⟶ ((j)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus :=
  Functor.whiskerLeft D+((j)_!open[ModuleCat.{u + 1} Λ])
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus.unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (inv (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat.{u + 1} Λ) j).unit)
      ((j)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ≫
    (Functor.leftUnitor _).hom

lemma openImmersionLowerShriekToLowerStarPlus_app
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriekToLowerStarPlus Λ j).app K =
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus.unit.app
          (D+((j)_!open[ModuleCat.{u + 1} Λ]).obj K) ≫
        ((j)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
            (ModuleCat.{u + 1} Λ) j).unit.app K)) := by
  simp [openImmersionLowerShriekToLowerStarPlus]

/-- The counit `D⁺j^* R⁺j_* ⟶ 𝟭` is an isomorphism for an open immersion `j`: in the adjoint
triple `D⁺j_! ⊣ D⁺j^* ⊣ R⁺j_*` the unit of the first adjunction is an isomorphism. -/
instance isIso_counit_derivedPlus_of_isOpenImmersion :
    IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus.counit :=
  (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus
    ).isIso_unit_iff_isIso_counit.1 inferInstance

/-- The transpose of `ι_j` under `D⁺j^* ⊣ R⁺j_*` is the inverse of the unit of `D⁺j_! ⊣ D⁺j^*`. -/
lemma upperStar_map_openImmersionLowerShriekToLowerStarPlus_app_counit
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((j)^*[ModuleCat.{u + 1} Λ]).map ((openImmersionLowerShriekToLowerStarPlus Λ j).app K) ≫
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus.counit.app K =
    inv ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j).unit.app K) := by
  let adj := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus
  have h := adj.counit.naturality (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j).unit.app K))
  simp only [Functor.comp_map, Functor.id_map] at h
  rw [openImmersionLowerShriekToLowerStarPlus_app, Functor.map_comp, assoc]
  erw [h]
  rw [← assoc]
  erw [adj.left_triangle_components]
  rw [id_comp]

/-- `j^*` of `ι_j` is an isomorphism. -/
instance isIso_upperStar_map_openImmersionLowerShriekToLowerStarPlus_app
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (D+((j)^*[ModuleCat.{u + 1} Λ]).map
      ((openImmersionLowerShriekToLowerStarPlus Λ j).app K)) := by
  have h := upperStar_map_openImmersionLowerShriekToLowerStarPlus_app_counit Λ j K
  have : IsIso (D+((j)^*[ModuleCat.{u + 1} Λ]).map
      ((openImmersionLowerShriekToLowerStarPlus Λ j).app K) ≫
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus.counit.app K) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).derivedPlus.counit.app K)

end Iota

/-- The bounded below derived category of étale sheaves on an empty scheme is zero. -/
lemma isZero_derivedCategoryPlus_of_isEmpty (E : Scheme.{u}) [IsEmpty E]
    (K : DerivedCategory.Plus (Sheaf E.smallEtaleTopology (ModuleCat.{u + 1} Λ))) : IsZero K :=
  IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι K
    (DerivedCategory.isZero_of_forall_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty ·) _)

end Etale

namespace ProperOpenDatum

variable {X : Scheme.{u}} (D : ProperOpenDatum X)

/-- The map `Ru_* (ι_{j₁}) : Ru_* j₁! ⟶ Ru_* Rj₁_*` followed by the composition isomorphism
`Ru_* Rj₁_* ≅ Rj₂_*`. -/
noncomputable def toLowerStar :
    D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]) ⋙ ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ⟶
      ((D.j₂)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus :=
  Functor.whiskerRight (openImmersionLowerShriekToLowerStarPlus Λ D.j₁)
      ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ≫
    (Functor.rightDerivedFunctorPlusCompIso' ((D.j₁)_*[ModuleCat.{u + 1} Λ])
      ((D.u)_*[ModuleCat.{u + 1} Λ])
      (Etale.lowerStarComp _ D.j₁ D.u D.j₂ D.comm.symm)).hom

lemma toLowerStar_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D.toLowerStar Λ).app K =
      ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
          ((openImmersionLowerShriekToLowerStarPlus Λ D.j₁).app K) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((D.j₁)_*[ModuleCat.{u + 1} Λ])
          ((D.u)_*[ModuleCat.{u + 1} Λ])
          (Etale.lowerStarComp _ D.j₁ D.u D.j₂ D.comm.symm)).hom.app K := rfl

/-- The open complement `V \ s(X)` of the clopen image of the section. -/
noncomputable def complementOpens : D.V.Opens :=
  ⟨(Set.range D.section.base)ᶜ, D.isClopen_range_section.isClosed.isOpen_compl⟩

lemma range_complementOpens_ι :
    Set.range D.complementOpens.ι.base = (Set.range D.section.base)ᶜ :=
  D.complementOpens.range_ι

/-- The complement `V \ s(X)` does not meet `j₁(X)` inside `T₁`. -/
lemma disjoint_range_complementOpens_ι_comp_b :
    Disjoint (Set.range (D.complementOpens.ι ≫ D.b).base) (Set.range D.j₁.base) := by
  rw [Set.disjoint_iff]
  rintro _ ⟨⟨w, rfl⟩, ⟨x, hx⟩⟩
  have hw : D.complementOpens.ι.base w ∈ (Set.range D.section.base)ᶜ := by
    rw [← D.range_complementOpens_ι]; exact Set.mem_range_self w
  apply hw
  refine ⟨x, D.b.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, D.section_b, hx, Scheme.Hom.comp_apply]

instance isEmpty_pullback_complementOpens :
    IsEmpty ↥(pullback D.j₁ (D.complementOpens.ι ≫ D.b) : Scheme.{u}) := by
  refine ⟨fun x ↦ ?_⟩
  have hx : (pullback.fst D.j₁ (D.complementOpens.ι ≫ D.b)).base x ∈
      D.j₁.base ⁻¹' Set.range (D.complementOpens.ι ≫ D.b).base := by
    rw [← Scheme.Pullback.range_fst]; exact Set.mem_range_self x
  exact Set.disjoint_iff.1 D.disjoint_range_complementOpens_ι_comp_b ⟨hx, ⟨_, rfl⟩⟩

/-- `b^*` of `ι_{j₁}` is an isomorphism on `V = T₁ ×_{T₂} X`. On the closed complement of the
open `W = V \ s(X)`, which lies inside the open `s(X)`, it is `j₁^*` of `ι_{j₁}`; on `W` both
sides vanish, `j₁! K` because `W` does not meet `j₁(X)`, and `Rj₁_* K` by étale base change, the
fibre product `X ×_{T₁} W` being empty. -/
instance isIso_upperStar_b_map_openImmersionLowerShriekToLowerStarPlus_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (D+((D.b)^*[ModuleCat.{u + 1} Λ]).map
      ((openImmersionLowerShriekToLowerStarPlus Λ D.j₁).app K)) := by
  set ψ := (openImmersionLowerShriekToLowerStarPlus Λ D.j₁).app K
  set W := D.complementOpens
  set i := W.ι.closedComplement
  have hi : Set.range i.base ⊆ Set.range D.section.base := by
    rw [Scheme.Hom.range_closedComplement, D.range_complementOpens_ι, compl_compl]
  set l := IsOpenImmersion.lift D.section i hi
  have hl : l ≫ D.section = i := IsOpenImmersion.lift_fac _ _ _
  suffices IsIso (DerivedCategory.Plus.ι.map (D+((D.b)^*[ModuleCat.{u + 1} Λ]).map ψ)) from
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  refine isIso_of_isIso_mapDerivedCategoryUpperStar_map _ W.ι i
    W.ι.range_closedComplement _ ?_ ?_
  · -- on `W`, source and target vanish
    have hs : IsZero (D+((W.ι)^*[ModuleCat.{u + 1} Λ]).obj (D+((D.b)^*[ModuleCat.{u + 1} Λ]).obj
        (D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]).obj K))) := by
      refine IsZero.of_iso ?_ ((Etale.upperStarCompDerivedPlus _ W.ι D.b).app _).symm
      exact IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι _
        (isZero_mapDerivedCategoryUpperStar_obj_openImmersionLowerShriek_of_disjoint_range _ D.j₁
          (W.ι ≫ D.b) D.disjoint_range_complementOpens_ι_comp_b (DerivedCategory.Plus.ι.obj K))
    have ht : IsZero (D+((W.ι)^*[ModuleCat.{u + 1} Λ]).obj (D+((D.b)^*[ModuleCat.{u + 1} Λ]).obj
        (((D.j₁)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K))) := by
      refine IsZero.of_iso ?_ ((Etale.upperStarCompDerivedPlus _ W.ι D.b).app _).symm
      let sq := IsPullback.of_hasPullback D.j₁ (W.ι ≫ D.b)
      have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
      exact IsZero.of_iso
        ((((pullback.snd D.j₁
          (W.ι ≫ D.b))_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus).map_isZero
          (isZero_derivedCategoryPlus_of_isEmpty Λ _ _))
        (asIso ((Etale.derivedBaseChangeMapPlus _ sq.toCommSq).app K))
    have := isIso_of_source_target_iso_zero (D+((W.ι)^*[ModuleCat.{u + 1} Λ]).map
      (D+((D.b)^*[ModuleCat.{u + 1} Λ]).map ψ)) hs.isoZero ht.isoZero
    exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map (D+((W.ι)^*[ModuleCat.{u + 1} Λ]).map
      (D+((D.b)^*[ModuleCat.{u + 1} Λ]).map ψ))))
  · -- on the closed complement of `W`, which lies in `s(X)`, it is `j₁^*` of `ι_{j₁}`
    have h₁ : IsIso (D+((D.section)^*[ModuleCat.{u + 1} Λ]).map
        (D+((D.b)^*[ModuleCat.{u + 1} Λ]).map ψ)) := by
      have := (NatIso.isIso_map_iff (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ)
        D.section D.b D.j₁ D.section_b.symm) ψ).1 inferInstance
      exact this
    have h₂ : IsIso (D+((i)^*[ModuleCat.{u + 1} Λ]).map
        (D+((D.b)^*[ModuleCat.{u + 1} Λ]).map ψ)) := by
      rw [NatIso.isIso_map_iff (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ)
        l D.section i hl.symm)]
      exact (inferInstance : IsIso (D+((l)^*[ModuleCat.{u + 1} Λ]).map
        (D+((D.section)^*[ModuleCat.{u + 1} Λ]).map (D+((D.b)^*[ModuleCat.{u + 1} Λ]).map ψ))))
    exact (inferInstance : IsIso (DerivedCategory.Plus.ι.map (D+((i)^*[ModuleCat.{u + 1} Λ]).map
      (D+((D.b)^*[ModuleCat.{u + 1} Λ]).map ψ))))

/-- **`j₂^*` of `Ru_* (ι_{j₁})` is an isomorphism.** By étale base change along the open
immersion `j₂` it is `Rp_*` of `b^* (ι_{j₁})`
(`isIso_upperStar_b_map_openImmersionLowerShriekToLowerStarPlus_app`). -/
instance isIso_upperStar_map_toLowerStar_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map ((D.toLowerStar Λ).app K)) := by
  rw [toLowerStar_app, Functor.map_comp]
  suffices IsIso (D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map
      (((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
        ((openImmersionLowerShriekToLowerStarPlus Λ D.j₁).app K))) from inferInstance
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ D.isPullback
  have h := (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) D.isPullback.toCommSq).naturality
    ((openImmersionLowerShriekToLowerStarPlus Λ D.j₁).app K)
  simp only [Functor.comp_map] at h
  have : IsIso (D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map
      (((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.map
        ((openImmersionLowerShriekToLowerStarPlus Λ D.j₁).app K)) ≫
      (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) D.isPullback.toCommSq).app _) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) D.isPullback.toCommSq).app _)

/-- The adjunction `D⁺j₂! ⊣ D⁺j₂^*`. -/
noncomputable abbrev adj₂ :=
  derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat.{u + 1} Λ) D.j₂

/-- Maps `j₂! K ⟶ Ru_* j₁! M` are determined by their composite with `Ru_* (ι_{j₁})`. -/
lemma comparison_ext
    {K M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ ψ : D+((D.j₂)_!open[ModuleCat.{u + 1} Λ]).obj K ⟶
      ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj
        (D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]).obj M))
    (h : φ ≫ (D.toLowerStar Λ).app M = ψ ≫ (D.toLowerStar Λ).app M) : φ = ψ := by
  apply ((D.adj₂ Λ).homEquiv _ _).injective
  rw [← cancel_mono (D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map ((D.toLowerStar Λ).app M)),
    ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right, h]

/-- The component of the comparison map `α_u` at `K`. -/
noncomputable def comparisonApp
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+((D.j₂)_!open[ModuleCat.{u + 1} Λ]).obj K ⟶
      ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj
        (D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]).obj K) :=
  ((D.adj₂ Λ).homEquiv _ _).symm
    ((D.adj₂ Λ).homEquiv _ _ ((openImmersionLowerShriekToLowerStarPlus Λ D.j₂).app K) ≫
      inv (D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map ((D.toLowerStar Λ).app K)))

@[reassoc]
lemma comparisonApp_toLowerStar
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D.comparisonApp Λ K ≫ (D.toLowerStar Λ).app K =
      (openImmersionLowerShriekToLowerStarPlus Λ D.j₂).app K := by
  apply ((D.adj₂ Λ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, comparisonApp, Equiv.apply_symm_apply, assoc,
    IsIso.inv_hom_id, comp_id]

/-- Blueprint `proposition-construction-independence-rf-shriek--7`: Comparison map for a proper map
fixing an open. For a proper `u : T₁ ⟶ T₂` and open immersions `j₁, j₂` with `j₁ ≫ u = j₂`, the map

`α_{u,K} : j₂! K ⟶ Ru_* j₁! K`

on `D⁺(X_ét, Λ)`. It is the adjoint, under `j₂! ⊣ j₂^*`, of the inverse of the restriction
isomorphism `θ_{u,K} : j₂^* Ru_* j₁! K ≅ K` (`homEquiv_comparison_app`), and it is characterised
by `Ru_* (ι_{j₁}) ∘ α_u = ι_{j₂}` (`comparison_toLowerStar`, `comparison_ext`). -/
noncomputable def comparison :
    D+((D.j₂)_!open[ModuleCat.{u + 1} Λ]) ⟶
      D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]) ⋙
        ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus where
  app := D.comparisonApp Λ
  naturality K L f := by
    apply D.comparison_ext Λ
    simp only [Functor.comp_map, assoc, comparisonApp_toLowerStar]
    have h₁ := (D.toLowerStar Λ).naturality f
    have h₂ := (openImmersionLowerShriekToLowerStarPlus Λ D.j₂).naturality f
    simp only [Functor.comp_map] at h₁
    rw [h₁, comparisonApp_toLowerStar_assoc, h₂]

/-- **The characterisation of `α_u`**: `Ru_* (ι_{j₁}) ∘ α_u = ι_{j₂}`, modulo the composition
isomorphism `Ru_* Rj₁_* ≅ Rj₂_*`. -/
@[reassoc]
lemma comparison_toLowerStar :
    D.comparison Λ ≫ D.toLowerStar Λ = openImmersionLowerShriekToLowerStarPlus Λ D.j₂ := by
  ext K : 2
  exact D.comparisonApp_toLowerStar Λ K

@[reassoc]
lemma comparison_app_toLowerStar_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D.comparison Λ).app K ≫ (D.toLowerStar Λ).app K =
      (openImmersionLowerShriekToLowerStarPlus Λ D.j₂).app K :=
  D.comparisonApp_toLowerStar Λ K

/-- `α_u` is the only natural transformation satisfying `comparison_toLowerStar`. -/
lemma eq_comparison (α : D+((D.j₂)_!open[ModuleCat.{u + 1} Λ]) ⟶
      D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]) ⋙
        ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus)
    (h : α ≫ D.toLowerStar Λ = openImmersionLowerShriekToLowerStarPlus Λ D.j₂) :
    α = D.comparison Λ := by
  ext K : 2
  apply D.comparison_ext Λ
  rw [comparison_app_toLowerStar_app]
  exact NatTrans.congr_app h K

/-- The restriction isomorphism `θ_{u,K} : j₂^* Ru_* j₁! K ≅ K`: `j₂^*` of
`Ru_* (ι_{j₁})` (modulo `Ru_* Rj₁_* ≅ Rj₂_*`), followed by the counit `j₂^* Rj₂_* K ≅ K`. -/
noncomputable def restrictionIso :
    D+((D.j₁)_!open[ModuleCat.{u + 1} Λ]) ⋙
        ((D.u)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus ⋙
          D+((D.j₂)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun K ↦ asIso (D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map ((D.toLowerStar Λ).app K)) ≪≫
      asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) D.j₂).derivedPlus.counit.app
        K))
    (by
      intro K L f
      have h₁ := (D.toLowerStar Λ).naturality f
      simp only [Functor.comp_map] at h₁
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Iso.trans_hom, asIso_hom,
        Functor.id_map, assoc]
      rw [← Functor.map_comp_assoc, h₁, Functor.map_comp, assoc]
      erw [(Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        D.j₂).derivedPlus.counit_naturality])

lemma restrictionIso_hom_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D.restrictionIso Λ).hom.app K =
      D+((D.j₂)^*[ModuleCat.{u + 1} Λ]).map ((D.toLowerStar Λ).app K) ≫
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) D.j₂).derivedPlus.counit.app K :=
  rfl

/-- `α_u` is the adjoint, under `D⁺j₂! ⊣ D⁺j₂^*`, of the inverse of `θ_u`. -/
theorem homEquiv_comparison_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D.adj₂ Λ).homEquiv _ _ ((D.comparison Λ).app K) = (D.restrictionIso Λ).inv.app K := by
  rw [← cancel_mono ((D.restrictionIso Λ).hom.app K), Iso.inv_hom_id_app, restrictionIso_hom_app,
    ← assoc, ← Adjunction.homEquiv_naturality_right, comparison_app_toLowerStar_app,
    Adjunction.homEquiv_unit, assoc,
    upperStar_map_openImmersionLowerShriekToLowerStarPlus_app_counit,
    IsIso.hom_inv_id]
  rfl

end ProperOpenDatum

end AlgebraicGeometry

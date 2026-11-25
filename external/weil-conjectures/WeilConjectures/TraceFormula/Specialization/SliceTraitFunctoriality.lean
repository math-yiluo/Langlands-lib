/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitPoint
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal

/-!

# Functoriality of slice traits along a change of trait

Let `ι : R₁ →+* R₂` be a local homomorphism of local rings, `κ₂` a field and `b₂ : R₂ →+* κ₂` a
ring map with kernel the maximal ideal of `R₂`. Then `b₂ ∘ ι` has kernel the maximal ideal of
`R₁`, and the geometric points `sliceTraitPoint (b₂.comp ι) : Spec K₂ ⟶ 𝔸¹_{R₁}` and
`sliceTraitPoint b₂ : Spec K₂ ⟶ 𝔸¹_{R₂}` (with `K₂ = κ₂(x)^alg`) are compatible with the map
`𝔸¹_{R₂} ⟶ 𝔸¹_{R₁}` induced by `ι`.

Since the strict henselization `𝒪^{sh}_{𝔸¹_{R₂}, s₂}` is strictly henselian, the universal property
of the strict localization gives a ring map
`sliceTraitMap ι b₂ : 𝒪^{sh}_{𝔸¹_{R₁}, s₁} →+* 𝒪^{sh}_{𝔸¹_{R₂}, s₂}`, compatible with the maps to
the bases, the evaluations at the geometric points and the structure maps from `R₁` and `R₂`. It
is a local homomorphism, and it is injective when `R₁` and `R₂` are discrete valuation rings and
`ι` is injective.

## Main results

- `AlgebraicGeometry.sliceTraitPoint_comp`: `sliceTraitPoint (b₂.comp ι)` factors through
  `sliceTraitPoint b₂`.
- `AlgebraicGeometry.sliceTraitMap` and its compatibilities
  `spec_sliceTraitMap_comp_strictLocalizationToBase`,
  `strictHenselizationEval_comp_sliceTraitMap`, `sliceTraitMap_comp_sliceTraitStructureMap`.
- `AlgebraicGeometry.isLocalHom_sliceTraitMap`, `AlgebraicGeometry.injective_sliceTraitMap`.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

open Scheme

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] (ι : R₁ →+* R₂)
  {κ₂ : Type u} [Field κ₂] (b₂ : R₂ →+* κ₂)

/-- The kernel of `b₂ ∘ ι` is the maximal ideal of `R₁` when `ker b₂` is the maximal ideal of `R₂`
and `ι` is local. -/
lemma ker_comp_eq_maximalIdeal [IsLocalRing R₁] [IsLocalRing R₂] [IsLocalHom ι]
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) :
    RingHom.ker (b₂.comp ι) = maximalIdeal R₁ := by
  rw [← RingHom.comap_ker, hb₂, IsLocalRing.maximalIdeal_comap]

/-- The morphism `𝔸¹_{R₂} ⟶ 𝔸¹_{R₁}` induced by `ι : R₁ →+* R₂`. -/
noncomputable abbrev affineLineMap :
    𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) :=
  AffineSpace.map _ (Spec.map (CommRingCat.ofHom ι))

/-- The morphism `𝔸¹_{R₂} ⟶ 𝔸¹_{R₁}` lies over `Spec R₂ ⟶ Spec R₁`. -/
lemma affineLineMap_over :
    affineLineMap ι ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) =
      𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) ≫ Spec.map (CommRingCat.ofHom ι) :=
  AffineSpace.map_over _

/-- The ring map of the geometric point `sliceTraitPoint (b₂.comp ι)` is that of
`sliceTraitPoint b₂` precomposed with `MvPolynomial.map ι`. -/
lemma sliceTraitPointRingHom_comp :
    sliceTraitPointRingHom (b₂.comp ι) =
      (sliceTraitPointRingHom b₂).comp (MvPolynomial.map (σ := ULift.{u} (Fin 1)) ι) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp [sliceTraitPointRingHom]
  · simp [sliceTraitPointRingHom]

/-- **Compatibility of the slice points with a change of trait**: `sliceTraitPoint (b₂.comp ι)`
is `sliceTraitPoint b₂` followed by `𝔸¹_{R₂} ⟶ 𝔸¹_{R₁}`. -/
lemma sliceTraitPoint_comp :
    sliceTraitPoint (b₂.comp ι) = sliceTraitPoint b₂ ≫ affineLineMap ι := by
  rw [sliceTraitPoint_eq, sliceTraitPoint_eq, affineLineMap, AffineSpace.map_SpecMap,
    Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, CommRingCat.hom_ofHom,
    ← CommRingCat.ofHom_comp, sliceTraitPointRingHom_comp]

/-- A morphism from the strict localization of `𝔸¹_{R₂}` at `sliceTraitPoint b₂` to the strict
localization of `𝔸¹_{R₁}` at `sliceTraitPoint (b₂.comp ι)` over `𝔸¹_{R₂} ⟶ 𝔸¹_{R₁}`, compatible
with the canonical geometric points; it exists since the source is strictly henselian. -/
lemma exists_sliceTrait_hom_strictLocalization :
    ∃ k : Spec (.of (strictHenselization (sliceTraitPoint b₂))) ⟶
        strictLocalization (sliceTraitPoint (b₂.comp ι)),
      k ≫ strictLocalizationToBase (sliceTraitPoint (b₂.comp ι)) =
          strictLocalizationToBase (sliceTraitPoint b₂) ≫ affineLineMap ι ∧
        Spec.map (strictHenselizationEval (sliceTraitPoint b₂)) ≫ k =
          Spec.map (strictHenselizationEval (sliceTraitPoint (b₂.comp ι))) :=
  have := isStrictlyHenselianLocalRing_strictHenselization' (sliceTraitPoint b₂)
  exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing _ _ _
    (spec_map_strictHenselizationEval_apply _ _) (by
      rw [← Category.assoc, spec_map_strictHenselizationEval_comp_strictLocalizationToBase,
        sliceTraitPoint_comp])

/-- The ring map `𝒪^{sh}_{𝔸¹_{R₁}, s₁} ⟶ 𝒪^{sh}_{𝔸¹_{R₂}, s₂}` between the strict henselizations at
the slice points, induced by `ι` through the universal property of the strict localization. -/
noncomputable def sliceTraitMap :
    strictHenselization (sliceTraitPoint (b₂.comp ι)) →+*
      strictHenselization (sliceTraitPoint b₂) :=
  (Spec.preimage (exists_sliceTrait_hom_strictLocalization ι b₂).choose).hom

/-- `sliceTraitMap` lies over the morphism `𝔸¹_{R₂} ⟶ 𝔸¹_{R₁}`. -/
lemma spec_sliceTraitMap_comp_strictLocalizationToBase :
    Spec.map (CommRingCat.ofHom (sliceTraitMap ι b₂)) ≫
        strictLocalizationToBase (sliceTraitPoint (b₂.comp ι)) =
      strictLocalizationToBase (sliceTraitPoint b₂) ≫ affineLineMap ι := by
  rw [sliceTraitMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  exact (exists_sliceTrait_hom_strictLocalization ι b₂).choose_spec.1

/-- `sliceTraitMap` is compatible with the evaluations at the geometric points. -/
lemma strictHenselizationEval_comp_sliceTraitMap :
    (strictHenselizationEval (sliceTraitPoint b₂)).hom.comp (sliceTraitMap ι b₂) =
      (strictHenselizationEval (sliceTraitPoint (b₂.comp ι))).hom := by
  have h := (exists_sliceTrait_hom_strictLocalization ι b₂).choose_spec.2
  rw [← Spec.map_preimage (exists_sliceTrait_hom_strictLocalization ι b₂).choose,
    ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- `sliceTraitMap` is compatible with the structure maps from `R₁` and `R₂`. -/
lemma sliceTraitMap_comp_sliceTraitStructureMap :
    (sliceTraitMap ι b₂).comp (sliceTraitStructureMap (b₂.comp ι)) =
      (sliceTraitStructureMap b₂).comp ι := by
  suffices CommRingCat.ofHom ((sliceTraitMap ι b₂).comp (sliceTraitStructureMap (b₂.comp ι))) =
      CommRingCat.ofHom ((sliceTraitStructureMap b₂).comp ι) from
    congrArg CommRingCat.Hom.hom this
  refine Spec.map_injective ?_
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    sliceTraitStructureMap, sliceTraitStructureMap, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom,
    Spec.map_preimage, Spec.map_preimage, ← Category.assoc,
    spec_sliceTraitMap_comp_strictLocalizationToBase, Category.assoc, affineLineMap_over,
    Category.assoc]

/-- `sliceTraitMap` is a local homomorphism, being compatible with the evaluations at the
geometric points, which are local. -/
instance isLocalHom_sliceTraitMap : IsLocalHom (sliceTraitMap ι b₂) := by
  have : IsLocalHom ((strictHenselizationEval (sliceTraitPoint b₂)).hom.comp
      (sliceTraitMap ι b₂)) := by
    rw [strictHenselizationEval_comp_sliceTraitMap]
    infer_instance
  exact isLocalHom_of_comp _ (strictHenselizationEval (sliceTraitPoint b₂)).hom

/-- **Injectivity of `sliceTraitMap`** for an injective local map of discrete valuation rings:
the kernel is a prime of the discrete valuation ring `𝒪^{sh}_{𝔸¹_{R₁}, s₁}`; were it the maximal
ideal, generated by a uniformizer `π` of `R₁`, the element `ι π ≠ 0` would vanish in
`𝒪^{sh}_{𝔸¹_{R₂}, s₂}`, contradicting the injectivity of `R₂ ⟶ 𝒪^{sh}_{𝔸¹_{R₂}, s₂}`. -/
theorem injective_sliceTraitMap [IsDomain R₁] [IsDiscreteValuationRing R₁] [IsDomain R₂]
    [IsDiscreteValuationRing R₂] [IsLocalHom ι] (hι : Function.Injective ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) : Function.Injective (sliceTraitMap ι b₂) := by
  have hb₁ := ker_comp_eq_maximalIdeal ι b₂ hb₂
  have := isDomain_strictHenselization_sliceTraitPoint _ hb₁
  have := isDiscreteValuationRing_strictHenselization_sliceTraitPoint _ hb₁
  have := isDomain_strictHenselization_sliceTraitPoint b₂ hb₂
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R₁
  have hker : RingHom.ker (sliceTraitMap ι b₂) ≠ maximalIdeal _ := by
    intro h
    have hm : sliceTraitStructureMap (b₂.comp ι) π ∈ maximalIdeal _ := by
      rw [maximalIdeal_strictHenselization_sliceTraitPoint _ hb₁]
      exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal π).2 hπ.not_isUnit)
    rw [← h, RingHom.mem_ker, ← RingHom.comp_apply, sliceTraitMap_comp_sliceTraitStructureMap,
      RingHom.comp_apply, ← map_zero (sliceTraitStructureMap b₂),
      (injective_sliceTraitStructureMap b₂ hb₂).eq_iff, ← map_zero ι, hι.eq_iff] at hm
    exact hπ.ne_zero hm
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have := RingHom.ker_isPrime (sliceTraitMap ι b₂)
  exact hker (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne))

end AlgebraicGeometry

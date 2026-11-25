/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationModelGeneric
public import WeilConjectures.TraceFormula.Specialization.TraitPowMap

/-!

# Morphisms of deformation models over the power map of the trait

Let `I`, `J` be ideal sheaves on a `k`-scheme `X`, and let `ν₀ : D_I X ⟶ D_J X` be a morphism of
deformation spaces over `X` lying over the power map `p : t ↦ t^m` of the affine line, for
instance the power map of `J = I^m`. Base changing along the power map `σ : S ⟶ S` of the trait
`S = Spec k'⟦t⟧` gives a morphism of total spaces `𝒟_I ⟶ 𝒟_J`
(`ProEtale.CondensedRing.deformationTotalPowMap`), and, through the automorphism of the
geometric generic point `Spec Ω` extending `σ`, a morphism of geometric generic fibres
(`ProEtale.CondensedRing.deformationGenericPowMap`), which is an isomorphism: both geometric
generic fibres are `X_Ω` (`ProEtale.CondensedRing.isIso_deformationGenericPowMap`).

The special fibre `t = 0` of `𝒟_J` pulls back to the thickened special fibre `t^m = 0` of `𝒟_I`.
We therefore consider the model `𝒲` of `X` with the total space and geometric generic fibre of
`𝒟_I` and with special fibre this pullback (`ProEtale.CondensedRing.powSourceModel`), and the
morphism of models `𝒲 ⟶ 𝒟_J` over the identity of `X`
(`ProEtale.CondensedRing.powModelHom`), whose square of special fibres is cartesian by
construction and whose square of identifications `ε` is cartesian
(`ProEtale.CondensedRing.isPullback_powModelHom_ε`). If `ν₀` is proper, so is its morphism of total
spaces (`ProEtale.CondensedRing.isProper_deformationTotalPowMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k' : Type u) [Field k'] {m : ℕ} (hm : m ≠ 0)

instance : IsFinite (traitPowMap k' m hm) :=
  (IsFinite.SpecMap_iff _).2 (PowerSeries.finite_expand m hm)

namespace ProEtale.CondensedRing

variable {k : Type u} [Field k] [Algebra k k'] (X : Over (Spec (.of k)))
  (I J : X.left.IdealSheafData) (ν₀ : I.deformationSpace ⟶ J.deformationSpace)
  (p : 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
  (hν₀ : ν₀ ≫ deformationSpaceToAffineLine X J = deformationSpaceToAffineLine X I ≫ p)
  (hσ : traitPowMap k' m hm ≫ traitToAffineLine k k' = traitToAffineLine k k' ≫ p)

/-- The morphism of total spaces `𝒟_I ⟶ 𝒟_J` induced by `ν₀` and the power map of the trait. -/
noncomputable def deformationTotalPowMap : deformationTotal X I k' ⟶ deformationTotal X J k' :=
  pullback.map _ _ _ _ ν₀ (traitPowMap k' m hm) p hν₀.symm hσ.symm

@[reassoc (attr := simp)]
lemma deformationTotalPowMap_toSpace :
    deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ ≫ deformationTotalToSpace X J k' =
      deformationTotalToSpace X I k' ≫ ν₀ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationTotalPowMap_toTrait :
    deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ ≫ deformationTotalToTrait X J k' =
      deformationTotalToTrait X I k' ≫ traitPowMap k' m hm :=
  pullback.lift_snd _ _ _

/-- The morphism of geometric generic fibres `𝒟_{I,Ω} ⟶ 𝒟_{J,Ω}` over the automorphism of
`Spec Ω` extending the power map of the trait. -/
noncomputable def deformationGenericPowMap :
    deformationGeneric X I k' ⟶ deformationGeneric X J k' :=
  pullback.map _ _ _ _ (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ)
    (traitGenericPointPowMap k' m hm) (traitPowMap k' m hm)
    (deformationTotalPowMap_toTrait k' hm X I J ν₀ p hν₀ hσ).symm
    (traitGenericPointPowMap_traitGenericPoint k' m hm).symm

@[reassoc (attr := simp)]
lemma deformationGenericPowMap_toTotal :
    deformationGenericPowMap k' hm X I J ν₀ p hν₀ hσ ≫ deformationGenericToTotal X J k' =
      deformationGenericToTotal X I k' ≫ deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma deformationGenericPowMap_toPoint :
    deformationGenericPowMap k' hm X I J ν₀ p hν₀ hσ ≫ deformationGenericToPoint X J k' =
      deformationGenericToPoint X I k' ≫ traitGenericPointPowMap k' m hm :=
  pullback.lift_snd _ _ _

variable (hproj : ν₀ ≫ J.deformationSpaceProj = I.deformationSpaceProj)

include hproj in
@[reassoc]
lemma deformationGenericPowMap_ε :
    deformationGenericPowMap k' hm X I J ν₀ p hν₀ hσ ≫ (deformationModel X J k').ε =
      (deformationModel X I k').ε := by
  rw [deformationModel_ε, deformationModel_ε, deformationGenericPowMap_toTotal_assoc,
    deformationTotalToBase, deformationTotalToBase, deformationTotalPowMap_toSpace_assoc, hproj]

include hproj in
/-- The morphism of geometric generic fibres is an isomorphism: both are the base change `X_Ω`
of `X` (`isPullback_deformationModel_ε`), and the morphism lies over the automorphism of
`Spec Ω`. -/
lemma isIso_deformationGenericPowMap :
    IsIso (deformationGenericPowMap k' hm X I J ν₀ p hν₀ hσ) := by
  have hI := isPullback_deformationModel_ε (k' := k') I
  have hJ := isPullback_deformationModel_ε (k' := k') J
  have hω : traitGenericPointPowMap k' m hm ≫ traitGenericPoint k' ≫ traitToBase k k' =
      traitGenericPoint k' ≫ traitToBase k k' := by
    rw [traitGenericPointPowMap_traitGenericPoint_assoc, traitPowMap_traitToBase]
  have hI' : IsPullback (deformationModel X I k').ε
      (deformationGenericToPoint X I k' ≫ traitGenericPointPowMap k' m hm) X.hom
      (traitGenericPoint k' ≫ traitToBase k k') := by
    refine hI.of_iso (Iso.refl _) (Iso.refl _) (asIso (traitGenericPointPowMap k' m hm))
      (Iso.refl _) (by simp) (by simp) (by simp) ?_
    simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
    exact hω.symm
  have : deformationGenericPowMap k' hm X I J ν₀ p hν₀ hσ = (hI'.isoIsPullback _ _ hJ).hom := by
    refine hJ.hom_ext ?_ ?_
    · exact (deformationGenericPowMap_ε k' hm X I J ν₀ p hν₀ hσ hproj).trans
        (IsPullback.isoIsPullback_hom_fst _ _ hI' hJ).symm
    · exact (deformationGenericPowMap_toPoint k' hm X I J ν₀ p hν₀ hσ).trans
        (IsPullback.isoIsPullback_hom_snd _ _ hI' hJ).symm
  rw [this]
  infer_instance

/-- The thickened special fibre `𝒟_I ×_{𝒟_J} 𝒟_{J,s}` (the locus `t^m = 0` of `𝒟_I`), as a
`k'`-scheme. -/
noncomputable def powSpecialFibre : Over (Spec (.of k')) :=
  Over.mk (pullback.fst (deformationModel X J k').i
    (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ) ≫
    (deformationSpecialFibre X J k').hom)

/-- The model `𝒲` of `X`: the total space and geometric generic fibre of `𝒟_I`, with the
thickened special fibre `𝒟_I ×_{𝒟_J} 𝒟_{J,s}`. -/
noncomputable def powSourceModel :
    NearbyCyclesModel X.left (powSpecialFibre k' hm X I J ν₀ p hν₀ hσ).left where
  total := deformationTotal X I k'
  generic := deformationGeneric X I k'
  j := deformationGenericToTotal X I k'
  i := pullback.snd (deformationModel X J k').i (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ)
  ε := (deformationModel X I k').ε

/-- The morphism of special fibres `𝒲_s ⟶ 𝒟_{J,s}`, over `k'`. -/
noncomputable def powSpecialFibreMap :
    powSpecialFibre k' hm X I J ν₀ p hν₀ hσ ⟶ deformationSpecialFibre X J k' :=
  Over.homMk (pullback.fst _ _) rfl

include hproj in
/-- The morphism of models `𝒲 ⟶ 𝒟_J` over the identity of `X`. -/
noncomputable def powModelHom :
    (powSourceModel k' hm X I J ν₀ p hν₀ hσ).Hom (deformationModel X J k') (𝟙 X.left)
      (powSpecialFibreMap k' hm X I J ν₀ p hν₀ hσ).left where
  total := deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ
  generic := deformationGenericPowMap k' hm X I J ν₀ p hν₀ hσ
  comm_j := deformationGenericPowMap_toTotal k' hm X I J ν₀ p hν₀ hσ
  comm_i := pullback.condition
  comm_ε := by
    rw [Category.comp_id]
    exact deformationGenericPowMap_ε k' hm X I J ν₀ p hν₀ hσ hproj

/-- The square of special fibres of `𝒲 ⟶ 𝒟_J` is cartesian. -/
lemma isPullback_powModelHom_i :
    IsPullback (powSourceModel k' hm X I J ν₀ p hν₀ hσ).i
      (powSpecialFibreMap k' hm X I J ν₀ p hν₀ hσ).left
      (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ) (deformationModel X J k').i :=
  (IsPullback.of_hasPullback _ _).flip

include hproj in
/-- The square of identifications `ε` of `𝒲 ⟶ 𝒟_J` is cartesian. -/
lemma isPullback_powModelHom_ε :
    IsPullback (powSourceModel k' hm X I J ν₀ p hν₀ hσ).ε
      (deformationGenericPowMap k' hm X I J ν₀ p hν₀ hσ) (𝟙 X.left)
      (deformationModel X J k').ε := by
  have := isIso_deformationGenericPowMap k' hm X I J ν₀ p hν₀ hσ hproj
  refine IsPullback.of_vert_isIso ⟨?_⟩
  rw [Category.comp_id]
  exact (deformationGenericPowMap_ε k' hm X I J ν₀ p hν₀ hσ hproj).symm

include hν₀ hσ in
/-- If `ν₀` is finite, so is the morphism of total spaces `𝒟_I ⟶ 𝒟_J`: it is the closed
immersion `𝒟_I ⟶ D_I X ×_{𝔸¹} S` (via `p`) followed by the base change of `ν₀ × σ`. -/
lemma isFinite_deformationTotalPowMap [IsFinite ν₀] [IsSeparated p] :
    IsFinite (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ) := by
  have e : deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ =
      pullback.mapDesc (deformationSpaceToAffineLine X I) (traitToAffineLine k k') p ≫
        pullback.map _ _ _ _ ν₀ (traitPowMap k' m hm) (𝟙 _)
          ((Category.comp_id _).trans hν₀.symm) ((Category.comp_id _).trans hσ.symm) := by
    refine pullback.hom_ext ?_ ?_ <;> simp [deformationTotalPowMap]
  rw [e]
  have := MorphismProperty.pullbackMap (P := @IsFinite) (f := deformationSpaceToAffineLine X I ≫ p)
    (g := traitToAffineLine k k' ≫ p) (i₁ := ν₀) (i₂ := traitPowMap k' m hm)
    (inferInstanceAs (IsFinite ν₀)) inferInstance hν₀.symm hσ.symm
  exact MorphismProperty.comp_mem _ _ _ inferInstance this

/-- The special fibre `𝒟_{I,s} ⟶ 𝒟_{J,s}` of the morphism of total spaces. -/
noncomputable def deformationSpecialFibrePowMap :
    (deformationSpecialFibre X I k').left ⟶ (deformationSpecialFibre X J k').left :=
  pullback.lift (deformationSpecialToTotal X I k' ≫ deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ)
    (deformationSpecialFibre X I k').hom (by
      rw [Category.assoc, deformationTotalPowMap_toTrait,
        reassoc_of% (isPullback_deformationSpecialFibre X I k').w, traitClosedPoint_traitPowMap])

/-- The inclusion `c : 𝒟_{I,s} ⟶ 𝒲_s` of the special fibre `t = 0` of `𝒟_I` into the thickened
special fibre `t^m = 0`. -/
noncomputable def specialFibreToPowSpecialFibre :
    (deformationSpecialFibre X I k').left ⟶ (powSpecialFibre k' hm X I J ν₀ p hν₀ hσ).left :=
  pullback.lift (deformationSpecialFibrePowMap k' hm X I J ν₀ p hν₀ hσ)
    (deformationSpecialToTotal X I k') (pullback.lift_fst _ _ _)

@[reassoc (attr := simp)]
lemma specialFibreToPowSpecialFibre_i :
    specialFibreToPowSpecialFibre k' hm X I J ν₀ p hν₀ hσ ≫
      (powSourceModel k' hm X I J ν₀ p hν₀ hσ).i = (deformationModel X I k').i :=
  pullback.lift_snd _ _ _

omit [Algebra k k'] in
lemma isClosedImmersion_traitClosedPoint : IsClosedImmersion (traitClosedPoint k') :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨PowerSeries.C a, by simp⟩

instance (Y : Over (Spec (.of k))) (K : Y.left.IdealSheafData) :
    IsClosedImmersion (deformationModel Y K k').i := by
  have := isClosedImmersion_traitClosedPoint k'
  exact inferInstanceAs (IsClosedImmersion (pullback.fst _ _))

instance : IsClosedImmersion (powSourceModel k' hm X I J ν₀ p hν₀ hσ).i :=
  inferInstanceAs (IsClosedImmersion (pullback.snd (deformationModel X J k').i _))

instance : IsClosedImmersion (specialFibreToPowSpecialFibre k' hm X I J ν₀ p hν₀ hσ) := by
  have : IsClosedImmersion (specialFibreToPowSpecialFibre k' hm X I J ν₀ p hν₀ hσ ≫
      (powSourceModel k' hm X I J ν₀ p hν₀ hσ).i) := by
    rw [specialFibreToPowSpecialFibre_i]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _
    (powSourceModel k' hm X I J ν₀ p hν₀ hσ).i

instance : Surjective (specialFibreToPowSpecialFibre k' hm X I J ν₀ p hν₀ hσ) := by
  refine ⟨fun w ↦ ?_⟩
  have e : pullback.snd (deformationModel X J k').i
      (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ) ≫
      deformationTotalToTrait X I k' ≫ traitPowMap k' m hm =
      pullback.fst (deformationModel X J k').i (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ) ≫
        (deformationSpecialFibre X J k').hom ≫ traitClosedPoint k' := by
    rw [← deformationTotalPowMap_toTrait k' hm X I J ν₀ p hν₀ hσ, ← Category.assoc,
      ← pullback.condition, Category.assoc,
      ← (isPullback_deformationSpecialFibre X J k').w]
    rfl
  set y := pullback.snd (deformationModel X J k').i
    (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ) w
  have hy : deformationTotalToTrait X I k' y ∈ Set.range (traitClosedPoint k') := by
    refine mem_range_traitClosedPoint_of_traitPowMap k' m hm _
      ⟨(deformationSpecialFibre X J k').hom (pullback.fst (deformationModel X J k').i
        (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ) w), ?_⟩
    have := congr($(e).base w)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    exact this.symm
  obtain ⟨s, hs⟩ := hy
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y s hs.symm
  refine ⟨z, (pullback.snd (deformationModel X J k').i
    (deformationTotalPowMap k' hm X I J ν₀ p hν₀ hσ)).isClosedEmbedding.injective ?_⟩
  change ((specialFibreToPowSpecialFibre k' hm X I J ν₀ p hν₀ hσ) ≫
    (powSourceModel k' hm X I J ν₀ p hν₀ hσ).i) z = y
  rw [specialFibreToPowSpecialFibre_i]
  exact hz

end ProEtale.CondensedRing

end AlgebraicGeometry

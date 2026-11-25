/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitExists
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitSepClosed

/-!

# The strict localization of `𝔸¹_S` has residue coefficients

Let `R` be the strict henselization of `𝔸¹_S` (`S = Spec k'⟦t⟧`) at the generic point of its
special fibre, with the local injection `ι : R ⟶ K⟦t⟧` through which the generic slice factors
(`AlgebraicGeometry.genericSliceRingHom`). Then `ι` takes values in `κ'⟦t⟧`, where `κ' ⊆ K` is the
image of the residue field of `R`
(`AlgebraicGeometry.hasResidueCoeffs_genericSliceTraitOfStrictLocalization`): `κ'⟦t⟧` is strictly
henselian and receives the generic slice `x ↦ x ∈ κ'`, so by the universal property of the strict
localization `ι` factors through `κ'⟦t⟧ ⊆ K⟦t⟧`.

Consequently the strict localization is a generic slice trait whose compositum is relatively
separably closed in that of `Spec K⟦t⟧`
(`AlgebraicGeometry.exists_genericSliceTrait_hasResidueCoeffs`).

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (k' : Type u) [Field k']

/-- The slice `R ⟶ K⟦t⟧` restricts to the generic slice `k'⟦t⟧[x] ⟶ K⟦t⟧` on the affine chart. -/
lemma genericSliceRingHom_comp_genericSliceChartRingHom
    [IsDomain (strictHenselization (genericSlicePoint k'))] :
    (genericSliceRingHom k').comp (genericSliceChartRingHom k') =
      traitSliceRingHom (traitSliceCoord k') := by
  have h : Spec.map (CommRingCat.ofHom ((genericSliceRingHom k').comp
      (genericSliceChartRingHom k'))) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).inv =
      traitSlice (traitSliceCoord k') := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, spec_genericSliceChartRingHom,
      spec_genericSliceRingHom]
  rw [traitSlice, cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

variable [IsSepClosed k']

attribute [local instance] isDomain_strictHenselization_genericSlicePoint

/-- The field `K = k'(x)^alg` of the generic slices. -/
local notation "𝕂" => traitSliceField k'

/-- **The strict localization of `𝔸¹_S` has residue coefficients**: the slice `R ⟶ K⟦t⟧` takes
values in `κ'⟦t⟧`, `κ' ⊆ K` the image of the residue field of `R`. -/
theorem hasResidueCoeffs_genericSliceTraitOfStrictLocalization :
    (genericSliceTraitOfStrictLocalization k').HasResidueCoeffs := by
  set D := genericSliceTraitOfStrictLocalization k'
  set κ := D.residueSubfield
  -- the coordinate `x` lies in `κ'`
  have hx : traitSliceCoord k' ∈ κ := by
    refine (D.mem_residueSubfield_iff _).2
      ⟨genericSliceChartRingHom k' (MvPolynomial.X ⟨0⟩), ?_⟩
    have h := RingHom.congr_fun (genericSliceRingHom_comp_genericSliceChartRingHom k')
      (MvPolynomial.X ⟨0⟩)
    rw [RingHom.comp_apply] at h
    refine (congrArg PowerSeries.constantCoeff h).trans ?_
    simp [traitSliceRingHom]
  let : Algebra k' κ := ((algebraMap k' 𝕂).codRestrict κ D.algebraMap_mem_residueSubfield).toAlgebra
  let xκ : κ := ⟨_, hx⟩
  -- the geometric point `Spec K ⟶ Spec κ'⟦t⟧` and the slice `Spec κ'⟦t⟧ ⟶ 𝔸¹_S`
  let p₀ : Spec (.of 𝕂) ⟶ Spec (.of (PowerSeries κ)) :=
    Spec.map (CommRingCat.ofHom ((algebraMap κ 𝕂).comp PowerSeries.constantCoeff))
  have hp₀ : p₀ (IsLocalRing.closedPoint 𝕂) = IsLocalRing.closedPoint (PowerSeries κ) :=
    IsLocalRing.comap_closedPoint ((algebraMap κ 𝕂).comp (PowerSeries.constantCoeff (R := κ)))
  have hring : ((algebraMap κ 𝕂).comp PowerSeries.constantCoeff).comp
      (traitSliceRingHom (k' := k') xκ) =
      PowerSeries.constantCoeff.comp (traitSliceRingHom (traitSliceCoord k')) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.comp_apply, traitSliceRingHom, MvPolynomial.eval₂Hom_C,
        constantCoeff_map_apply]
      rfl
    · simp only [RingHom.comp_apply, traitSliceRingHom, MvPolynomial.eval₂Hom_X',
        PowerSeries.constantCoeff_C]
      rfl
  have ha : p₀ ≫ traitSlice xκ = genericSlicePoint k' := by
    rw [genericSlicePoint, traitClosedPoint, traitSlice, traitSlice, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  obtain ⟨kk, hkk, hkk'⟩ := exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing
    (genericSlicePoint k') (traitSlice xκ) p₀ hp₀ ha
  -- the inclusion `κ'⟦t⟧ ⊆ K⟦t⟧`
  let m : Spec (.of (PowerSeries 𝕂)) ⟶ Spec (.of (PowerSeries κ)) :=
    Spec.map (CommRingCat.ofHom (PowerSeries.map (algebraMap κ 𝕂)))
  have hring' : (PowerSeries.map (algebraMap κ 𝕂)).comp (traitSliceRingHom (k' := k') xκ) =
      traitSliceRingHom (traitSliceCoord k') := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · ext n
      simp [traitSliceRingHom]
      rfl
    · simp [traitSliceRingHom, xκ]
      rfl
  have hm : m ≫ traitSlice (k' := k') xκ = traitSlice (traitSliceCoord k') := by
    rw [traitSlice, traitSlice, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hring']
  have hm' : traitClosedPoint 𝕂 ≫ m = p₀ := by
    rw [traitClosedPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have heq : (exists_genericSlice_hom_strictLocalization k').choose = m ≫ kk := by
    refine hom_strictLocalization_ext (genericSlicePoint k') ?_ (traitClosedPoint 𝕂)
      (IsLocalRing.closedPoint 𝕂) (traitClosedPoint_apply_closedPoint 𝕂) ?_
    · rw [(exists_genericSlice_hom_strictLocalization k').choose_spec.1, Category.assoc, hkk, hm]
    · rw [(exists_genericSlice_hom_strictLocalization k').choose_spec.2, reassoc_of% hm', hkk']
  have hι : D.ι = (PowerSeries.map (algebraMap κ 𝕂)).comp (Spec.preimage kk).hom := by
    have h : Spec.map (CommRingCat.ofHom (genericSliceRingHom k')) =
        Spec.map (Spec.preimage kk ≫ CommRingCat.ofHom (PowerSeries.map (algebraMap κ 𝕂))) := by
      rw [Spec.map_comp, Spec.map_preimage, genericSliceRingHom, CommRingCat.ofHom_hom,
        Spec.map_preimage, heq]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  intro r n
  have hmem : PowerSeries.coeff n (D.ι r) ∈ κ := by
    rw [hι, RingHom.comp_apply, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  obtain ⟨s, hs⟩ := (D.mem_residueSubfield_iff _).1 hmem
  exact ⟨s, hs.symm⟩



/-- **A generic slice trait with residue coefficients exists**: the strict localization of `𝔸¹_S`
at the generic point of its special fibre
(`AlgebraicGeometry.hasResidueCoeffs_genericSliceTraitOfStrictLocalization`). For such a generic
slice trait, the compositum `L'` is relatively separably closed in `L_T`
(`AlgebraicGeometry.GenericSliceTrait.compositumSepMap_mem_range_algebraMap`). -/
theorem exists_genericSliceTrait_hasResidueCoeffs :
    ∃ D : GenericSliceTrait k', D.HasResidueCoeffs :=
  ⟨_, hasResidueCoeffs_genericSliceTraitOfStrictLocalization k'⟩
end AlgebraicGeometry

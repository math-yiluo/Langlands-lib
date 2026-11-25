/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUnramified
public import WeilConjectures.TraceFormula.Specialization.HenselianTraitLaurentSepClosed
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisSepClosed
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUniversal
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!

# The fraction field of a generic slice trait is separably closed in `K((t))`

Let `D` be a generic slice trait of `𝔸¹_S`, `S = Spec k'⟦t⟧` with `k'` separably closed
(`AlgebraicGeometry.GenericSliceTrait`), with the local injection `ι : R ⟶ K⟦t⟧`,
`K = k'(x)^alg`. Write `κ' ⊆ K` for the image of the residue field of `R`
(`AlgebraicGeometry.GenericSliceTrait.residueSubfield`), a separably closed field. Assume that
`ι` takes values in `κ'⟦t⟧` (`AlgebraicGeometry.GenericSliceTrait.HasResidueCoeffs`; this holds
for the strict localization of `𝔸¹_S` at the generic point of its special fibre). Then
`F' = Frac R` is separably closed in `F_K = K((t))`
(`AlgebraicGeometry.GenericSliceTrait.mem_range_fractionRingMap_of_isSeparable`), SGA 4½,
[Th. finitude], 3.3:

* an element of `K((t))` separable over `F'` is separable over `κ'((t)) ⊇ F'`, hence lies in
  `κ'((t))` (`AlgebraicGeometry.mem_range_traitLaurentFieldMap_of_isSeparable`, `K` being
  algebraic over `κ'`);
* `F'` is separably closed in `κ'((t))` since `R` is a henselian discrete valuation ring with
  uniformizer `t` and residue field `κ'`
  (`IsDiscreteValuationRing.mem_range_fractionRingMap_of_isSeparable`).

-/

@[expose] public section

universe u

open IsLocalRing

namespace AlgebraicGeometry.GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

/-- **The slice has residue coefficients**: every coefficient of the power series `ι r`, `r ∈ R`,
is the constant coefficient of some `ι s`, i.e. `ι : R ⟶ K⟦t⟧` takes values in `κ'⟦t⟧` for the
image `κ' ⊆ K` of the residue field of `R`. -/
def HasResidueCoeffs : Prop :=
  ∀ (r : D.R) (n : ℕ), ∃ s : D.R,
    PowerSeries.coeff n (D.ι r) = PowerSeries.constantCoeff (D.ι s)

/-- The image `κ' ⊆ K` of the residue field of `R` under `R ⟶ K⟦t⟧ ⟶ K`. -/
noncomputable def residueSubfield : Subfield (traitSliceField k') :=
  (ResidueField.lift ((PowerSeries.constantCoeff (R := traitSliceField k')).comp D.ι)).fieldRange

/-- The elements of `κ'` are the constant coefficients of the power series `ι s`, `s ∈ R`. -/
lemma mem_residueSubfield_iff (c : traitSliceField k') :
    c ∈ D.residueSubfield ↔ ∃ s : D.R, PowerSeries.constantCoeff (D.ι s) = c := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨s, rfl⟩ := residue_surjective z
    exact ⟨s, (ResidueField.lift_residue_apply
      ((PowerSeries.constantCoeff (R := traitSliceField k')).comp D.ι) s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨residue D.R s, ResidueField.lift_residue_apply
      ((PowerSeries.constantCoeff (R := traitSliceField k')).comp D.ι) s⟩

/-- The residue field `κ'` is separably closed, `R` being strictly henselian. -/
instance isSepClosed_residueSubfield : IsSepClosed D.residueSubfield :=
  IsSepClosed.of_ringEquiv (RingHom.rangeRestrictFieldEquiv _)

/-- `κ'` contains `k'`. -/
lemma algebraMap_mem_residueSubfield (c : k') :
    algebraMap k' (traitSliceField k') c ∈ D.residueSubfield := by
  refine (D.mem_residueSubfield_iff _).2 ⟨D.φ (PowerSeries.C c), ?_⟩
  rw [← RingHom.comp_apply D.ι, D.ι_comp_φ, PowerSeries.map_C, PowerSeries.constantCoeff_C]

variable {D}

/-- The coefficients of `ι r` lie in `κ'` when the slice has residue coefficients. -/
lemma mem_range_map_ι (hD : D.HasResidueCoeffs) (r : D.R) :
    D.ι r ∈ (PowerSeries.map (algebraMap D.residueSubfield (traitSliceField k'))).range := by
  refine (PowerSeries.mem_range_map_iff _ _).2 fun n ↦ ?_
  obtain ⟨s, hs⟩ := hD r n
  exact ⟨⟨_, (D.mem_residueSubfield_iff _).2 ⟨s, hs.symm⟩⟩, rfl⟩

/-- The slice `R ⟶ κ'⟦t⟧` with coefficients in the residue field `κ'`, when the slice has residue
coefficients. -/
noncomputable def residueι (hD : D.HasResidueCoeffs) : D.R →+* PowerSeries D.residueSubfield :=
  (RingEquiv.ofLeftInverse (Function.leftInverse_invFun (PowerSeries.map_injective _
    (algebraMap D.residueSubfield (traitSliceField k')).injective))).symm.toRingHom.comp
    (D.ι.codRestrict _ (mem_range_map_ι hD))

/-- `ι` is the composite of `R ⟶ κ'⟦t⟧` and the inclusion `κ'⟦t⟧ ⊆ K⟦t⟧`. -/
lemma map_residueι (hD : D.HasResidueCoeffs) (r : D.R) :
    PowerSeries.map (algebraMap D.residueSubfield (traitSliceField k')) (residueι hD r) =
      D.ι r :=
  congrArg Subtype.val (RingEquiv.apply_symm_apply (RingEquiv.ofLeftInverse
    (Function.leftInverse_invFun (PowerSeries.map_injective _
      (algebraMap D.residueSubfield (traitSliceField k')).injective)))
    ⟨D.ι r, mem_range_map_ι hD r⟩)

/-- The slice `R ⟶ κ'⟦t⟧` is injective. -/
lemma injective_residueι (hD : D.HasResidueCoeffs) : Function.Injective (residueι hD) :=
  fun a b h ↦ D.injective_ι (by rw [← map_residueι hD a, ← map_residueι hD b, h])

/-- `K = k'(x)^alg` has transcendence degree `≤ 1` over the residue field `κ' ⊇ k'`. -/
lemma trdeg_residueSubfield_le_one :
    Algebra.trdeg D.residueSubfield (traitSliceField k') ≤ 1 := by
  let : Algebra k' D.residueSubfield := ((algebraMap k' (traitSliceField k')).codRestrict
    D.residueSubfield D.algebraMap_mem_residueSubfield).toAlgebra
  have : IsScalarTower k' D.residueSubfield (traitSliceField k') :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FaithfulSMul k' D.residueSubfield :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul D.residueSubfield (traitSliceField k') :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have h := trdeg_add_eq (R := k') (S := D.residueSubfield) (A := traitSliceField k')
  exact le_add_self.trans (h.trans_le (trdeg_traitSliceField_le_one k'))

/-- **The fraction field of a generic slice trait is separably closed in `K((t))`** (SGA 4½,
[Th. finitude], 3.3): if the slice has residue coefficients, every element of `Frac K⟦t⟧`
separable over `Frac R` lies in `Frac R`. -/
theorem mem_range_fractionRingMap_of_isSeparable [IsSepClosed k'] (hD : D.HasResidueCoeffs)
    (α : FractionRing (PowerSeries (traitSliceField k')))
    (hα : letI := (IsDiscreteValuationRing.fractionRingMap D.ι D.injective_ι).toAlgebra
      IsSeparable (FractionRing D.R) α) :
    α ∈ (IsDiscreteValuationRing.fractionRingMap D.ι D.injective_ι).range := by
  set j := IsDiscreteValuationRing.fractionRingMap D.ι D.injective_ι
  set j₁ := IsDiscreteValuationRing.fractionRingMap (residueι hD) (injective_residueι hD)
  set j₂ := traitLaurentFieldMap D.residueSubfield (traitSliceField k')
  have hj : j₂.comp j₁ = j := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors D.R) (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply, j, j₁, j₂]
    rw [IsDiscreteValuationRing.fractionRingMap_algebraMap, traitLaurentFieldMap_algebraMap,
      map_residueι, IsDiscreteValuationRing.fractionRingMap_algebraMap]
  let := j.toAlgebra
  let := j₁.toAlgebra
  let := j₂.toAlgebra
  have : IsScalarTower (FractionRing D.R) (FractionRing (PowerSeries D.residueSubfield))
      (FractionRing (PowerSeries (traitSliceField k'))) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (RingHom.congr_fun hj x).symm
  -- `α` lies in `κ'((t))`
  obtain ⟨β, rfl⟩ := mem_range_traitLaurentFieldMap_of_isSeparable
    D.trdeg_residueSubfield_le_one α (hα.tower_top _)
  have hβ : IsSeparable (FractionRing D.R) β := IsSeparable.of_algHom _
    (IsScalarTower.toAlgHom (FractionRing D.R) (FractionRing (PowerSeries D.residueSubfield))
      (FractionRing (PowerSeries (traitSliceField k')))) hα
  -- `Frac R` is separably closed in `κ'((t))`
  have hX : residueι hD (D.φ PowerSeries.X) = PowerSeries.X := by
    refine PowerSeries.map_injective _
      (algebraMap D.residueSubfield (traitSliceField k')).injective ?_
    rw [map_residueι, ← RingHom.comp_apply D.ι, D.ι_comp_φ, PowerSeries.map_X, PowerSeries.map_X]
  have hπ : Irreducible (D.φ PowerSeries.X) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, D.maximalIdeal_eq,
      PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton]
  obtain ⟨x, rfl⟩ := IsDiscreteValuationRing.mem_range_fractionRingMap_of_isSeparable
    (residueι hD) (injective_residueι hD) hπ (by rw [hX, PowerSeries.order_X])
    (fun c ↦ by
      obtain ⟨s, hs⟩ := (D.mem_residueSubfield_iff c).1 c.2
      refine ⟨s, Subtype.ext ?_⟩
      rw [← hs, ← map_residueι hD s, constantCoeff_map_apply]
      rfl) β hβ
  exact ⟨x, (RingHom.congr_fun hj x).symm⟩

end AlgebraicGeometry.GenericSliceTrait

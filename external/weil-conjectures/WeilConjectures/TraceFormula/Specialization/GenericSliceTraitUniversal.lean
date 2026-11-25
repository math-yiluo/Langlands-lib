/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSlicePoint
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction

/-!

# The generic slice factors through the strict localization

Let `S = Spec k'⟦t⟧`, `K = k'(x)^alg` and `s = genericSlicePoint k' : Spec K ⟶ 𝔸¹_S`. We show:

* the strict localization `𝔸¹_{S,(s)} ⟶ 𝔸¹_S` is weakly étale
  (`AlgebraicGeometry.weaklyEtale_strictLocalizationToBase_genericSlicePoint`), since its ring is
  ind-étale over the affine chart `k'⟦t⟧[x]`;
* since `K⟦t⟧` is strictly henselian, the generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` factors through the
  strict localization, via a local ring map `𝒪^{sh}_{𝔸¹_S,s} ⟶ K⟦t⟧`
  (`AlgebraicGeometry.genericSliceRingHom`) compatible with the evaluations at the closed points;
* this ring map is injective as soon as the strict henselization is a discrete valuation ring
  (`AlgebraicGeometry.injective_genericSliceRingHom`): its kernel is not the maximal ideal, as
  `t` lies in the maximal ideal but maps to `t ≠ 0`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (k' : Type u) [Field k']

/-- The ring map `k'⟦t⟧[x] ⟶ 𝒪^{sh}_{𝔸¹_S,s}` of the strict localization at the generic slice
point, read on the affine chart `𝔸¹_S ≅ Spec k'⟦t⟧[x]`. -/
noncomputable def genericSliceChartRingHom :
    MvPolynomial (ULift.{u} (Fin 1)) (PowerSeries k') →+*
      strictHenselization (genericSlicePoint k') :=
  (Spec.preimage (strictLocalizationToBase (genericSlicePoint k') ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).hom)).hom

/-- The strict localization at the generic slice point is given on the affine chart by
`genericSliceChartRingHom`. -/
lemma spec_genericSliceChartRingHom :
    Spec.map (CommRingCat.ofHom (genericSliceChartRingHom k')) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).inv =
      strictLocalizationToBase (genericSlicePoint k') := by
  rw [genericSliceChartRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The strict localization of `𝔸¹_S` at the generic slice point is weakly étale over `𝔸¹_S`:
its ring is ind-étale over the affine chart `k'⟦t⟧[x]`. -/
instance weaklyEtale_strictLocalizationToBase_genericSlicePoint :
    WeaklyEtale (strictLocalizationToBase (genericSlicePoint k')) := by
  rw [← spec_genericSliceChartRingHom]
  have hind := strictHenselization_indEtale_of_affine_chart (genericSlicePoint k')
    (.of (MvPolynomial (ULift.{u} (Fin 1)) (PowerSeries k')))
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).inv
    ((AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).inv.surjective _)
    (Iso.refl _) (genericSliceChartRingHom k') (by
      rw [spec_genericSliceChartRingHom, Iso.refl_hom, Category.id_comp])
  have : WeaklyEtale (Spec.map (CommRingCat.ofHom (genericSliceChartRingHom k'))) := by
    let := (genericSliceChartRingHom k').toAlgebra
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 hind)
  exact MorphismProperty.comp_mem _ _ _ this (MorphismProperty.of_isIso @WeaklyEtale _)

/-- The constant coefficient of power series is a local ring map. -/
instance _root_.PowerSeries.isLocalHom_constantCoeff (R : Type*) [CommRing R] :
    IsLocalHom (PowerSeries.constantCoeff (R := R)) :=
  ⟨fun _ h ↦ PowerSeries.isUnit_iff_constantCoeff.2 h⟩

/-- The closed point of `Spec K⟦t⟧` is the image of the point `Spec K`. -/
lemma traitClosedPoint_apply_closedPoint (K : Type u) [Field K] :
    traitClosedPoint K (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint (PowerSeries K) :=
  IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := K))

/-- A morphism `Spec K⟦t⟧ ⟶ 𝔸¹_{S,(s)}` over `𝔸¹_S`, extending the canonical geometric point:
it exists since `K⟦t⟧` is strictly henselian. -/
lemma exists_genericSlice_hom_strictLocalization :
    ∃ κ : Spec (.of (PowerSeries (traitSliceField k'))) ⟶
        strictLocalization (genericSlicePoint k'),
      κ ≫ strictLocalizationToBase (genericSlicePoint k') = traitSlice (traitSliceCoord k') ∧
        traitClosedPoint _ ≫ κ = Spec.map (strictHenselizationEval (genericSlicePoint k')) :=
  exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing _ _ _
    (traitClosedPoint_apply_closedPoint _) rfl

/-- The local ring map `𝒪^{sh}_{𝔸¹_S,s} ⟶ K⟦t⟧` through which the generic slice
`Spec K⟦t⟧ ⟶ 𝔸¹_S` factors. -/
noncomputable def genericSliceRingHom :
    strictHenselization (genericSlicePoint k') →+* PowerSeries (traitSliceField k') :=
  (Spec.preimage (exists_genericSlice_hom_strictLocalization k').choose).hom

/-- The generic slice factors through the strict localization via `genericSliceRingHom`. -/
lemma spec_genericSliceRingHom :
    Spec.map (CommRingCat.ofHom (genericSliceRingHom k')) ≫
      strictLocalizationToBase (genericSlicePoint k') = traitSlice (traitSliceCoord k') := by
  rw [genericSliceRingHom, CommRingCat.ofHom_hom, Spec.map_preimage]
  exact (exists_genericSlice_hom_strictLocalization k').choose_spec.1

/-- The ring map `genericSliceRingHom` is compatible with the evaluations at the closed points. -/
lemma constantCoeff_comp_genericSliceRingHom :
    PowerSeries.constantCoeff.comp (genericSliceRingHom k') =
      (strictHenselizationEval (genericSlicePoint k')).hom := by
  have h := (exists_genericSlice_hom_strictLocalization k').choose_spec.2
  unfold traitClosedPoint at h
  rw [← Spec.map_preimage (exists_genericSlice_hom_strictLocalization k').choose,
    ← Spec.map_comp] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- The ring map `genericSliceRingHom` is local. -/
instance isLocalHom_genericSliceRingHom : IsLocalHom (genericSliceRingHom k') := by
  have : IsLocalHom (PowerSeries.constantCoeff.comp (genericSliceRingHom k')) := by
    rw [constantCoeff_comp_genericSliceRingHom]
    infer_instance
  exact isLocalHom_of_comp _ PowerSeries.constantCoeff

/-- The ring map `genericSliceRingHom` is injective when the strict henselization is a discrete
valuation ring: its kernel is a prime ideal, and it is not the maximal ideal, since `t` lies in
the maximal ideal but maps to `t ≠ 0`. -/
theorem injective_genericSliceRingHom [IsDomain (strictHenselization (genericSlicePoint k'))]
    [IsDiscreteValuationRing (strictHenselization (genericSlicePoint k'))] :
    Function.Injective (genericSliceRingHom k') := by
  have hcomp : (genericSliceRingHom k').comp (genericSliceChartRingHom k') =
      traitSliceRingHom (traitSliceCoord k') := by
    have h : Spec.map (CommRingCat.ofHom ((genericSliceRingHom k').comp
        (genericSliceChartRingHom k'))) ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).inv =
        traitSlice (traitSliceCoord k') := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, spec_genericSliceChartRingHom,
        spec_genericSliceRingHom]
    rw [traitSlice, cancel_mono] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have hX : genericSliceRingHom k' (genericSliceChartRingHom k' (MvPolynomial.C PowerSeries.X)) =
      PowerSeries.X := by
    rw [← RingHom.comp_apply, hcomp]
    simp [traitSliceRingHom]
  have hker : RingHom.ker (genericSliceRingHom k') ≠ IsLocalRing.maximalIdeal _ := by
    intro h
    have hm : genericSliceChartRingHom k' (MvPolynomial.C PowerSeries.X) ∈
        IsLocalRing.maximalIdeal _ := by
      rw [maximalIdeal_strictHenselization, RingHom.mem_ker,
        ← constantCoeff_comp_genericSliceRingHom, RingHom.comp_apply, hX,
        PowerSeries.constantCoeff_X]
    rw [← h, RingHom.mem_ker, hX] at hm
    exact PowerSeries.X_ne_zero hm
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have := RingHom.ker_isPrime (genericSliceRingHom k')
  exact hker (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne))

end AlgebraicGeometry

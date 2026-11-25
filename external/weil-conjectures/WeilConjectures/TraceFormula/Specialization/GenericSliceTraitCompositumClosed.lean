/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitCompositumMap
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitSepClosed
public import Mathlib.FieldTheory.Extension

/-!

# The compositum of a generic slice trait is relatively separably closed

Let `D` be a generic slice trait of `𝔸¹_S`, `S = Spec k'⟦t⟧` with `k'` separably closed
(`AlgebraicGeometry.GenericSliceTrait`), `T = Spec K⟦t⟧` and, over the geometric generic point
`Ω` of `S`, the composita `L' = Ω(R) ⊆ Ω'` and `L_T = Ω(K⟦t⟧) ⊆ Ω_K` with the maps
`l : L' ⟶ L_T` and `ω : L'^sep ⟶ L_T^sep` induced by `ω_K : Ω' ⟶ Ω_K`
(`AlgebraicGeometry.GenericSliceTrait.compositumSepMap`). If the slice has residue coefficients
(`AlgebraicGeometry.GenericSliceTrait.HasResidueCoeffs`, true for the strict localization of
`𝔸¹_S`), then `L'` is relatively separably closed in `L_T`: an element of `L'^sep` whose image
under `ω` lies in `L_T` lies in `L'`
(`AlgebraicGeometry.GenericSliceTrait.compositumSepMap_mem_range_algebraMap`). This is the
hypothesis `hclosed` of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic`
for the change of trait `T ⟶ S'` (SGA 4½, [Th. finitude], proof of 3.7).

The proof: `Frac R` is separably closed in `K((t))`
(`AlgebraicGeometry.GenericSliceTrait.mem_range_fractionRingMap_of_isSeparable`), so every
automorphism of `Ω'` over `Frac R` lifts along `ω_K` to an endomorphism of `Ω_K` over `K((t))`
(`AlgHom.exists_comp_eq_of_forall_isSeparable_mem_range`), which fixes `L_T`. Hence an element as
above is fixed by `Aut(Ω'/L')`, so it is purely inseparable over `L'`, and it is separable.

-/

@[expose] public section

open IntermediateField

open scoped TensorProduct

/-- **Lifting automorphisms along a separably closed extension.** Let `P ⊆ Q` be fields with `P`
separably closed in `Q`, `M` an algebraic extension of `P`, `N` an algebraically closed algebraic
extension of `Q` and `ω : M ⟶ N` a `P`-embedding. Then every `P`-endomorphism `τ` of `M` is the
restriction along `ω` of a `Q`-endomorphism `σ` of `N`: on the separable closure `P^sep` of `P` in
`M`, `σ` is defined on the field `Q ⊗_P P^sep`
(`Algebra.TensorProduct.isField_of_isSeparable_of_forall_mem_range`) and extended to `N`; it
agrees with `τ` on `M`, which is purely inseparable over `P^sep`. -/
theorem AlgHom.exists_comp_eq_of_forall_isSeparable_mem_range {P Q M N : Type*} [Field P]
    [Field Q] [Field M] [Field N] [Algebra P Q] [Algebra P M] [Algebra Q N] [Algebra P N]
    [IsScalarTower P Q N] [Algebra.IsAlgebraic P M] [IsAlgClosed N] [Algebra.IsAlgebraic Q N]
    (hQ : ∀ c : Q, IsSeparable P c → c ∈ (algebraMap P Q).range) (ω : M →ₐ[P] N)
    (τ : M →ₐ[P] M) : ∃ σ : N →ₐ[Q] N, ∀ m, σ (ω m) = ω (τ m) := by
  let Ms := separableClosure P M
  have hT : IsField (Q ⊗[P] Ms) :=
    (Algebra.TensorProduct.comm P Q Ms).toMulEquiv.isField
      (Algebra.TensorProduct.isField_of_isSeparable_of_forall_mem_range hQ Ms)
  let : Field (Q ⊗[P] Ms) := hT.toField
  let Φ : Q ⊗[P] Ms →ₐ[Q] N :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q N) (ω.comp Ms.val)
  let Ψ : Q ⊗[P] Ms →ₐ[Q] N :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId Q N) ((ω.comp τ).comp Ms.val)
  let : Algebra (Q ⊗[P] Ms) N := Φ.toRingHom.toAlgebra
  have : IsScalarTower Q (Q ⊗[P] Ms) N := IsScalarTower.of_algebraMap_eq fun q ↦ (Φ.commutes q).symm
  obtain ⟨σ, hσ⟩ := IntermediateField.exists_algHom_of_splits' (F := Q) (E := N) (K := N)
    (L := Q ⊗[P] Ms) Ψ fun s ↦
      ⟨(Algebra.IsIntegral.isIntegral (R := Q) s).tower_top, IsAlgClosed.splits _⟩
  refine ⟨σ, fun m ↦ ?_⟩
  have hMs : (σ.toRingHom.comp ω.toRingHom).comp (algebraMap Ms M) =
      (ω.toRingHom.comp τ.toRingHom).comp (algebraMap Ms M) := by
    ext a
    have h₁ : algebraMap (Q ⊗[P] Ms) N (1 ⊗ₜ a) = ω a := by
      rw [RingHom.algebraMap_toAlgebra]
      simp [Φ]
    have h₂ : Ψ (1 ⊗ₜ a) = ω (τ a) := by simp [Ψ]
    have := congrArg (fun f ↦ f (1 ⊗ₜ a)) hσ
    simp only [AlgHom.domRestrict, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', h₁,
      h₂] at this
    simpa using this
  exact congrArg (fun f ↦ f m) (IsPurelyInseparable.injective_comp_algebraMap Ms M N hMs)

universe u

namespace AlgebraicGeometry.GenericSliceTrait

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {D : GenericSliceTrait k'}

/-- **Automorphisms of `Ω'` over `R` lift to `Ω_K` over `K((t))`.** If the slice has residue
coefficients, every endomorphism `τ` of `Ω'` fixing `R` is the restriction along
`ω_K : Ω' ⟶ Ω_K` of an endomorphism `σ` of `Ω_K` over `K((t))`: `Frac R` is separably closed in
`K((t))` (`AlgebraicGeometry.GenericSliceTrait.mem_range_fractionRingMap_of_isSeparable`). -/
theorem exists_algHom_ωK_eq [IsSepClosed k'] (hD : D.HasResidueCoeffs) (τ : D.Ω →+* D.Ω)
    (hτ : ∀ r, τ (D.a r) = D.a r) :
    ∃ σ : traitGenericField (traitSliceField k') →ₐ[FractionRing (PowerSeries (traitSliceField k'))]
      traitGenericField (traitSliceField k'), ∀ m, σ (D.ωK m) = D.ωK (τ m) := by
  set j := IsDiscreteValuationRing.fractionRingMap D.ι D.injective_ι
  let jM : FractionRing D.R →+* D.Ω := IsFractionRing.lift D.injective_a
  let : Algebra (FractionRing D.R) (FractionRing (PowerSeries (traitSliceField k'))) :=
    j.toAlgebra
  let : Algebra (FractionRing D.R) D.Ω := jM.toAlgebra
  have : IsScalarTower (FractionRing D.R) (FractionRing (PowerSeries (traitSliceField k')))
      (traitGenericField (traitSliceField k')) := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsAlgebraic (FractionRing D.R) D.Ω := by
    let := D.a.toAlgebra
    have := D.isAlgebraic_a
    have : IsScalarTower D.R (FractionRing D.R) D.Ω :=
      .of_algebraMap_eq fun r ↦ (IsFractionRing.lift_algebraMap D.injective_a r).symm
    exact ⟨fun x ↦ (Algebra.IsAlgebraic.isAlgebraic (R := D.R) x).extendScalars
      (IsFractionRing.injective _ _)⟩
  have hjM : D.ωK.comp jM = (algebraMap (FractionRing (PowerSeries (traitSliceField k')))
      (traitGenericField (traitSliceField k'))).comp j := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors D.R) (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply, jM, j, IsFractionRing.lift_algebraMap,
      IsDiscreteValuationRing.fractionRingMap_algebraMap]
    rw [← IsScalarTower.algebraMap_apply]
    exact RingHom.congr_fun D.ωK_comp_a r
  have hω (p : FractionRing D.R) :
      D.ωK (jM p) = algebraMap _ (traitGenericField (traitSliceField k')) p :=
    (RingHom.congr_fun hjM p).trans (IsScalarTower.algebraMap_apply _
      (FractionRing (PowerSeries (traitSliceField k'))) _ p).symm
  let ω : D.Ω →ₐ[FractionRing D.R] traitGenericField (traitSliceField k') :=
    { D.ωK with commutes' := hω }
  have hτP : τ.comp jM = jM :=
    IsLocalization.ringHom_ext (nonZeroDivisors D.R) (RingHom.ext fun r ↦ by
      simp only [RingHom.comp_apply, jM, IsFractionRing.lift_algebraMap]
      exact hτ r)
  let τ' : D.Ω →ₐ[FractionRing D.R] D.Ω := { τ with commutes' := fun p ↦ RingHom.congr_fun hτP p }
  exact AlgHom.exists_comp_eq_of_forall_isSeparable_mem_range
    (fun c hc ↦ mem_range_fractionRingMap_of_isSeparable hD c hc) ω τ'

/-- `ω_K` maps the compositum `L' = Ω(R)` onto a subfield fixed by the lifts of the automorphisms
of `Ω'` over `L'`: an endomorphism `σ` of `Ω_K` over `K((t))` compatible along `ω_K` with an
automorphism of `Ω'` over `L'` fixes `L_T = Ω(K⟦t⟧)`. -/
lemma algHom_apply_eq_of_mem_compositum
    (τ : D.toSliceTrait.Ω ≃ₐ[D.toSliceTrait.compositum] D.toSliceTrait.Ω)
    (σ : traitGenericField (traitSliceField k') →ₐ[FractionRing (PowerSeries (traitSliceField k'))]
      traitGenericField (traitSliceField k'))
    (hσ : ∀ m, σ (D.sliceωK m) = D.sliceωK (τ m)) (z : traitGenericField (traitSliceField k'))
    (hz : z ∈ traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
      (traitGenericField (traitSliceField k'))) : σ z = z := by
  have hle : (traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
      (traitGenericField (traitSliceField k'))).toSubfield ≤
        RingHom.eqLocusField σ.toRingHom (RingHom.id _) := by
    rw [traitTensorCompositum, adjoin_toSubfield]
    refine Subfield.closure_le.mpr ?_
    rintro _ (⟨w, rfl⟩ | ⟨f, rfl⟩)
    · have hτw : τ (D.toSliceTrait.ωS w) = D.toSliceTrait.ωS w :=
        τ.commutes ⟨D.toSliceTrait.ωS w, IntermediateField.algebraMap_mem _ w⟩
      have h := hσ (D.toSliceTrait.ωS w)
      rw [hτw, ← RingHom.comp_apply, D.sliceωK_comp_ωS] at h
      exact h
    · have h := σ.commutes (algebraMap (PowerSeries (traitSliceField k'))
        (FractionRing (PowerSeries (traitSliceField k'))) f)
      rw [← IsScalarTower.algebraMap_apply] at h
      exact h
  exact hle hz

/-- **The compositum of a generic slice trait is relatively separably closed in that of the
trait `T = Spec K⟦t⟧`** (SGA 4½, [Th. finitude], proof of 3.7): if the slice has residue
coefficients, an element of `L'^sep` whose image under `ω : L'^sep ⟶ L_T^sep` lies in `L_T` lies
in `L'`. Every automorphism of `Ω'` over `L'` lifts along `ω_K` to an endomorphism of `Ω_K` over
`K((t))` (`AlgebraicGeometry.GenericSliceTrait.exists_algHom_ωK_eq`), which fixes `L_T`; so such
an element is fixed by `Aut(Ω'/L')`, hence purely inseparable and separable over `L'`. -/
theorem compositumSepMap_mem_range_algebraMap [IsSepClosed k'] (hD : D.HasResidueCoeffs) :
    ∀ x, D.compositumSepMap x ∈ Set.range (algebraMap
        (traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')))
        (traitTensorCompositumSep (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')))) →
      x ∈ Set.range (algebraMap D.toSliceTrait.compositum D.toSliceTrait.compositumSep) := by
  rintro x ⟨y, hy⟩
  have hxy : D.sliceωK x = y := congrArg Subtype.val hy.symm
  have hfix (τ : D.toSliceTrait.Ω ≃ₐ[D.toSliceTrait.compositum] D.toSliceTrait.Ω) :
      τ x = x := by
    obtain ⟨σ, hσ⟩ := exists_algHom_ωK_eq hD τ.toRingHom fun r ↦
      τ.commutes ⟨D.a r, subset_adjoin _ _ ⟨r, rfl⟩⟩
    have hσ' (m : D.toSliceTrait.Ω) : σ (D.sliceωK m) = D.sliceωK (τ m) := hσ m
    apply D.sliceωK.injective
    rw [← hσ', hxy, algHom_apply_eq_of_mem_compositum τ σ hσ' y y.2]
  let := D.toSliceTrait.a.toAlgebra
  have : FaithfulSMul D.toSliceTrait.R D.toSliceTrait.Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  have : Algebra.IsAlgebraic D.toSliceTrait.R D.toSliceTrait.Ω := D.isAlgebraic_a
  have : IsAlgClosure D.toSliceTrait.compositum D.toSliceTrait.Ω := ⟨inferInstance, inferInstance⟩
  let z : fixedField (⊤ : Subgroup Gal(D.toSliceTrait.Ω/D.toSliceTrait.compositum)) :=
    ⟨x, fun τ ↦ hfix τ⟩
  have hz : IsSeparable D.toSliceTrait.compositum z := by
    unfold IsSeparable
    rw [minpoly_eq]
    exact mem_separableClosure_iff.1 x.2
  obtain ⟨c, hc⟩ := (Normal.isPurelyInseparable_fixedField (F := D.toSliceTrait.compositum)
    (E := D.toSliceTrait.Ω)).inseparable _ z hz
  exact ⟨c, Subtype.ext (congrArg (fun w : fixedField _ ↦ (w : D.toSliceTrait.Ω)) hc)⟩

end AlgebraicGeometry.GenericSliceTrait

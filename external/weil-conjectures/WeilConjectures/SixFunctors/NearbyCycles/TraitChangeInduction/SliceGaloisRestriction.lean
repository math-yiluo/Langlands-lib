/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.FieldTheory.GaloisRestriction
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceStability

/-!

# The wild inertia of the slice over a change of trait surjects

Let `ι : R₁ ⟶ R₂` be a local injection of strictly henselian discrete valuation rings,
with algebraic geometric generic points `Ωᵢ`, and let `S₂(x) ⟶ S₁(x)` be the morphism of the
strict localizations of `𝔸¹` at the generic points of the special fibres
(`AlgebraicGeometry.sliceTraitOfStrictLocalizationHom`), with composita `Lᵢ = Ωᵢ(Sᵢ(x))`. Then
`L₁` is relatively separably closed in `L₂`
(`AlgebraicGeometry.sliceTraitOfStrictLocalizationHom_mem_compositum`), so that the restriction
`Gal(L₂^sep/L₂) ⟶ Gal(L₁^sep/L₁)` of the wild inertia groups `Pᵢ` of the slices has dense image
(by `AlgEquiv.exists_restrictNormalHomAlong_eq` and
`AlgebraicGeometry.sliceTraitOfStrictLocalizationHom_mem_range_algebraMap`). This is the
surjectivity `P₂ ↠ P₁` used in Deligne's proof of SGA 4½, [Th. finitude], Prop. 3.7, to compare
the invariant summands of the nearby cycles of the two slices.

With the Gauss valuation, `Lᵢ` is the inertia field of `Ωᵢ(x)`; an extension of `L₁` of degree
`p` inside `L₂` would be immediate (residue fields and value groups agree), and it is excluded by
the defectlessness of `L₁`, the stability theorem of Ohm and Kuhlmann in the residue-transcendental
case (F.-V. Kuhlmann, *Elimination of ramification I: the generalized stability theorem*,
Trans. AMS 362 (2010), §4), proved in `SliceTrait.Hom.mem_compositum_of_ΩMap_mem`.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing IntermediateField

namespace AlgebraicGeometry

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] (ι : R₁ →+* R₂) [IsLocalHom ι] (hι : Function.Injective ι)
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] (c : Ω₁ →+* Ω₂) {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂}
  (ha₁ : Function.Injective a₁) (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  (ha₂ : Function.Injective a₂) (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂)
  (hc : c.comp a₁ = a₂.comp ι)
  {κ : Type u} [Field κ] {b₂ : R₂ →+* κ} (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)

include hι ha₁ halg₁ ha₂ halg₂ hc hb₂ in
/-- **The compositum of the slice over `S₁` is relatively separably closed in that of the slice
over `S₂`** (SGA 4½, [Th. finitude], proof of 3.7): for a change of trait, an element
of `Ω'₁` separable over `L₁ = Ω₁(S₁(x))` whose image lies in `L₂ = Ω₂(S₂(x))` lies in `L₁`. -/
theorem sliceTraitOfStrictLocalizationHom_mem_compositum [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [IsSepClosed κ] :
    letI := a₁.toAlgebra
    letI := a₂.toAlgebra
    ∀ x : (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
        (ker_comp_eq_maximalIdeal ι b₂ hb₂)).compositumSep,
      (sliceTraitOfStrictLocalizationHom ι hι c ha₁ halg₁ ha₂ halg₂ hc hb₂).ΩMap x ∈
        (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).compositum →
      (x : (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
        (ker_comp_eq_maximalIdeal ι b₂ hb₂)).Ω) ∈
        (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).compositum :=
  letI := a₁.toAlgebra
  letI := a₂.toAlgebra
  fun x hx ↦ SliceTrait.Hom.mem_compositum_of_ΩMap_mem ha₁ halg₁ ha₂ halg₂
    (ker_comp_eq_maximalIdeal ι b₂ hb₂) hb₂
    (sliceTraitOfStrictLocalizationHom ι hι c ha₁ halg₁ ha₂ halg₂ hc hb₂) (fun _ ↦ rfl)
    (mem_separableClosure_iff.1 x.2) hx

include hι ha₁ halg₁ ha₂ halg₂ hc hb₂ in
/-- The relative separable closedness of `L₁` in `L₂`, in the form used for the restriction of
Galois groups (`AlgEquiv.exists_restrictNormalHomAlong_eq`): an element of `L₁^sep` whose image
under `ω : L₁^sep ⟶ L₂^sep` lies in `L₂` lies in `L₁`. -/
theorem sliceTraitOfStrictLocalizationHom_mem_range_algebraMap [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [IsSepClosed κ] :
    letI := a₁.toAlgebra
    letI := a₂.toAlgebra
    ∀ x, (sliceTraitOfStrictLocalizationHom ι hι c ha₁ halg₁ ha₂ halg₂ hc hb₂).compositumSepMap x ∈
        Set.range (algebraMap
          (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).compositum
          (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).compositumSep) →
      x ∈ Set.range (algebraMap
        (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).compositum
        (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).compositumSep) := by
  let := a₁.toAlgebra
  let := a₂.toAlgebra
  rintro x ⟨y, hy⟩
  have hmem := sliceTraitOfStrictLocalizationHom_mem_compositum ι hι c ha₁ halg₁ ha₂ halg₂ hc hb₂
    x (by
      rw [← SliceTrait.Hom.coe_compositumSepMap, ← hy]
      exact y.2)
  exact ⟨⟨x, hmem⟩, Subtype.ext rfl⟩

end AlgebraicGeometry

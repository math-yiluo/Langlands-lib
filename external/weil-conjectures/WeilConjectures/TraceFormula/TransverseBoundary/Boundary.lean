/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictionGenerization
public import WeilConjectures.TraceFormula.TransverseBoundary.CornerVanishing
public import WeilConjectures.TraceFormula.TransverseBoundary.TameLocalConstancy

/-!
# The transverse boundary calculation

Let `Z` be a regular smooth surface over an algebraically closed field `k`, or an étale limit
with affine transition maps of such surfaces, and `X, Y` regular divisors meeting transversely
at exactly one point `z` (`AlgebraicGeometry.Scheme.TransverseCorner`), with
`j : Z - Y ⟶ Z` and `i : Z - (X ∪ Y) ⟶ Z - Y`. Let `ℓ` be a prime invertible in `k`, `Λ` a
finite commutative `ℓ`-primary ring and `E` a bounded complex of `Λ`-modules on `Z - (X ∪ Y)`
with finite locally constant cohomology whose monodromy factors through a finite `ℓ`-group. Put
`M = Rj_* i_! E`. Then `M_z = 0`, `M|_{Y - z}` has finite locally constant cohomology, and if `Y`
is connected, then for every geometric point `s̄` of `Y - z` the restriction map
`RΓ(Y, M|_Y) ⟶ M_s̄` is zero in `D(Λ)` (blueprint `lemma-cohomology-near-two-transverse-divisors`).

The first two assertions are `lemma-cohomology-near-two-transverse-divisors--1` and
`lemma-cohomology-near-two-transverse-divisors--1`. The last one is the generization square
(`AlgebraicGeometry.Etale.derivedGlobalSectionsRestriction_eq_zero_of_isZero_of_isLocallyConstant`):
the restriction to `s̄` followed by the specialization isomorphism `M_s̄ ≅ M_η̄` to a geometric
generic point of `Y` factors through `M_z = 0`. Forgetting the `Λ`-action only serves to detect
the zero object `M_z`; the vanishing of the morphism is proved in `D(Λ)`.

## Main statements

- `TransverseCorner.derivedGlobalSectionsRestriction_boundaryComplex_eq_zero`:
  the restriction map `RΓ(Y, M|_Y) ⟶ M_s̄` vanishes.
- `AlgebraicGeometry.Scheme.TransverseCorner.transverse_boundary`: the three assertions of the
  transverse boundary calculation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.TransverseCorner

variable {k : Type u} [Field k] [IsAlgClosed k] (C : TransverseCorner k) {ℓ : ℕ} [Fact ℓ.Prime]
  (hℓ : (ℓ : k) ≠ 0) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)

include hℓ hΛ in
/-- Blueprint `lemma-cohomology-near-two-transverse-divisors`, last assertion: if `Y` is connected,
then for every geometric point `s̄` of `Y - z` the restriction map `RΓ(Y, M|_Y) ⟶ M_s̄` is zero in
`D(Λ)`, where `M = Rj_* i_! E`. -/
theorem derivedGlobalSectionsRestriction_boundaryComplex_eq_zero [ConnectedSpace C.Y]
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (sbar : Spec (.of Ω) ⟶ C.Y) (hs : C.z ∉ Set.range (sbar ≫ C.iY)) :
    Etale.derivedGlobalSectionsRestriction Λ sbar
      ((L((C.iY)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E)) = 0 := by
  have hz : C.z ∈ Set.range C.iX ∩ Set.range C.iY := C.range_inter ▸ rfl
  obtain ⟨zY, hzY⟩ := hz.2
  have hpre : C.iY ⁻¹' {C.z} = {zY} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ C.iY.isClosedEmbedding.injective (h.trans hzY.symm), fun h ↦ h ▸ hzY⟩
  have hzYc : IsClosed ({zY} : Set C.Y) := hpre ▸ C.isClosed_singleton_z.preimage C.iY.continuous
  have : IsLocallyNoetherian C.Y := LocallyOfFiniteType.isLocallyNoetherian C.iY
  have : IrreducibleSpace C.Y := IsRegular.irreducibleSpace C.Y
  have hO : C.puncturedY = ⟨({zY} : Set C.Y)ᶜ, hzYc.isOpen_compl⟩ := by
    ext1
    exact congrArg compl hpre
  refine Etale.derivedGlobalSectionsRestriction_eq_zero_of_isZero_of_isLocallyConstant Λ zY hzYc _
    ?_ ?_ sbar ?_
  · intro Ω _ _ zbar hz
    refine (C.isZero_leftDerivedUpperStar_boundaryComplex hℓ Λ hΛ E hE (zbar ≫ C.iY) ?_).of_iso
      ((Etale.leftDerivedUpperStarComp _ zbar C.iY).app _).symm
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hz, Set.image_singleton, hzY]
  · intro n
    have := C.isFiniteLocallyConstantSheaf_homology_boundaryComplex hℓ Λ hΛ E hE n
    rw [hO] at this
    exact IsLocallyConstantSheaf.of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
      ((Etale.leftDerivedUpperStarComp _ _ C.iY).app _))
  · rintro ⟨x, rfl⟩
    exact hs ⟨x, by rw [Scheme.Hom.comp_apply, hzY]⟩

include hℓ hΛ in
/-- Blueprint `lemma-cohomology-near-two-transverse-divisors`: Transverse boundary calculation. For
a bounded complex `E` on `Z - (X ∪ Y)` with finite locally constant cohomology whose monodromy
factors through a finite `ℓ`-group, `M = Rj_* i_! E` satisfies:

1. `M_z̄ = 0` at every geometric point `z̄` over the corner point;
2. `M|_{Y - z}` has finite locally constant cohomology sheaves;
3. if `Y` is connected, the restriction map `RΓ(Y, M|_Y) ⟶ M_s̄` is zero in `D(Λ)` for every
   geometric point `s̄` of `Y - z`. -/
theorem transverse_boundary
    (E : DerivedCategory (Sheaf C.V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hE : Etale.IsBoundedFiniteEllGroupMonodromy ℓ E) :
    (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (zbar : Spec (.of Ω) ⟶ C.Z),
      Set.range zbar = {C.z} →
        IsZero ((L((zbar)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E))) ∧
    (∀ n : ℤ, IsFiniteLocallyConstantSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((L((C.puncturedY.ι ≫ C.iY)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E)))) ∧
    (ConnectedSpace C.Y → ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (sbar : Spec (.of Ω) ⟶ C.Y), C.z ∉ Set.range (sbar ≫ C.iY) →
        Etale.derivedGlobalSectionsRestriction Λ sbar
          ((L((C.iY)^*[ModuleCat.{u + 1} Λ])).obj (C.boundaryComplex Λ E)) = 0) :=
  ⟨fun _ _ _ zbar hz ↦ C.isZero_leftDerivedUpperStar_boundaryComplex hℓ Λ hΛ E hE zbar hz,
    C.isFiniteLocallyConstantSheaf_homology_boundaryComplex hℓ Λ hΛ E hE,
    fun _ _ _ _ sbar hs ↦
      C.derivedGlobalSectionsRestriction_boundaryComplex_eq_zero hℓ Λ hΛ E hE sbar hs⟩

end AlgebraicGeometry.Scheme.TransverseCorner

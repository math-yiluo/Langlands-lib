/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceIntegralFactor
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelUnit

/-!

# The special fibre of the change of trait to a generic slice trait

Let `D` be a generic slice trait `S' = Spec R` of `𝔸¹_S`, `S = Spec k'⟦t⟧`, with residue field
`κ`, and `K = k'(x)^alg`. The residue field extension `κ ⟶ K` of the change of trait
`Spec K⟦t⟧ ⟶ S'` is algebraic (`AlgebraicGeometry.GenericSliceTrait.isAlgebraic_κK`): its image
contains `k'` and the coordinate `x`. As `κ` is separably closed, it is purely inseparable, so
`Spec K ⟶ Spec κ` is a universal homeomorphism. Consequently the map of special fibres of the
change of trait `τ : 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳 ×_{𝔸¹_S} S'` of a model with a coordinate, its base
change, is a universal homeomorphism
(`NearbyCyclesModel.isUniversalHomeomorphism_coordinateSliceTraitChangeSpecial`), and the derived
pullback along it reflects isomorphisms
(`NearbyCyclesModel.isIso_of_isIso_map_coordinateSliceTraitChangeSpecial`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

/-- The coordinate `x` of the generic slice is the residue of an element of `R`. -/
lemma exists_κK_b_eq : ∃ r : D.R, D.κK (D.b r) = traitSliceCoord k' := by
  let ψ := Spec.preimage (D.toAffineLine ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).hom)
  have hψ : ψ ≫ CommRingCat.ofHom D.ι =
      CommRingCat.ofHom (traitSliceRingHom (traitSliceCoord k')) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc, D.spec_ι_comp, traitSlice,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨ψ.hom (MvPolynomial.X ⟨0⟩), ?_⟩
  have h := congrArg (fun f ↦ PowerSeries.constantCoeff (f.hom (MvPolynomial.X ⟨0⟩))) hψ
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, traitSliceRingHom,
    MvPolynomial.eval₂Hom_X', PowerSeries.constantCoeff_C] at h
  rw [← h]
  exact RingHom.congr_fun D.κK_comp_b _

/-- The image of `k'(x)` in `K` lies in the image of the residue field `κ` of the generic slice
trait. -/
lemma algebraMap_mem_range_κK (f : RatFunc k') :
    algebraMap (RatFunc k') (traitSliceField k') f ∈ D.κK.range := by
  obtain ⟨r, hr⟩ := D.exists_κK_b_eq
  have hpol : ∀ p : Polynomial k', algebraMap (RatFunc k') (traitSliceField k')
      (algebraMap (Polynomial k') (RatFunc k') p) ∈ D.κK.range := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, map_add]
      exact add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow,
        RatFunc.algebraMap_X, RatFunc.algebraMap_C]
      refine mul_mem (RingHom.mem_range.2 ⟨D.κS a, ?_⟩)
        (pow_mem (RingHom.mem_range.2 ⟨D.b r, hr⟩) n)
      rw [← RingHom.comp_apply, D.κK_comp_κS, IsScalarTower.algebraMap_apply k' (RatFunc k')]
      rfl
  have hfield : algebraMap (RatFunc k') (traitSliceField k') f ∈ D.κK.fieldRange := by
    rw [← RatFunc.num_div_denom f, map_div₀]
    exact div_mem (by simpa using hpol f.num) (by simpa using hpol f.denom)
  simpa using hfield

/-- **The residue field extension of the change of trait `Spec K⟦t⟧ ⟶ S'` is algebraic.** -/
theorem isAlgebraic_κK :
    letI := D.κK.toAlgebra
    Algebra.IsAlgebraic D.κ (traitSliceField k') := by
  let := D.κK.toAlgebra
  let e : D.κ ≃+* D.κK.range :=
    RingEquiv.ofBijective D.κK.rangeRestrict ⟨fun x y h ↦ D.κK.injective (congrArg Subtype.val h),
      D.κK.rangeRestrict_surjective⟩
  let c : RatFunc k' →+* D.κ := e.symm.toRingHom.comp
    ((algebraMap (RatFunc k') (traitSliceField k')).codRestrict D.κK.range
      (D.algebraMap_mem_range_κK))
  refine Algebra.IsAlgebraic.ringHom_of_comp_eq c (RingHom.id _) c.injective
    Function.surjective_id ?_
  ext f
  have : D.κK.rangeRestrict (e.symm _) = _ := e.apply_symm_apply
    ((algebraMap (RatFunc k') (traitSliceField k')).codRestrict D.κK.range
      D.algebraMap_mem_range_κK f)
  exact congrArg Subtype.val this

/-- **`Spec K ⟶ Spec κ` is a universal homeomorphism**: `K / κ` is algebraic, hence purely
inseparable over the separably closed `κ`. -/
instance isUniversalHomeomorphism_specMap_κK :
    IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom D.κK)) := by
  let := D.κK.toAlgebra
  have := D.isAlgebraic_κK
  exact inferInstanceAs
    (IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap D.κ (traitSliceField k')))))

end AlgebraicGeometry.GenericSliceTrait

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (D : GenericSliceTrait k')

/-- The closed point of `Spec K⟦t⟧` lies over the closed point of `S'`, along `κ ⟶ K`. -/
lemma specMap_κK_comp_toAffineLine :
    Spec.map (CommRingCat.ofHom D.κK) ≫ Spec.map (CommRingCat.ofHom D.b) ≫ D.toAffineLine =
      traitClosedPoint (traitSliceField k') ≫ traitSlice (traitSliceCoord k') := by
  rw [← D.spec_ι_comp, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, D.κK_comp_b,
    CommRingCat.ofHom_comp, Spec.map_comp_assoc, traitClosedPoint]

/-- **The special fibre of the change of trait to the generic slice trait is the base change of
`Spec K ⟶ Spec κ`**: `(𝒳 ×_{𝔸¹_S} Spec K⟦t⟧)_s = (𝒳 ×_{𝔸¹_S} S')_s ×_{Spec κ} Spec K`. -/
lemma isPullback_coordinateSliceTraitChangeSpecial :
    IsPullback (coordinateSliceTraitChangeSpecial b D) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom D.κK)) := by
  have hS := (IsPullback.of_hasPullback (pullback.snd b D.toAffineLine)
    (Spec.map (CommRingCat.ofHom D.b))).paste_horiz (IsPullback.of_hasPullback b D.toAffineLine)
  have hT := (IsPullback.of_hasPullback (pullback.snd b (traitSlice (traitSliceCoord k')))
    (traitClosedPoint (traitSliceField k'))).paste_horiz
      (IsPullback.of_hasPullback b (traitSlice (traitSliceCoord k')))
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hS
  have e : coordinateSliceTraitChangeSpecial b D ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
    simp [coordinateSliceTraitChangeSpecial]
  rw [e, specMap_κK_comp_toAffineLine]
  exact hT

/-- **The special fibre of the change of trait to the generic slice trait is a universal
homeomorphism**, base change of `Spec K ⟶ Spec κ`. -/
instance isUniversalHomeomorphism_coordinateSliceTraitChangeSpecial :
    IsUniversalHomeomorphism (coordinateSliceTraitChangeSpecial b D) :=
  MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism)
    (isPullback_coordinateSliceTraitChangeSpecial b D).flip inferInstance

/-- **The derived pullback along the special fibre of the change of trait reflects
isomorphisms**: it is fully faithful, the unit of `Lτ_s^* ⊣ Rτ_{s*}` being invertible for the
universal homeomorphism `τ_s`. -/
theorem isIso_of_isIso_map_coordinateSliceTraitChangeSpecial
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {C C' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b)))) Ab.{u + 1})
      (condensedRingObj Λ
        (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b)))))}
    (x : C ⟶ C')
    (h : IsIso (L((coordinateSliceTraitChangeSpecial b D)^*⟦Λ⟧).map x)) : IsIso x := by
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism Λ
    (coordinateSliceTraitChangeSpecial b D)
  exact ((derivedUpperStarLowerStarAdjunction Λ
    (coordinateSliceTraitChangeSpecial b D)).fullyFaithfulLOfIsIsoUnit).isIso_of_isIso_map x

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

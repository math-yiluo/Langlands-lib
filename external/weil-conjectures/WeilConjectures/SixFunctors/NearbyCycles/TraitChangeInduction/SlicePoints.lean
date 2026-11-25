/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitExists

/-!

# The points of the special fibre reached by the slice

Let `S₂ = Spec R₂` be a trait with separably closed point `b₂ : R₂ ⟶ κ`, `M` a model over `S₂`
with special fibre `X' = 𝒳_M ×_{S₂} Spec κ`, `cM : 𝒳_M ⟶ 𝔸¹_{S₂}` a coordinate over `S₂` and
`cX : X' ⟶ 𝔸¹_κ` the induced coordinate of the special fibre. For a slice trait `S'` over `S₂`
with closed point `Spec κ' ⟶ S'`, the special fibre `W = 𝒳_M ×_{𝔸¹_{S₂}} Spec κ'` of the slice of
`M` along `cM` is the base change of `cX` along the point `ξ : Spec κ' ⟶ 𝔸¹_κ` of the closed point
of `S'` (`NearbyCyclesModel.isPullback_sliceTraitSpecial`).

For the strict localization of `𝔸¹_{S₂}` at the generic point of its special fibre, `ξ` is the
generic point of `𝔸¹_κ`, so that every point of `X'` over the generic point of `𝔸¹_κ` comes from
the special fibre of the slice (`NearbyCyclesModel.mem_range_sliceTraitSpecial_of_isGenericPoint`):
this is how the slice step of Deligne's induction (SGA 4½, [Th. finitude], proof of 3.7) reaches
the points of `X'` over the generic point of a coordinate.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section SliceTrait

variable {R₂ : Type u} [CommRing R₂] {Ω₂ : Type u} [Field Ω₂] {a₂ : R₂ →+* Ω₂}
  {κ : Type u} [Field κ] {b₂ : R₂ →+* κ} {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')
  {q₂ : M.total ⟶ Spec (.of R₂)} {p₂ : X' ⟶ Spec (.of κ)}

/-- The special fibre `X'` of a model `M` over `S₂` is `𝒳_M ×_{𝔸¹_{S₂}} 𝔸¹_κ`, for a coordinate
`cM : 𝒳_M ⟶ 𝔸¹_{S₂}` over `S₂` and the induced coordinate `cX : X' ⟶ 𝔸¹_κ` over `κ`. -/
lemma isPullback_i_coordinate (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)))
    (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
    (cX : X' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)))
    (hcX : cX ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂)) = M.i ≫ cM)
    (hcXp : cX ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)) ↘ Spec (.of κ) = p₂) :
    IsPullback M.i cX cM (AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂))) := by
  refine IsPullback.of_bot ?_ hcX.symm (AffineSpace.isPullback_map _)
  rw [hcXp, hcM']
  exact hMi

variable [IsLocalRing R₂] (D : SliceTrait a₂ b₂)

/-- **The special fibre of the slice is a base change of the special fibre.** For a slice trait
`S'` over `S₂` and a point `ξ : Spec κ' ⟶ 𝔸¹_κ` of `𝔸¹_κ` over the closed point of `S'`, the special
fibre `W` of the slice of `M` along `cM` is `X' ×_{𝔸¹_κ} Spec κ'`, via the map of special fibres
`W ⟶ X'` and the coordinate `cX` of `X'`. -/
theorem isPullback_sliceTraitSpecial (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)))
    (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
    (cX : X' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)))
    (hcX : cX ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂)) = M.i ≫ cM)
    (hcXp : cX ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)) ↘ Spec (.of κ) = p₂)
    (ξ : Spec (.of D.κ) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)))
    (hξ : ξ ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂)) =
      Spec.map (CommRingCat.ofHom D.b) ≫ D.toAffineLine)
    (hξ' : ξ ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)) ↘ Spec (.of κ) =
      Spec.map (CommRingCat.ofHom D.κS)) :
    IsPullback (sliceTraitSpecial D M cM hcM' hMi) (pullback.snd _ _) cX ξ := by
  have hW := (IsPullback.of_hasPullback (sliceTraitStructure D M cM)
    (Spec.map (CommRingCat.ofHom D.b))).paste_horiz (IsPullback.of_hasPullback cM D.toAffineLine)
  refine IsPullback.of_right ?_ ?_ (isPullback_i_coordinate M hMi cM hcM' cX hcX hcXp)
  · rw [sliceTraitSpecial, IsPullback.lift_fst, hξ]
    exact hW
  · refine (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1))
      (Spec.map (CommRingCat.ofHom b₂))).hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hcX, hξ, sliceTraitSpecial, IsPullback.lift_fst_assoc]
      exact hW.w
    · rw [Category.assoc, Category.assoc, hcXp, hξ', sliceTraitSpecial, IsPullback.lift_snd]

/-- A point of the special fibre `X'` whose coordinate is the image of the point of `Spec κ'` under
a point `ξ : Spec κ' ⟶ 𝔸¹_κ` over the closed point of the slice trait `S'` comes from the special
fibre of the slice. -/
theorem mem_range_sliceTraitSpecial_of_eq
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)))
    (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
    (cX : X' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)))
    (hcX : cX ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂)) = M.i ≫ cM)
    (hcXp : cX ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)) ↘ Spec (.of κ) = p₂)
    (ξ : Spec (.of D.κ) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)))
    (hξ : ξ ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂)) =
      Spec.map (CommRingCat.ofHom D.b) ≫ D.toAffineLine)
    (hξ' : ξ ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)) ↘ Spec (.of κ) =
      Spec.map (CommRingCat.ofHom D.κS))
    {x : X'} {t : Spec (.of D.κ)} (hxt : cX x = ξ t) :
    x ∈ Set.range (sliceTraitSpecial D M cM hcM' hMi) := by
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x t hxt
  refine ⟨(isPullback_sliceTraitSpecial M D hMi cM hcM' cX hcX hcXp ξ hξ hξ').isoPullback.inv w,
    ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw]

end SliceTrait

section StrictLocalization

variable {R₂ : Type u} [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {Ω₂ : Type u} [Field Ω₂] {a₂ : R₂ →+* Ω₂}
  (ha₂ : Function.Injective a₂) (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂)
  {κ : Type u} [Field κ] {b₂ : R₂ →+* κ} (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)

/-- The closed point of the strict localization of `𝔸¹_{S₂}` at the generic point of its special
fibre lies over the point `x` of `𝔸¹_κ`. -/
lemma traitSlicePoint_comp_map_eq :
    traitSlicePoint (traitSliceCoord κ) ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂)) =
      Spec.map (CommRingCat.ofHom
          (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).b) ≫
        (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).toAffineLine := by
  rw [sliceTraitOfStrictLocalization_b, sliceTraitOfStrictLocalization_toAffineLine,
    CommRingCat.ofHom_hom, Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase,
    sliceTraitPoint_eq, traitSlicePoint, AffineSpace.map_SpecMap, Category.assoc,
    Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    sliceTraitPointRingHom_eq]
  rfl

/-- The point `x` of `𝔸¹_κ` lies over the embedding `κ ⟶ κ(x)^alg`. -/
lemma traitSlicePoint_comp_over :
    traitSlicePoint (traitSliceCoord κ) ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)) ↘ Spec (.of κ) =
      Spec.map (CommRingCat.ofHom
        (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).κS) := by
  rw [traitSlicePoint, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  simp [sliceTraitOfStrictLocalization]

/-- **Every point of the special fibre over the generic point of the coordinate comes from the
slice.** Let `D` be the strict localization of `𝔸¹_{S₂}` at the generic point of its special
fibre. A point of the special fibre `X'` of `M` sent by its coordinate `cX` to the generic point of
`𝔸¹_κ` lies in the image of the special fibre of the slice of `M` along `cM` over `D`. -/
theorem mem_range_sliceTraitSpecial_of_isGenericPoint {X X' : Scheme.{u}}
    (M : NearbyCyclesModel X X') {q₂ : M.total ⟶ Spec (.of R₂)} {p₂ : X' ⟶ Spec (.of κ)}
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)))
    (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
    (cX : X' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)))
    (hcX : cX ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom b₂)) = M.i ≫ cM)
    (hcXp : cX ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of κ)) ↘ Spec (.of κ) = p₂)
    (x : X') (hx : IsGenericPoint (cX x) Set.univ) :
    x ∈ Set.range (sliceTraitSpecial
      (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂) M cM hcM' hMi) :=
  mem_range_sliceTraitSpecial_of_eq M _ hMi cM hcM' cX hcX hcXp _
    (traitSlicePoint_comp_map_eq ha₂ halg₂ hb₂) (traitSlicePoint_comp_over ha₂ halg₂ hb₂)
    (t := IsLocalRing.closedPoint (traitSliceField κ))
    (hx.eq (isGenericPoint_traitSlicePoint_traitSliceCoord κ _))

end StrictLocalization

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

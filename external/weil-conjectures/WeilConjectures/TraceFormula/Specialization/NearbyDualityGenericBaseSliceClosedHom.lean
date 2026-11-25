/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.GenericRestriction.GenericFibre
public import WeilConjectures.TraceFormula.Specialization.GenericSliceBaseMap
public import WeilConjectures.TraceFormula.Specialization.SliceSpecialPullback

/-!

# The pullbacks to a generic slice commute with internal Hom

For the generic slice of a trait model over a generic base along a coordinate `b`, the pullbacks
along the special-fibre map `p : 𝒳''_s ⟶ X'` and the generic-fibre map `c : X₂ ⟶ X₁` commute
with internal Hom
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_closedHomComparison_sliceSpecialUpperStar`,
`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_closedHomComparison_genericSliceUpperStar`).
This is blueprint `lemma-restriction-geometric-generic-fibre` (2)
(`lemma-restriction-geometric-generic-fibre`) for the two pullbacks:

* `p` is the base change along the special coordinate `𝒳_s ⟶ 𝔸¹_{k'}` of the geometric generic
  point `Spec K ⟶ 𝔸¹_{k'}` (`NearbyCyclesModel.isPullback_sliceSpecialMap_traitSlicePoint`), so
  `ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_isPullback` applies;
* `c` is `X₂ ≅ 𝒳''_η ⟶ 𝒳_η ⟶ X₁ ×_F η ⟶ X₁`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceBaseMap_eq`): the base change of the
  generic slice `Spec Frac K⟦t⟧ ⟶ 𝔸¹_η`, which lies over the generic point of `𝔸¹_η`, an open
  immersion and the change of the base field along `ι`
  (`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_fieldExtension`); the comparisons
  compose (`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

namespace IsTraitModelOfGenericBase

omit [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [IsSepClosed k'] [LocallyOfFiniteType X₁.hom]
  [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom] in
/-- **The pullback to the special fibre of a generic slice commutes with internal Hom**
(blueprint `lemma-restriction-geometric-generic-fibre` (2), for the geometric generic fibre
`𝒳''_s = 𝒳_s ×_{𝔸¹_{k'}} Spec K` of the coordinate): the comparison
`p^* RHom(A, ω_{X'}) ⟶ RHom(p^* A, p^* ω_{X'})` is an isomorphism. -/
theorem isIso_closedHomComparison_sliceSpecialUpperStar
    (A : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (Functor.LaxMonoidal.μ (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb))
      (𝟙 ((sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X'))) A) := by
  have hsq := isPullback_sliceSpecialMap_traitSlicePoint (traitSliceCoord k') h.isTraitModelOver hb
  rw [traitSlicePoint_eq_comp_affineLineGenericPoint (transcendental_traitSliceCoord k')] at hsq
  have hiso := isIso_ihomUpperStarComparison_of_isPullback ℓ X'
    (specialCoordinate h.isTraitModelOver b hb) (specialCoordinate_over _ _ _)
    (transcendentalFractionLift (transcendental_traitSliceCoord k')) hsq A.obj
    (dualizingComplex ℓ X').obj A.property (dualizingComplex ℓ X').property
  have := isIso_nearbyDualityMap_upperStarOfMap_id_of_isIso ℓ (P := X')
    (P' := baseChangeSpecial b (traitSlice (traitSliceCoord k')))
    (sliceSpecialMap _ h.isTraitModelOver hb) (dualizingComplex ℓ X') A hiso
  exact this

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom] in
/-- **The pullback to the base of a generic slice commutes with internal Hom** (blueprint
`lemma-restriction-geometric-generic-fibre` (2), on the generic fibres): the comparison
`c^* RHom(A, ω_{X₁}) ⟶ RHom(c^* A, c^* ω_{X₁})` is an isomorphism. -/
theorem isIso_closedHomComparison_genericSliceUpperStar
    (A : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (Functor.LaxMonoidal.μ (genericSliceUpperStar (traitSliceCoord k') ℓ h hb))
      (𝟙 ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁))) A) := by
  obtain ⟨w, hw, hw₁, hw₂⟩ := h.exists_openImmersion_genericFibre
  have hc := genericSliceBaseMap_eq (traitSliceCoord k') h hb w hw₂
  have hq := h.isTraitModelOver
  have := hq.locallyOfFiniteType
  have := hq.quasiCompact
  have := hq.isSeparated
  -- the base change `X₁ ×_F η ⟶ X₁` of the field extension `ι`
  let : Algebra F (FractionRing (PowerSeries k')) := (Spec.preimage ι).hom.toAlgebra
  have hι : Spec.map (CommRingCat.ofHom (algebraMap F (FractionRing (PowerSeries k')))) = ι := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  have sq₁ : IsPullback (pullback.fst X₁.hom ι) (pullback.snd X₁.hom ι) X₁.hom
      (Spec.map (CommRingCat.ofHom (algebraMap F (FractionRing (PowerSeries k'))))) := by
    rw [hι]; exact IsPullback.of_hasPullback _ _
  -- the generic slice `X₂ ⟶ 𝒳_η` over the generic point of `𝔸¹_η`
  have hx := transcendental_traitSliceCoord k'
  have hchar := Algebra.ringChar_eq k' (FractionRing (PowerSeries k'))
  have : Fact (ringChar (FractionRing (PowerSeries k'))).Prime := ⟨hchar ▸ Fact.out⟩
  have : Fact (ringChar (FractionRing (PowerSeries k')) ≠ ℓ) := ⟨hchar ▸ Fact.out⟩
  have sq₂ := isPullback_genericSliceFibreMap (traitSliceCoord k') hb
  rw [traitGenericSlice_eq_comp_affineLineGenericPoint hx] at sq₂
  let Xη : Over (Spec (.of (FractionRing (PowerSeries k')))) :=
    Over.mk (pullback.snd q (traitGenericSpec k'))
  have : LocallyOfFiniteType Xη.hom := by dsimp [Xη]; infer_instance
  have : QuasiCompact Xη.hom := by dsimp [Xη]; infer_instance
  have : IsSeparated Xη.hom := by dsimp [Xη]; infer_instance
  have hK := A.property
  have hM := (dualizingComplex ℓ X₁).property
  have h₁ := isIso_ihomUpperStarComparison_of_fieldExtension ℓ X₁ sq₁ A.obj
    (dualizingComplex ℓ X₁).obj hK hM
  have h₂ : IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) w
      ((L((pullback.fst X₁.hom ι)^*⟦(Profinite.padicAlgClRingObj ℓ)⟧)).obj A.obj)
      ((L((pullback.fst X₁.hom ι)^*⟦(Profinite.padicAlgClRingObj ℓ)⟧)).obj
        (dualizingComplex ℓ X₁).obj)) := inferInstance
  have hK' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ w _
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (pullback.fst X₁.hom ι) _ hK)
  have hM' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ w _
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (pullback.fst X₁.hom ι) _ hM)
  have h₃ := isIso_ihomUpperStarComparison_of_isPullback ℓ Xη
    (coordinateBaseChange b hb (traitGenericSpec k')) (coordinateBaseChange_over _ _ _)
    (traitGenericSliceLift hx) sq₂ _ _ hK' hM'
  have h₃₄ := isIso_ihomUpperStarComparison_comp (Profinite.padicAlgClRingObj ℓ)
    (genericSliceFibreIso (traitSliceCoord k') hb).inv
    (genericSliceFibreMap (traitSliceCoord k') hb) h₃ inferInstance
  have h₂₃₄ := isIso_ihomUpperStarComparison_comp (Profinite.padicAlgClRingObj ℓ)
    ((genericSliceFibreIso (traitSliceCoord k') hb).inv ≫
      genericSliceFibreMap (traitSliceCoord k') hb) w h₂ h₃₄
  have h₁₂₃₄ := isIso_ihomUpperStarComparison_comp (Profinite.padicAlgClRingObj ℓ)
    (((genericSliceFibreIso (traitSliceCoord k') hb).inv ≫
      genericSliceFibreMap (traitSliceCoord k') hb) ≫ w) (pullback.fst X₁.hom ι) h₁ h₂₃₄
  have hc' : h.genericSliceBaseMap (traitSliceCoord k') hb =
      (((genericSliceFibreIso (traitSliceCoord k') hb).inv ≫
        genericSliceFibreMap (traitSliceCoord k') hb) ≫ w) ≫ pullback.fst X₁.hom ι := by
    rw [hc]; simp only [Category.assoc]
  rw [← hc'] at h₁₂₃₄
  exact isIso_nearbyDualityMap_upperStarOfMap_id_of_isIso ℓ (P := X₁)
    (P' := genericSliceBase (traitSliceCoord k') hb) _ (dualizingComplex ℓ X₁) A h₁₂₃₄

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

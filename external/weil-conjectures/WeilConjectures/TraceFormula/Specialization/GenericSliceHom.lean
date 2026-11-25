/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceOpen
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingCompositionLaw

/-!

# Generic slices of a morphism of trait models

Let `φ : M ⟶ N` be a morphism of trait models over a common generic base `(F, ι)`, over
`i₁ : X₁ ⟶ Y₁` and `i₂ : X' ⟶ Y'`, and let `b = φ ≫ b_N` be a coordinate of `M` restricted from a
coordinate `b_N` of `N`. The generic slices along `b` and `b_N` are related by the morphism of
generic slice models `φ'' = NearbyCyclesModel.Hom.genericSliceOpenHom` over the maps
`i₁'' : X₂ ⟶ Y₂` of the bases and `i₂'' : X'' ⟶ Y''` of the special fibres of the slices (the
construction of `TraceFormula.Specialization.NearbyDualityGenericBaseSliceOpen` does not use that
`φ` is an open immersion). This file collects the properties needed to compare the exchanges of
`φ` and of `φ''` (`NearbyCyclesModel.Hom.exceptionalExchange_slice_app`) and to apply the
composition law of the dualizing maps
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_comp_law`) to `φ''`:

* `NearbyCyclesModel.Hom.genericSliceHom_total_comp`, `...generic_comp`: the square of slice
  projections and of `φ`, `φ''` commutes on total spaces and on geometric generic fibres;
* `NearbyCyclesModel.Hom.isPullback_sliceSpecialMap`: the square of special fibres
  `X'' = X' ×_{Y'} Y''` is cartesian (slicing is base change along the generic slice);
* `NearbyCyclesModel.Hom.isPullback_genericSliceBaseMap`: for trait models with full geometric
  generic fibres, the square of bases `X₂ = X₁ ×_{Y₁} Y₂` is cartesian. The generic fibre of a
  trait model with full geometric generic fibre is all of `X₁ ×_F η`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isIso_genericFibre`, by descent of
  surjectivity along `Spec Ω ⟶ η`), and `X₂ = 𝒳_η ×_{𝔸¹_η} Spec Frac K⟦t⟧`;
* hence `i₁''` and `i₂''` are proper (closed immersions) when `i₁` and `i₂` are;
* the generic slice models have full geometric generic fibres
  (`NearbyCyclesModel.isPullback_genericSliceModel_ε`), are proper over the trait when the models
  are (`NearbyCyclesModel.isProper_genericSlice_q`), and so are their bases and special fibres;
* the composition law of the dualizing maps for `φ''`
  (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_comp_law_genericSlice`).

The projective line `ℙ¹_S` (`NearbyCyclesModel.projectiveLineModel`) has no coordinate to `𝔸¹_S`,
so it is not covered here: slicing a model mapping to `ℙ¹_S` needs the open sub-model `𝔸¹_S`,
which is not proper.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  (x : K) {X₁ Y₁ : Over (Spec (.of F))} {X' Y' : Over (Spec (.of k'))}
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {N : NearbyCyclesModel Y₁.left Y'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

section FullGenericFibre

/-- **The generic fibre of a trait model with full geometric generic fibre**: if the geometric
generic fibre of a trait model over the generic base is all of `X₁ ×_F Spec Ω`, its generic fibre
`𝒳_η` is all of `X₁ ×_F η`. The open immersion `w : 𝒳_η ⟶ X₁ ×_F η` becomes an isomorphism after
the faithfully flat base change `Spec Ω ⟶ η`, so it is surjective. -/
lemma IsTraitModelOfGenericBase.exists_isIso_genericFibre
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    ∃ w : pullback q (traitGenericSpec k') ⟶ pullback X₁.hom ι,
      IsIso w ∧ w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ w ≫ pullback.fst _ _ =
          M.ε := by
  obtain ⟨w, hw, hw₁, hw₂⟩ := h.exists_openImmersion_genericFibre
  have hM := h.isTraitModelOver
  have hr := isPullback_genericFibreBaseChangeMap k' X₁ ι
  let s := genericFibreInclusion M q g hM.isPullback_j.w
  let u := hr.lift (s ≫ w) g (by
    rw [Category.assoc, hw₁, genericFibreInclusion_snd])
  have hu : u ≫ genericFibreBaseChangeMap k' X₁ ι = s ≫ w := hr.lift_fst _ _ _
  have hu₁ : u ≫ pullback.fst _ _ = M.ε := by
    rw [← genericFibreBaseChangeMap_fst k' X₁ ι, reassoc_of% hu, hw₂]
  have hu₂ : u ≫ pullback.snd _ _ = g := hr.lift_snd _ _ _
  have hiso : IsIso u := by
    have : u = hgen.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [hu₁, IsPullback.isoPullback_hom_fst]
      · rw [hu₂, IsPullback.isoPullback_hom_snd]
    rw [this]
    infer_instance
  have hB : Surjective (genericFibreBaseChangeMap k' X₁ ι) :=
    (MorphismProperty.of_isPullback hr.flip (traitGenericPointToSpec_mem k')).1.1
  have : Surjective (s ≫ w) := by
    rw [← hu]
    infer_instance
  have : Surjective w := Surjective.of_comp s w
  exact ⟨w, (isIso_iff_isOpenImmersion_and_surjective w).2 ⟨hw, this⟩, hw₁, hw₂⟩

/-- The map of generic fibres `𝒳_η ⟶ 𝒴_η` of a morphism of models over the trait. -/
noncomputable abbrev Hom.genericFibreMap {i₁ : X₁.left ⟶ Y₁.left} {i₂ : X'.left ⟶ Y'.left}
    (φ : M.Hom N i₁ i₂) (hq : q = φ.total ≫ qN) :
    pullback q (traitGenericSpec k') ⟶ pullback qN (traitGenericSpec k') :=
  pullback.map _ _ _ _ φ.total (𝟙 _) (𝟙 _) (by rw [hq, Category.comp_id])
    (by rw [Category.comp_id, Category.id_comp])

/-- The square of generic fibres of a morphism of models over the trait is cartesian:
`𝒳_η = 𝒳 ×_𝒴 𝒴_η`. -/
lemma Hom.isPullback_genericFibreMap {i₁ : X₁.left ⟶ Y₁.left} {i₂ : X'.left ⟶ Y'.left}
    (φ : M.Hom N i₁ i₂) (hq : q = φ.total ≫ qN) :
    IsPullback (pullback.fst _ _) (φ.genericFibreMap hq) φ.total (pullback.fst _ _) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback qN (traitGenericSpec k'))
  rw [pullback.lift_snd, Category.comp_id, ← hq]
  exact IsPullback.of_hasPullback q (traitGenericSpec k')

/-- The identifications of generic fibres `w` with full generic fibres are compatible with a
morphism of trait models over the generic base. -/
lemma Hom.genericFibreMap_comp_eq {i₁ : X₁ ⟶ Y₁} {i₂ : X'.left ⟶ Y'.left}
    (φ : M.Hom N i₁.left i₂) (hq : q = φ.total ≫ qN) (hg : g = φ.generic ≫ gN)
    (hM : M.IsTraitModelOver q g) (hN : N.IsTraitModelOver qN gN)
    (wM : pullback q (traitGenericSpec k') ⟶ pullback X₁.hom ι)
    (hwM₁ : wM ≫ pullback.snd _ _ = pullback.snd _ _)
    (hwM₂ : genericFibreInclusion M q g hM.isPullback_j.w ≫ wM ≫ pullback.fst _ _ = M.ε)
    (wN : pullback qN (traitGenericSpec k') ⟶ pullback Y₁.hom ι)
    (hwN₁ : wN ≫ pullback.snd _ _ = pullback.snd _ _)
    (hwN₂ : genericFibreInclusion N qN gN hN.isPullback_j.w ≫ wN ≫ pullback.fst _ _ = N.ε) :
    wM ≫ pullback.map _ _ _ _ i₁.left (𝟙 _) (𝟙 _) (by rw [Over.w i₁, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp]) =
      φ.genericFibreMap hq ≫ wN := by
  apply pullback.hom_ext
  · have : Epi (genericFibreInclusion M q g hM.isPullback_j.w) :=
      hM.epi_lift_traitGenericPointToSpec
    refine (cancel_epi (genericFibreInclusion M q g hM.isPullback_j.w)).1 ?_
    have hs : genericFibreInclusion M q g hM.isPullback_j.w ≫ φ.genericFibreMap hq =
        φ.generic ≫ genericFibreInclusion N qN gN hN.isPullback_j.w := by
      apply pullback.hom_ext
      · simp [φ.comm_j]
      · simp [hg]
    rw [Category.assoc, Category.assoc, pullback.lift_fst, reassoc_of% hwM₂,
      reassoc_of% hs, hwN₂, φ.comm_ε]
  · simp [hwM₁, hwN₁]

end FullGenericFibre

section SliceModel

variable {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-- **The generic slice model has full geometric generic fibre**: `𝒳''_Ω = X₂ ×_{F'} Spec Ω_K`,
`F' = Frac K⟦t⟧`. -/
lemma isPullback_genericSliceModel_ε (hM : M.IsTraitModelOver q g) :
    IsPullback (genericSliceModel x hb).ε (pullback.snd _ _) (genericSliceBase x hb).hom
      (traitGenericPointToSpec K ≫ 𝟙 _) := by
  have hB := (isTraitModelOfGenericBase_genericSliceModel x hb hM).isTraitModelOver
  have h₁ := hB.isPullback_traitGenericPointToSpec
  have h₂ : IsPullback (genericSliceFibreIso x hb).hom (pullback.snd _ _)
      (genericSliceBase x hb).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [genericSliceFibreIso_hom_over, Category.comp_id]⟩
  rw [genericSliceModel_ε]
  exact h₁.paste_horiz h₂

include hb in
/-- The total space of the generic slice of a proper model is proper over `Spec K⟦t⟧`. -/
lemma isProper_genericSlice_q [IsProper q] : IsProper (pullback.snd b (traitSlice x)) := by
  have : IsProper (b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') := hb ▸ inferInstance
  have : IsProper b := IsProper.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  infer_instance

include hb in
/-- The special fibre of the generic slice of a proper model is proper over `Spec K`. -/
lemma isProper_baseChangeSpecial [IsProper q] :
    IsProper (baseChangeSpecial b (traitSlice x)).hom := by
  have := isProper_genericSlice_q x hb
  exact inferInstanceAs (IsProper (pullback.snd _ _))

/-- The base of the generic slice of a proper model is proper over `Frac K⟦t⟧`. -/
lemma isProper_genericSliceBase [IsProper q] : IsProper (genericSliceBase x hb).hom := by
  have : IsProper (b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') := hb ▸ inferInstance
  have : IsProper b := IsProper.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : IsProper (coordinateBaseChange b hb (traitGenericSpec k')) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (isPullback_coordinateBaseChange b hb (traitGenericSpec k')) inferInstance
  exact inferInstanceAs (IsProper (pullback.snd _ _))

end SliceModel

section Hom

variable {i₁ : X₁ ⟶ Y₁} {i₂ : X' ⟶ Y'} (φ : M.Hom N i₁.left i₂.left)
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')} {bN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  (hbN : bN ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qN) (hbb : φ.total ≫ bN = b)

namespace Hom

/-- **The slice projections commute with `φ` on total spaces**:
`s_M ≫ φ = φ'' ≫ s_N` on `𝒳'' ⟶ 𝒴`. -/
lemma genericSliceHom_total_comp (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN) :
    (hM.genericSliceHom x hb).total ≫ φ.total =
      (φ.genericSliceOpenHom x hb hbN hbb).total ≫ (hN.genericSliceHom x hbN).total := by
  simp [IsTraitModelOfGenericBase.genericSliceHom]

/-- **The slice projections commute with `φ` on geometric generic fibres**. -/
lemma genericSliceHom_generic_comp (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN) (hg : g = φ.generic ≫ gN) :
    (hM.genericSliceHom x hb).generic ≫ φ.generic =
      (φ.genericSliceOpenHom x hb hbN hbb).generic ≫ (hN.genericSliceHom x hbN).generic :=
  baseChangeGenericMap_comp_generic hM.isTraitModelOver hN.isTraitModelOver hg

/-- The slice projections commute with `φ` on the bases: `c_M ≫ i₁ = i₁'' ≫ c_N`. -/
lemma genericSliceBaseMap_comp (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN) (hg : g = φ.generic ≫ gN) :
    hM.genericSliceBaseMap x hb ≫ i₁.left =
      (φ.genericSliceBaseMap x hb hbN hbb).left ≫ hN.genericSliceBaseMap x hbN :=
  hM.genericSliceBaseMap_comp_openSubmodel hN hg

/-- The slice projections commute with `φ` on the special fibres: `p_M ≫ i₂ = i₂'' ≫ p_N`. -/
lemma sliceSpecialMap_comp (hM : M.IsTraitModelOver q g) (hN : N.IsTraitModelOver qN gN) :
    sliceSpecialMap x hM hb ≫ i₂.left =
      (φ.genericSliceSpecialMap x hbb).left ≫ sliceSpecialMap x hN hbN :=
  sliceSpecialMap_comp_openSubmodel hM hN

/-- **The square of special fibres of the slices is cartesian**: `X'' = X' ×_{Y'} Y''`, since
slicing is base change along the generic slice and `X' = 𝒳 ×_𝒴 Y'`. -/
lemma isPullback_sliceSpecialMap (hM : M.IsTraitModelOver q g) (hN : N.IsTraitModelOver qN gN)
    (hq : q = φ.total ≫ qN) :
    IsPullback (sliceSpecialMap x hM hb) (φ.genericSliceSpecialMap x hbb).left i₂.left
      (sliceSpecialMap x hN hbN) := by
  have hi : IsPullback M.i i₂.left φ.total N.i := by
    refine IsPullback.of_bot ?_ φ.comm_i.symm hN.isPullback_i
    rw [Over.w i₂, ← hq]
    exact hM.isPullback_i
  have hout := (isPullback_sliceFibreMap x hbb (traitClosedPoint K)).flip.paste_horiz
    (isPullback_sliceTotalMap x hbb).flip
  refine IsPullback.of_right ?_ (sliceSpecialMap_comp x φ hb hbN hbb hM hN) hi
  rw [sliceSpecialMap, sliceSpecialMap, hM.isPullback_i.lift_fst, hN.isPullback_i.lift_fst]
  exact hout

/-- The map of generic fibres of the slices, through `𝒳''_η ≅ X₂`, is `i₁''`. -/
lemma genericSliceBaseMap_left :
    (φ.genericSliceBaseMap x hb hbN hbb).left = (genericSliceFibreIso x hb).inv ≫
      sliceFibreMap x hbb (traitGenericSpec K) ≫ (genericSliceFibreIso x hbN).hom :=
  rfl

/-- The square of generic fibres of the slices is cartesian: `𝒳''_η = 𝒳_η ×_{𝒴_η} 𝒴''_η`. -/
lemma isPullback_genericSliceFibreMap (hq : q = φ.total ≫ qN) :
    IsPullback (genericSliceFibreMap x hb) (sliceFibreMap x hbb (traitGenericSpec K))
      (φ.genericFibreMap hq) (genericSliceFibreMap x hbN) := by
  have hout := (isPullback_sliceFibreMap x hbb (traitGenericSpec K)).flip.paste_horiz
    (isPullback_sliceTotalMap x hbb).flip
  refine IsPullback.of_right ?_ ?_ (φ.isPullback_genericFibreMap hq)
  · rw [genericSliceFibreMap_fst, genericSliceFibreMap_fst]
    exact hout
  · apply pullback.hom_ext
    · simp
    · simp

/-- **The square of bases of the slices is cartesian**: for trait models with full geometric
generic fibres, `X₂ = X₁ ×_{Y₁} Y₂`. The map `c_M : X₂ ⟶ X₁` is `X₂ ≅ 𝒳''_η ⟶ 𝒳_η ≅ X₁ ×_F η ⟶ X₁`
and the three squares are cartesian. -/
lemma isPullback_genericSliceBaseMap (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
    (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hNgen : IsPullback N.ε gN Y₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hq : q = φ.total ≫ qN) (hg : g = φ.generic ≫ gN) :
    IsPullback (hM.genericSliceBaseMap x hb) (φ.genericSliceBaseMap x hb hbN hbb).left i₁.left
      (hN.genericSliceBaseMap x hbN) := by
  obtain ⟨wM, hwM, hwM₁, hwM₂⟩ := hM.exists_isIso_genericFibre hMgen
  obtain ⟨wN, hwN, hwN₁, hwN₂⟩ := hN.exists_isIso_genericFibre hNgen
  -- the map of bases of a slice through the generic fibre
  have hc : ∀ {Z₁ : Over (Spec (.of F))} {Z' : Over (Spec (.of k'))}
      {P : NearbyCyclesModel Z₁.left Z'.left} {qP : P.total ⟶ trait k'}
      {gP : P.generic ⟶ Spec (.of (traitGenericField k'))}
      (hP : P.IsTraitModelOfGenericBase Z₁ ι qP gP) {bP : P.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
      (hbP : bP ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qP)
      (w : pullback qP (traitGenericSpec k') ⟶ pullback Z₁.hom ι)
      (_ : genericFibreInclusion P qP gP hP.isTraitModelOver.isPullback_j.w ≫ w ≫
        pullback.fst _ _ = P.ε),
      hP.genericSliceBaseMap x hbP = (genericSliceFibreIso x hbP).inv ≫
        genericSliceFibreMap x hbP ≫ w ≫ pullback.fst _ _ := by
    intro Z₁ Z' P qP gP hP bP hbP w hw
    have := hP.epi_genericSliceModel_ε x hbP
    refine (cancel_epi (genericSliceModel x hbP).ε).1 ?_
    have key : pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ traitGenericPointToSpec K)
        (by rw [pullback.condition, Category.assoc, traitGenericPointToSpec_traitGenericSpec]) ≫
          genericSliceFibreMap x hbP =
        baseChangeGenericMap hP.isTraitModelOver bP hbP (traitSlice x) (traitSlice_over x) ≫
          genericFibreInclusion P qP gP hP.isTraitModelOver.isPullback_j.w := by
      apply pullback.hom_ext
      · simp
      · simp only [Category.assoc, genericSliceFibreMap_snd, pullback.lift_snd_assoc,
          genericFibreInclusion_snd, baseChangeGenericMap_g_assoc,
          traitGenericPointToSpec_traitGenericSpecMap]
    rw [hP.genericSliceModel_ε_comp_genericSliceBaseMap, genericSliceModel_ε, Category.assoc,
      Iso.hom_inv_id_assoc, reassoc_of% key, hw]
  rw [hc hM hb wM hwM₂, hc hN hbN wN hwN₂]
  -- the right square: `X₁ ×_F η = X₁ ×_{Y₁} (Y₁ ×_F η)`
  have hR : IsPullback (pullback.fst X₁.hom ι)
      (pullback.map _ _ _ _ i₁.left (𝟙 _) (𝟙 _) (by rw [Over.w i₁, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp]))
      i₁.left (pullback.fst Y₁.hom ι) := by
    refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback Y₁.hom ι)
    rw [pullback.lift_snd, Category.comp_id, Over.w i₁]
    exact IsPullback.of_hasPullback X₁.hom ι
  have hW : IsPullback wM (φ.genericFibreMap hq)
      (pullback.map _ _ _ _ i₁.left (𝟙 _) (𝟙 _) (by rw [Over.w i₁, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp])) wN :=
    IsPullback.of_horiz_isIso ⟨φ.genericFibreMap_comp_eq hq hg hM.isTraitModelOver
      hN.isTraitModelOver wM hwM₁ hwM₂ wN hwN₁ hwN₂⟩
  have hI : IsPullback (genericSliceFibreIso x hb).inv (φ.genericSliceBaseMap x hb hbN hbb).left
      (sliceFibreMap x hbb (traitGenericSpec K)) (genericSliceFibreIso x hbN).inv :=
    IsPullback.of_horiz_isIso ⟨by rw [genericSliceBaseMap_left, Category.assoc,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  have h := hI.paste_horiz (((φ.isPullback_genericSliceFibreMap x hb hbN hbb hq).paste_horiz
    hW).paste_horiz hR)
  simpa only [Category.assoc] using h

/-- The map of bases of the slices is proper if `i₁` is. -/
lemma isProper_genericSliceBaseMap [IsProper i₁.left] (hM : M.IsTraitModelOfGenericBase X₁ ι q g)
    (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
    (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hNgen : IsPullback N.ε gN Y₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hq : q = φ.total ≫ qN) (hg : g = φ.generic ≫ gN) :
    IsProper (φ.genericSliceBaseMap x hb hbN hbb).left :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (φ.isPullback_genericSliceBaseMap x hb hbN hbb hM hN hMgen hNgen hq hg) inferInstance

/-- The map of bases of the slices is a closed immersion if `i₁` is. -/
lemma isClosedImmersion_genericSliceBaseMap [IsClosedImmersion i₁.left]
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g) (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
    (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hNgen : IsPullback N.ε gN Y₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hq : q = φ.total ≫ qN) (hg : g = φ.generic ≫ gN) :
    IsClosedImmersion (φ.genericSliceBaseMap x hb hbN hbb).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (φ.isPullback_genericSliceBaseMap x hb hbN hbb hM hN hMgen hNgen hq hg) inferInstance

include hb hbN in
/-- The map of special fibres of the slices is proper if `i₂` is. -/
lemma isProper_genericSliceSpecialMap [IsProper i₂.left] (hM : M.IsTraitModelOver q g)
    (hN : N.IsTraitModelOver qN gN) (hq : q = φ.total ≫ qN) :
    IsProper (φ.genericSliceSpecialMap x hbb).left :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (φ.isPullback_sliceSpecialMap x hb hbN hbb hM hN hq) inferInstance

include hb hbN in
/-- The map of special fibres of the slices is a closed immersion if `i₂` is. -/
lemma isClosedImmersion_genericSliceSpecialMap [IsClosedImmersion i₂.left]
    (hM : M.IsTraitModelOver q g) (hN : N.IsTraitModelOver qN gN) (hq : q = φ.total ≫ qN) :
    IsClosedImmersion (φ.genericSliceSpecialMap x hbb).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (φ.isPullback_sliceSpecialMap x hb hbN hbb hM hN hq) inferInstance

end Hom

end Hom

/-- **The composition law of the dualizing maps for the generic slices of a morphism of models**:
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_comp_law` for the morphism of generic slice
models `φ'' : M'' ⟶ N''` induced by a morphism `φ : M ⟶ N` of proper trait models with full
geometric generic fibres along compatible coordinates. The slice models are trait models over the
generic base `(Frac K⟦t⟧, 𝟙)` with full geometric generic fibres
(`NearbyCyclesModel.isPullback_genericSliceModel_ε`), proper over `Spec K⟦t⟧`
(`NearbyCyclesModel.isProper_genericSlice_q`), and `i₁''`, `i₂''` are proper
(`NearbyCyclesModel.Hom.isProper_genericSliceBaseMap`,
`NearbyCyclesModel.Hom.isProper_genericSliceSpecialMap`); these are taken as instance arguments
so that they can appear in the statement. -/
theorem NearbyDualizingDataOfGenericBase.θ_comp_law_genericSlice (ℓ : ℕ) [Fact ℓ.Prime]
    [IsSepClosed K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
    [Fact (ringChar (FractionRing (PowerSeries K))).Prime]
    [Fact (ringChar (FractionRing (PowerSeries K)) ≠ ℓ)]
    (D : NearbyDualizingDataOfGenericBase K ℓ) {i₁ : X₁ ⟶ Y₁} {i₂ : X' ⟶ Y'}
    (φ : M.Hom N i₁.left i₂.left) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    {bN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
    (hbN : bN ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qN) (hbb : φ.total ≫ bN = b)
    [LocallyOfFiniteType (genericSliceBase x hb).hom] [QuasiCompact (genericSliceBase x hb).hom]
    [IsSeparated (genericSliceBase x hb).hom]
    [LocallyOfFiniteType (genericSliceBase x hbN).hom] [QuasiCompact (genericSliceBase x hbN).hom]
    [IsSeparated (genericSliceBase x hbN).hom]
    [LocallyOfFiniteType (baseChangeSpecial b (traitSlice x)).hom]
    [QuasiCompact (baseChangeSpecial b (traitSlice x)).hom]
    [IsSeparated (baseChangeSpecial b (traitSlice x)).hom]
    [LocallyOfFiniteType (baseChangeSpecial bN (traitSlice x)).hom]
    [QuasiCompact (baseChangeSpecial bN (traitSlice x)).hom]
    [IsSeparated (baseChangeSpecial bN (traitSlice x)).hom]
    [IsProper (CondensedRing.toPoint (genericSliceBase x hb)).left]
    [IsProper (CondensedRing.toPoint (genericSliceBase x hbN)).left]
    [IsProper (CondensedRing.toPoint (baseChangeSpecial b (traitSlice x))).left]
    [IsProper (CondensedRing.toPoint (baseChangeSpecial bN (traitSlice x))).left]
    (hM : M.IsTraitModelOver q g) (hN : N.IsTraitModelOver qN gN)
    [IsProper (pullback.snd b (traitSlice x))] [IsProper (pullback.snd bN (traitSlice x))]
    [IsProper (φ.genericSliceBaseMap x hb hbN hbb).left]
    [IsProper (φ.genericSliceSpecialMap x hbb).left] :
    (boundedConstructibleNearbyCycles
        ((isTraitModelOfGenericBase_genericSliceModel x hb hM).preservesBoundedConstructible
          (ℓ := ℓ))).map
        (upperShriekDualizingComplexIso ℓ (φ.genericSliceBaseMap x hb hbN hbb)).hom ≫
        D.θ (isTraitModelOfGenericBase_genericSliceModel x hb hM) =
      (exceptionalExchange ℓ (φ.genericSliceBaseMap x hb hbN hbb)
          (φ.genericSliceSpecialMap x hbb)
          ((isTraitModelOfGenericBase_genericSliceModel x hbN hN).properCompactSupportExchange ℓ
            (isTraitModelOfGenericBase_genericSliceModel x hb hM)
            (isPullback_genericSliceModel_ε x hbN hN) (isPullback_genericSliceModel_ε x hb hM)
            (φ.genericSliceBaseMap x hb hbN hbb) (φ.genericSliceSpecialMap x hbb)
            (φ.genericSliceOpenHom x hb hbN hbb) (Hom.genericSliceOpenHom_q _ _ _ _ _)
            (Hom.genericSliceOpenHom_g _ _ _ _ _))).app
          (dualizingComplex ℓ (genericSliceBase x hbN)) ≫
        (boundedConstructibleUpperShriek ℓ (φ.genericSliceSpecialMap x hbb)).map
          (D.θ (isTraitModelOfGenericBase_genericSliceModel x hbN hN)) ≫
        (upperShriekDualizingComplexIso ℓ (φ.genericSliceSpecialMap x hbb)).hom :=
  D.θ_comp_law (isTraitModelOfGenericBase_genericSliceModel x hbN hN)
    (isTraitModelOfGenericBase_genericSliceModel x hb hM)
    (isPullback_genericSliceModel_ε x hbN hN) (isPullback_genericSliceModel_ε x hb hM)
    (φ.genericSliceBaseMap x hb hbN hbb) (φ.genericSliceSpecialMap x hbb)
    (φ.genericSliceOpenHom x hb hbN hbb) (Hom.genericSliceOpenHom_q _ _ _ _ _)
    (Hom.genericSliceOpenHom_g _ _ _ _ _)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Infinity
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBase
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingCompositionLaw
public import WeilConjectures.TraceFormula.Specialization.TraitModelEmbedding

/-!

# Compactifying a trait model along a coordinate

Let `S = Spec k'⟦t⟧` be the trait, `η` its generic point and `Spec Ω` its geometric generic point.

* `AlgebraicGeometry.ProjectiveLine.coordChart`: the affine chart `𝔸¹_S ⟶ ℙ¹_S`, on the affine
  line `𝔸(ULift (Fin 1); S)` of the coordinates of the generic slices (rather than the
  `𝔸(PUnit; S)` of `AlgebraicGeometry.ProjectiveLine.affineChart`).
* `NearbyCyclesModel.traitFibreModel q`: the *generic standard model* of a scheme
  `q : T ⟶ S` over the trait, a model of its generic fibre `T_η` (as a scheme over `η`) with
  geometric generic fibre `T_Ω` and special fibre `T_s`. It is a trait model over the generic
  base `(η, T_η, 𝟙)` (`NearbyCyclesModel.isTraitModelOfGenericBase_traitFibreModel`) with full
  geometric generic fibre (`NearbyCyclesModel.isPullback_traitFibreModel_ε`).
* `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_coordinateCompactification`: a trait model
  `M` over the generic base `(η, X₁, 𝟙)` whose generic fibre is all of `X₁`, with a coordinate
  `b : 𝒳 ⟶ 𝔸¹_S`, is an open sub-model of the open sub-model `W = b̄⁻¹(𝔸¹_S)` of a proper trait
  model `M̄` with full generic fibre and a proper morphism of models `b̄ : M̄ ⟶ ℙ¹_S`
  (`NearbyCyclesModel.projectiveLineModel`), compatibly with the coordinates `b` and `b̄|_W`.
  These are the hypotheses of
  `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel` (for
  `M ⟶ W`), of
  `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel_comp`
  (for `W ⟶ M̄`) and of `NearbyCyclesModel.exists_twist_of_slice_of_composition_law` (for `b̄`).

## Implementation notes

The total space of `M̄` is a Nagata compactification of `b ≫ χ : 𝒳 ⟶ ℙ¹_S`, `χ` the affine chart,
and `b̄` is its structure morphism; no graph closure is needed. The base of `M̄` is its generic
fibre, so that `M̄` has full generic fibre by construction. This is why the generic fibre of `M`
has to be all of `X₁`: the base of an open sub-model of `M̄` is an open of the base of `M̄`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace ProjectiveLine

variable (S : Scheme.{u})

/-- The affine chart `𝔸¹_S ⟶ ℙ¹_S` on the affine line `𝔸(ULift (Fin 1); S)`:
`AlgebraicGeometry.ProjectiveLine.affineChart` after relabelling the coordinate. -/
noncomputable def coordChart : 𝔸(ULift.{u} (Fin 1); S) ⟶ ProjectiveLine S :=
  (AffineSpace.reindexIso S (Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit)).inv ≫ affineChart S

instance : IsOpenImmersion (coordChart S) := by
  unfold coordChart
  infer_instance

instance : QuasiCompact (coordChart S) := by
  unfold coordChart
  infer_instance

@[reassoc (attr := simp)]
lemma coordChart_over :
    coordChart S ≫ ProjectiveLine S ↘ S = 𝔸(ULift.{u} (Fin 1); S) ↘ S := by
  rw [coordChart, Category.assoc, affineChart_over]
  exact AffineSpace.reindex_over _ S

end ProjectiveLine

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme ProjectiveSpace ProjectiveLine

section GenericModel

variable {k' : Type u} [Field k'] {T : Scheme.{u}} (q : T ⟶ trait k')

/-- The generic fibre `T_η = T ×_S η` of a scheme `q : T ⟶ S` over the trait, as a scheme over the
generic point `η`. -/
noncomputable def traitGenericBase :
    Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing)) :=
  Over.mk (pullback.snd q (traitGenericSpec k'))

instance [LocallyOfFiniteType q] : LocallyOfFiniteType (traitGenericBase q).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd q (traitGenericSpec k')))

instance [QuasiCompact q] : QuasiCompact (traitGenericBase q).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd q (traitGenericSpec k')))

instance [IsSeparated q] : IsSeparated (traitGenericBase q).hom :=
  inferInstanceAs (IsSeparated (pullback.snd q (traitGenericSpec k')))

/-- The generic fibre of a proper scheme over the trait is proper over `η`. -/
lemma isProper_toPoint_traitGenericBase [IsProper q] :
    IsProper (toPoint (traitGenericBase q)).left := by
  rw [toPoint_left]
  exact inferInstanceAs (IsProper (pullback.snd q (traitGenericSpec k')))

instance [LocallyOfFiniteType q] : LocallyOfFiniteType (traitStdSpecialFibre q).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd q (traitClosedPoint k')))

instance [QuasiCompact q] : QuasiCompact (traitStdSpecialFibre q).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd q (traitClosedPoint k')))

instance [IsSeparated q] : IsSeparated (traitStdSpecialFibre q).hom :=
  inferInstanceAs (IsSeparated (pullback.snd q (traitClosedPoint k')))

/-- The special fibre of a proper scheme over the trait is proper over `k'`. -/
lemma isProper_toPoint_traitStdSpecialFibre [IsProper q] :
    IsProper (toPoint (traitStdSpecialFibre q)).left := by
  rw [toPoint_left]
  exact inferInstanceAs (IsProper (pullback.snd q (traitClosedPoint k')))

/-- The *generic standard model* of a scheme `q : T ⟶ S` over the trait: total space `T`,
geometric generic fibre `T_Ω = T ×_S Spec Ω`, special fibre `T_s`, as a model of the generic
fibre `T_η`, with `ε : T_Ω ⟶ T_η` the base change of `Spec Ω ⟶ η`. -/
@[simps]
noncomputable def traitFibreModel :
    NearbyCyclesModel (traitGenericBase q).left (traitStdSpecialFibre q).left where
  total := T
  generic := pullback q (traitGenericPoint k')
  j := pullback.fst q (traitGenericPoint k')
  i := pullback.fst q (traitClosedPoint k')
  ε := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ traitGenericPointToSpec k') (by
    rw [pullback.condition, Category.assoc, traitGenericPointToSpec_traitGenericSpec])

/-- The generic standard model is a trait model over the generic base `(η, T_η, 𝟙)`. -/
theorem isTraitModelOfGenericBase_traitFibreModel [LocallyOfFiniteType q] [QuasiCompact q]
    [IsSeparated q] :
    (traitFibreModel q).IsTraitModelOfGenericBase (traitGenericBase q) (𝟙 _) q
      (pullback.snd q (traitGenericPoint k')) := by
  have hM : (traitFibreModel q).IsTraitModelOver (X' := traitStdSpecialFibre q) q
      (pullback.snd q (traitGenericPoint k')) :=
    ⟨inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback _ _,
      IsPullback.of_hasPullback _ _⟩
  refine ⟨hM, inv (pullback.fst (traitGenericBase q).hom (𝟙 _)), inferInstance, ?_, ?_⟩
  · rw [IsIso.inv_comp_eq, ← Category.comp_id (pullback.snd (traitGenericBase q).hom _),
      ← pullback.condition]
    rfl
  · rw [IsIso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [genericFibreInclusion_fst, traitFibreModel_ε, pullback.lift_fst]
      rfl
    · rw [genericFibreInclusion_snd, traitFibreModel_ε, pullback.lift_snd]

/-- The generic fibre of the generic standard model is all of its base `T_η`: the open immersion
of `NearbyCyclesModel.IsTraitModelOfGenericBase` can be chosen invertible. This is the hypothesis
`hfull` of `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_coordinateCompactification`. -/
lemma exists_isIso_genericFibre_traitFibreModel [LocallyOfFiniteType q] [QuasiCompact q]
    [IsSeparated q] :
    ∃ w : pullback q (traitGenericSpec k') ⟶ pullback (traitGenericBase q).hom (𝟙 _), IsIso w ∧
      w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      genericFibreInclusion (traitFibreModel q) q (pullback.snd q (traitGenericPoint k'))
          (isTraitModelOfGenericBase_traitFibreModel q).isTraitModelOver.isPullback_j.w ≫ w ≫
        pullback.fst _ _ = (traitFibreModel q).ε := by
  refine ⟨inv (pullback.fst (traitGenericBase q).hom (𝟙 _)), inferInstance, ?_, ?_⟩
  · rw [IsIso.inv_comp_eq, ← Category.comp_id (pullback.snd (traitGenericBase q).hom _),
      ← pullback.condition]
    rfl
  · rw [IsIso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [genericFibreInclusion_fst, traitFibreModel_ε, pullback.lift_fst]
      rfl
    · rw [genericFibreInclusion_snd, traitFibreModel_ε, pullback.lift_snd]

/-- The geometric generic fibre of the generic standard model is the full base change
`T_η ×_η Spec Ω`. -/
lemma isPullback_traitFibreModel_ε :
    IsPullback (traitFibreModel q).ε (pullback.snd q (traitGenericPoint k'))
      (traitGenericBase q).hom (traitGenericPointToSpec k' ≫ 𝟙 _) := by
  have h₂ : IsPullback ((traitFibreModel q).ε ≫ pullback.fst q (traitGenericSpec k'))
      (pullback.snd q (traitGenericPoint k')) q
      (traitGenericPointToSpec k' ≫ traitGenericSpec k') := by
    rw [traitFibreModel_ε, pullback.lift_fst, traitGenericPointToSpec_traitGenericSpec]
    exact IsPullback.of_hasPullback _ _
  rw [Category.comp_id]
  exact IsPullback.of_right h₂ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

end GenericModel

section Compactification

variable {k' : Type u} [Field k']

/-- **Compactifying a trait model along a coordinate**: let `M` be a trait model of `X₁` over the
generic base `(η, X₁, 𝟙)` whose generic fibre is all of `X₁` (`hfull`), and let
`b : 𝒳 ⟶ 𝔸¹_S` be a coordinate over `S`. Then there are

* a trait model `M̄` of `X̄₁` over the generic base `(η, X̄₁, 𝟙)`, with proper `q̄`, proper `X̄₁`,
  `X̄'` and full geometric generic fibre;
* a morphism of models `b̄ : M̄ ⟶ ℙ¹_S` over proper `b̄₁ : X̄₁ ⟶ ℙ¹_η`, `b̄₂ : X̄' ⟶ ℙ¹_{k'}`, with
  `q̄ = b̄ ≫ (ℙ¹_S ⟶ S)`, `ḡ = b̄ ≫ (ℙ¹_Ω ⟶ Spec Ω)`;
* the open `U = b̄⁻¹(𝔸¹_S)` of the total space of `M̄`, and the coordinate
  `b_W : U ⟶ 𝔸¹_S` of the open sub-model `W = M̄|_U` with `b_W ≫ χ = b̄|_U`;
* open immersions `j : X₁ ⟶ X̄₁`, `j' : X' ⟶ W_s` and an open immersion of models `φ : M ⟶ W`
  with cartesian square of geometric generic fibres, compatible with `q`, `g` and the
  coordinates: `φ ≫ b_W = b`.

The total space of `M̄` is a Nagata compactification of `b ≫ χ : 𝒳 ⟶ ℙ¹_S`, and `M̄` is its
generic standard model (`NearbyCyclesModel.traitFibreModel`). -/
theorem IsTraitModelOfGenericBase.exists_coordinateCompactification
    {X₁ : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing))}
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ (𝟙 _) q g)
    (hfull : ∃ w : pullback q (traitGenericSpec k') ⟶ pullback X₁.hom (𝟙 _), IsIso w ∧
      w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ w ≫ pullback.fst _ _ = M.ε)
    {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) :
    ∃ (Xc : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing)))
      (_ : LocallyOfFiniteType Xc.hom) (_ : QuasiCompact Xc.hom) (_ : IsSeparated Xc.hom)
      (_ : IsProper (CondensedRing.toPoint Xc).left) (Xc' : Over (Spec (.of k')))
      (_ : LocallyOfFiniteType Xc'.hom) (_ : QuasiCompact Xc'.hom) (_ : IsSeparated Xc'.hom)
      (_ : IsProper (CondensedRing.toPoint Xc').left) (Mc : NearbyCyclesModel Xc.left Xc'.left)
      (qc : Mc.total ⟶ trait k') (gc : Mc.generic ⟶ Spec (.of (traitGenericField k')))
      (_ : Mc.IsTraitModelOfGenericBase Xc (𝟙 _) qc gc) (_ : IsProper qc)
      (_ : IsPullback Mc.ε gc Xc.hom (traitGenericPointToSpec k' ≫ 𝟙 _))
      (b₁ : Xc ⟶ overProjectiveLine (point (FractionRing (PowerSeries k'))))
      (_ : IsProper b₁.left) (b₂ : Xc' ⟶ overProjectiveLine (point k')) (_ : IsProper b₂.left)
      (bc : Mc.Hom (projectiveLineModel k') b₁.left b₂.left)
      (_ : qc = bc.total ≫ (ProjectiveLine (trait k') ↘ trait k'))
      (_ : gc = bc.generic ≫
        (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k'))))
      (U : Mc.total.Opens) (_ : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
      (_ : QuasiCompact U.ι)
      (_ : LocallyOfFiniteType (Mc.restrictSpecialFibre U).hom)
      (_ : QuasiCompact (Mc.restrictSpecialFibre U).hom)
      (_ : IsSeparated (Mc.restrictSpecialFibre U).hom)
      (bW : (Mc.restrictOpen U).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
      (_ : bW ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = U.ι ≫ qc)
      (_ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
      (j : X₁ ⟶ Xc) (_ : IsOpenImmersion j.left) (j' : X' ⟶ Mc.restrictSpecialFibre U)
      (_ : IsOpenImmersion j'.left) (φ : M.Hom (Mc.restrictOpen U) j.left j'.left)
      (_ : IsOpenImmersion φ.total),
      IsPullback φ.generic M.j (Mc.restrictOpen U).j φ.total ∧ q = φ.total ≫ U.ι ≫ qc ∧
        g = φ.generic ≫ (Mc.j ⁻¹ᵁ U).ι ≫ gc ∧ φ.total ≫ bW = b := by
  obtain ⟨w, hw, hw₁, hw₂⟩ := hfull
  have hM := h.isTraitModelOver
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  let χ := coordChart (trait k')
  let πS := ProjectiveLine (trait k') ↘ trait k'
  -- the coordinate as a map to `ℙ¹_S`, and its compactification
  let f : M.total ⟶ ProjectiveLine (trait k') := b ≫ χ
  have hf : f ≫ πS = q := by
    simp only [f, πS, χ, Category.assoc, coordChart_over, hb]
  have : IsSeparated (f ≫ πS) := by rw [hf]; infer_instance
  have : IsSeparated f := IsSeparated.of_comp f πS
  have : LocallyOfFiniteType (f ≫ πS) := by rw [hf]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f πS
  have : QuasiCompact (f ≫ πS) := by rw [hf]; infer_instance
  have : QuasiCompact f := QuasiCompact.of_comp f πS
  have : CompactSpace (ProjectiveLine (trait k')) :=
    QuasiCompact.compactSpace_of_compactSpace πS
  have : QuasiSeparatedSpace (ProjectiveLine (trait k')) :=
    quasiSeparatedSpace_of_quasiSeparated πS
  let c := NagataCompactification f
  have hci : c.i ≫ c.g = f := c.comm.symm
  let qc : c.Z ⟶ trait k' := c.g ≫ πS
  have : IsProper qc := inferInstance
  have hciq : c.i ≫ qc = q := by rw [← Category.assoc, hci, hf]
  let Mc := traitFibreModel qc
  have hc := isTraitModelOfGenericBase_traitFibreModel qc
  have hcM := hc.isTraitModelOver
  -- the morphism of models `b̄ : M̄ ⟶ ℙ¹_S`
  let ιS := traitGenericSpec k'
  let γ := traitGenericPointToSpec k'
  have hγ : γ ≫ ιS = traitGenericPoint k' := traitGenericPointToSpec_traitGenericSpec k'
  have hPη := isPullback_map (ULift.{u} (Fin 2)) ιS
  have hPΩ := isPullback_map (ULift.{u} (Fin 2)) (traitGenericPoint k')
  have hPs := isPullback_map (ULift.{u} (Fin 2)) (traitClosedPoint k')
  let b₁l : pullback qc ιS ⟶ ProjectiveLine (Spec (.of (FractionRing (PowerSeries k')))) :=
    hPη.lift (pullback.fst _ _ ≫ c.g) (pullback.snd _ _) (by
      rw [Category.assoc]
      exact pullback.condition)
  let b₂l : pullback qc (traitClosedPoint k') ⟶ ProjectiveLine (Spec (.of k')) :=
    hPs.lift (pullback.fst _ _ ≫ c.g) (pullback.snd _ _) (by
      rw [Category.assoc]
      exact pullback.condition)
  let bgen : pullback qc (traitGenericPoint k') ⟶
      ProjectiveLine (Spec (.of (traitGenericField k'))) :=
    hPΩ.lift (pullback.fst _ _ ≫ c.g) (pullback.snd _ _) (by
      rw [Category.assoc]
      exact pullback.condition)
  let b₁ : traitGenericBase qc ⟶ overProjectiveLine (point (FractionRing (PowerSeries k'))) :=
    Over.homMk b₁l (by
      change b₁l ≫ (_ ↘ _ ≫ 𝟙 _) = _
      rw [Category.comp_id]
      exact hPη.lift_snd _ _ _)
  let b₂ : traitStdSpecialFibre qc ⟶ overProjectiveLine (point k') :=
    Over.homMk b₂l (by
      change b₂l ≫ (_ ↘ _ ≫ 𝟙 _) = _
      rw [Category.comp_id]
      exact hPs.lift_snd _ _ _)
  have hb₁ : IsPullback (pullback.fst qc ιS) b₁l c.g (ProjectiveSpace.map _ ιS) := by
    refine IsPullback.of_bot ?_ (hPη.lift_fst _ _ _).symm hPη
    rw [hPη.lift_snd]
    exact IsPullback.of_hasPullback qc ιS
  have hb₂ : IsPullback (pullback.fst qc (traitClosedPoint k')) b₂l c.g
      (ProjectiveSpace.map _ (traitClosedPoint k')) := by
    refine IsPullback.of_bot ?_ (hPs.lift_fst _ _ _).symm hPs
    rw [hPs.lift_snd]
    exact IsPullback.of_hasPullback qc (traitClosedPoint k')
  have hb₁p : IsProper b₁.left := MorphismProperty.of_isPullback hb₁ inferInstance
  have hb₂p : IsProper b₂.left := MorphismProperty.of_isPullback hb₂ inferInstance
  let bc : Mc.Hom (projectiveLineModel k') b₁.left b₂.left :=
    { total := c.g
      generic := bgen
      comm_j := hPΩ.lift_fst _ _ _
      comm_i := hPs.lift_fst _ _ _
      comm_ε := by
        change bgen ≫ ProjectiveSpace.map _ γ = Mc.ε ≫ b₁l
        apply hPη.hom_ext
        · rw [Category.assoc, Category.assoc, hPη.lift_fst, ← ProjectiveSpace.map_comp, hγ,
            traitFibreModel_ε, pullback.lift_fst_assoc]
          exact hPΩ.lift_fst _ _ _
        · rw [Category.assoc, Category.assoc, hPη.lift_snd, traitFibreModel_ε, pullback.lift_snd,
            ProjectiveSpace.map_over, ← Category.assoc, hPΩ.lift_snd] }
  have hbcg : pullback.snd qc (traitGenericPoint k') = bc.generic ≫
      (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘
        Spec (.of (traitGenericField k'))) := (hPΩ.lift_snd _ _ _).symm
  -- the open `U = b̄⁻¹(𝔸¹_S)` and its coordinate
  let O := χ.opensRange
  let U : Mc.total.Opens := c.g ⁻¹ᵁ O
  have hRU := isPullback_morphismRestrict c.g O
  have : QuasiCompact O.ι := by
    rw [← χ.isoOpensRange_inv_comp]
    infer_instance
  have hUqc : QuasiCompact U.ι := MorphismProperty.of_isPullback hRU inferInstance
  have hRj := isPullback_morphismRestrict Mc.j U
  have hRi := isPullback_morphismRestrict Mc.i U
  have : QuasiCompact (Mc.i ⁻¹ᵁ U).ι := MorphismProperty.of_isPullback hRi hUqc
  have hW := hc.restrictOpen U
  have hWM := hW.isTraitModelOver
  let bW : (Mc.restrictOpen U).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k') :=
    (c.g ∣_ O) ≫ χ.isoOpensRange.inv
  have hbWχ : bW ≫ χ = U.ι ≫ c.g := by
    change ((c.g ∣_ O) ≫ χ.isoOpensRange.inv) ≫ χ = _
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
    exact hRU.w
  have hbW : bW ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = U.ι ≫ qc := by
    rw [← coordChart_over, ← Category.assoc]
    change (bW ≫ χ) ≫ πS = _
    rw [hbWχ, Category.assoc]
  -- the open immersion of models `M ⟶ W`
  let φt : M.total ⟶ U := IsOpenImmersion.lift U.ι c.i (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change c.g (c.i y) ∈ O
    rw [← Scheme.Hom.comp_apply, hci]
    exact ⟨b y, rfl⟩)
  have hφU : φt ≫ U.ι = c.i := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion φt := IsOpenImmersion.of_comp φt U.ι
  have hbb : φt ≫ bW = b := by
    rw [← cancel_mono χ, Category.assoc, hbWχ, reassoc_of% hφU, hci]
  let genVc : M.generic ⟶ pullback qc (traitGenericPoint k') :=
    pullback.lift (M.j ≫ c.i) g (by rw [Category.assoc, hciq, hM.isPullback_j.w])
  let φg : M.generic ⟶ (Mc.restrictOpen U).generic :=
    hRj.lift (M.j ≫ φt) genVc (by
      rw [Category.assoc, hφU]
      exact (pullback.lift_fst _ _ _).symm)
  have hφg : φg ≫ (Mc.j ⁻¹ᵁ U).ι = genVc := hRj.lift_snd _ _ _
  let spVc : X'.left ⟶ pullback qc (traitClosedPoint k') :=
    pullback.lift (M.i ≫ c.i) X'.hom (by rw [Category.assoc, hciq, hM.isPullback_i.w])
  let j'l : X'.left ⟶ (Mc.restrictSpecialFibre U).left :=
    hRi.lift (M.i ≫ φt) spVc (by
      rw [Category.assoc, hφU]
      exact (pullback.lift_fst _ _ _).symm)
  let j' : X' ⟶ Mc.restrictSpecialFibre U :=
    Over.homMk j'l (by
      change j'l ≫ (Mc.i ⁻¹ᵁ U).ι ≫ pullback.snd _ _ = _
      rw [hRi.lift_snd_assoc]
      exact pullback.lift_snd _ _ _)
  let e : pullback q ιS ⟶ X₁.left := w ≫ pullback.fst _ _
  have : IsIso e := inferInstance
  have he : e ≫ X₁.hom = pullback.snd _ _ := by
    rw [Category.assoc, pullback.condition, Category.comp_id, hw₁]
  let pm : pullback q ιS ⟶ pullback qc ιS :=
    pullback.map _ _ _ _ c.i (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hciq]) (by simp)
  have hpm₁ : pm ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c.i := pullback.lift_fst _ _ _
  have hpm₂ : pm ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 _ := pullback.lift_snd _ _ _
  have : IsOpenImmersion pm := by
    have : IsOpenImmersion c.i := inferInstance
    infer_instance
  let j : X₁ ⟶ traitGenericBase qc :=
    Over.homMk (inv e ≫ pm) (by
      change (inv e ≫ pm) ≫ pullback.snd _ _ = _
      rw [Category.assoc, pullback.lift_snd, Category.comp_id, IsIso.inv_comp_eq, he])
  have hsε : genericFibreInclusion M q g hM.isPullback_j.w ≫ e = M.ε := hw₂
  let φ : M.Hom (Mc.restrictOpen U) j.left j'.left :=
    { total := φt
      generic := φg
      comm_j := hRj.lift_fst _ _ _
      comm_i := hRi.lift_fst _ _ _
      comm_ε := by
        change φg ≫ (Mc.j ⁻¹ᵁ U).ι ≫ Mc.ε = M.ε ≫ inv e ≫ pm
        rw [reassoc_of% hφg, ← hsε, Category.assoc, IsIso.hom_inv_id_assoc]
        apply pullback.hom_ext
        · rw [Category.assoc, traitFibreModel_ε, pullback.lift_fst, Category.assoc, hpm₁,
            genericFibreInclusion_fst_assoc]
          exact pullback.lift_fst _ _ _
        · rw [Category.assoc, traitFibreModel_ε, pullback.lift_snd, Category.assoc, hpm₂,
            Category.comp_id, genericFibreInclusion_snd]
          exact pullback.lift_snd_assoc _ _ _ _ }
  have hφq : q = φt ≫ U.ι ≫ qc := by rw [reassoc_of% hφU, hciq]
  have hφgq : g = φg ≫ (Mc.j ⁻¹ᵁ U).ι ≫ pullback.snd qc (traitGenericPoint k') := by
    rw [reassoc_of% hφg]
    exact (pullback.lift_snd _ _ _).symm
  have hφpb : IsPullback φg M.j (Mc.restrictOpen U).j φt := by
    refine IsPullback.of_right ?_ (hRj.lift_fst _ _ _) hWM.isPullback_j.flip
    rw [← hφgq, ← hφq]
    exact hM.isPullback_j.flip
  have hj'pb : IsPullback j'l M.i (Mc.restrictOpen U).i φt := by
    refine IsPullback.of_right ?_ (hRi.lift_fst _ _ _) hWM.isPullback_i.flip
    rw [← hφq]
    convert hM.isPullback_i.flip using 1
    exact Over.w j'
  have : IsOpenImmersion j'l := MorphismProperty.of_isPullback hj'pb.flip inferInstance
  refine ⟨traitGenericBase qc, inferInstance, inferInstance, inferInstance,
    isProper_toPoint_traitGenericBase qc, traitStdSpecialFibre qc, inferInstance, inferInstance,
    inferInstance, isProper_toPoint_traitStdSpecialFibre qc, Mc, qc, _, hc, inferInstance,
    isPullback_traitFibreModel_ε qc, b₁, hb₁p, b₂, hb₂p, bc, rfl, hbcg, U, rfl, hUqc,
    inferInstanceAs (LocallyOfFiniteType ((Mc.i ⁻¹ᵁ U).ι ≫ _)),
    inferInstanceAs (QuasiCompact ((Mc.i ⁻¹ᵁ U).ι ≫ _)),
    inferInstanceAs (IsSeparated ((Mc.i ⁻¹ᵁ U).ι ≫ _)), bW, hbW, hbWχ, j,
    inferInstanceAs (IsOpenImmersion (inv e ≫ pm)), j', ‹_›, φ, ‹_›, hφpb, hφq, hφgq, hbb⟩

end Compactification

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry

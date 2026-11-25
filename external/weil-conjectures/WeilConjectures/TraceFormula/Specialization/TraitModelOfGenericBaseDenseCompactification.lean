/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Dense
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseCompactification

/-!

# Dense compactification of trait models over a generic base

A variant of `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel` in which
the compactification `X̄₁` of the base `X₁` is dense: the open immersion `j : X₁ ⟶ X̄₁` has dense
image (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel_denseRange`).
The construction is the same, starting from the dense compactification
`AlgebraicGeometry.denseCompactification` of `X₁` over `F` instead of a Nagata compactification.

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {F : Type u} [Field F]

/-- **Dense compactification of trait models over a generic base**: a trait model `M` of `X₁`
over the generic base `(F, ι)` is an open sub-model of a trait model `M̄` of `X̄₁` over the generic
base `(F, ι)` with proper total space and proper `X̄₁`, `X̄'`, as in
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel`, where moreover the open
immersion `j : X₁ ⟶ X̄₁` has dense image: `X̄₁` is a dense compactification of `X₁`
(`AlgebraicGeometry.denseCompactification`). -/
theorem IsTraitModelOfGenericBase.exists_isProper_openSubmodel_denseRange
    {X₁ : Over (Spec (.of F))}
    [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
    {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X₁.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    ∃ (Xc : Over (Spec (.of F))) (_ : LocallyOfFiniteType Xc.hom) (_ : QuasiCompact Xc.hom)
      (_ : IsSeparated Xc.hom) (_ : IsProper (toPoint Xc).left) (Xc' : Over (Spec (.of k')))
      (_ : LocallyOfFiniteType Xc'.hom) (_ : QuasiCompact Xc'.hom) (_ : IsSeparated Xc'.hom)
      (_ : IsProper (toPoint Xc').left) (Mc : NearbyCyclesModel Xc.left Xc'.left)
      (qc : Mc.total ⟶ trait k') (gc : Mc.generic ⟶ Spec (.of (traitGenericField k')))
      (hMc : Mc.IsTraitModelOfGenericBase Xc ι qc gc)
      (_ : IsPullback Mc.ε gc Xc.hom (traitGenericPointToSpec k' ≫ ι))
      (_ : ∃ w : pullback qc (traitGenericSpec k') ⟶ pullback Xc.hom ι, IsIso w ∧
        w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        genericFibreInclusion Mc qc gc hMc.isTraitModelOver.isPullback_j.w ≫ w ≫
          pullback.fst _ _ = Mc.ε)
      (_ : IsProper qc) (j : X₁ ⟶ Xc) (_ : IsOpenImmersion j.left) (_ : DenseRange j.left)
      (j' : X' ⟶ Xc')
      (_ : IsOpenImmersion j'.left) (φ : M.Hom Mc j.left j'.left) (_ : IsOpenImmersion φ.total),
      IsPullback φ.generic M.j Mc.j φ.total ∧ q = φ.total ≫ qc ∧ g = φ.generic ≫ gc := by
  obtain ⟨w, hw, hw₁, hw₂⟩ := h.exists_openImmersion_genericFibre
  obtain ⟨u, hu, hu₁, hu₂⟩ := h.exists_openImmersion
  have hM := h.isTraitModelOver
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  -- the compactification `X̄₁` of `X₁` and the generic points of the trait
  let c₀ := denseCompactification X₁.hom
  have : IsSchemeTheoreticallyDominant c₀.i := denseCompactification_isDense X₁.hom
  have : QuasiCompact c₀.i := c₀.quasiCompact_openImmersion_iff.mpr inferInstance
  let Xc : Over (Spec (.of F)) := Over.mk c₀.g
  let ιS := traitGenericSpec k'
  let γ' := traitGenericPointToSpec k'
  have hγ : γ' ≫ ιS = traitGenericPoint k' := traitGenericPointToSpec_traitGenericSpec k'
  -- the open immersion of the generic fibre `𝒳_η` into `V = X̄₁ ×_F η`
  let jη : pullback X₁.hom ι ⟶ pullback Xc.hom ι :=
    pullback.map _ _ _ _ c₀.i (𝟙 _) (𝟙 _) ((Category.comp_id _).trans c₀.comm) (by simp)
  have hjη_fst : jη ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c₀.i := pullback.lift_fst _ _ _
  have hjη_snd : jη ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [pullback.lift_snd, Category.comp_id]
  have : IsProper Xc.hom := inferInstanceAs (IsProper c₀.g)
  have : IsOpenImmersion jη := by
    have : IsOpenImmersion c₀.i := inferInstance
    infer_instance
  obtain ⟨B, c, p, s, hc, hp, hcp, has, hps⟩ :=
    exists_isProper_isPullback_of_isProper (q := q) (ι := ιS) (F' := w ≫ jη)
      (r := pullback.snd Xc.hom ι) (IsPullback.of_hasPullback q ιS)
      (by rw [Category.assoc, hjη_snd, hw₁])
  -- the compactified model, with geometric generic fibre `X̄₁ ×_F Spec Ω`
  let Xc' : Over (Spec (.of k')) := Over.mk (pullback.snd p (traitClosedPoint k'))
  let bc := genericFibreBaseChangeMap k' Xc ι
  let Mc : NearbyCyclesModel Xc.left Xc'.left :=
    { total := B
      generic := pullback Xc.hom (γ' ≫ ι)
      j := bc ≫ s
      i := pullback.fst p (traitClosedPoint k')
      ε := pullback.fst _ _ }
  have hMcj : IsPullback (bc ≫ s) (pullback.snd _ _) p (traitGenericPoint k') := by
    rw [← hγ]
    exact (isPullback_genericFibreBaseChangeMap k' Xc ι).paste_horiz hps
  have hMc : Mc.IsTraitModelOver p (pullback.snd _ _) :=
    ⟨inferInstance, inferInstance, inferInstance, hMcj, IsPullback.of_hasPullback _ _⟩
  have hincl : genericFibreInclusion Mc p (pullback.snd _ _) hMc.isPullback_j.w =
      bc ≫ hps.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [genericFibreInclusion_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [genericFibreInclusion_snd, Category.assoc, IsPullback.isoPullback_hom_snd,
        genericFibreBaseChangeMap_snd]
  have hwc : genericFibreInclusion Mc p (pullback.snd _ _) hMc.isPullback_j.w ≫
      hps.isoPullback.inv ≫ pullback.fst _ _ = Mc.ε := by
    rw [hincl, Category.assoc, Iso.hom_inv_id_assoc, genericFibreBaseChangeMap_fst]
  have hMcG : Mc.IsTraitModelOfGenericBase Xc ι p (pullback.snd _ _) :=
    ⟨hMc, hps.isoPullback.inv, inferInstance, hps.isoPullback_inv_snd, hwc⟩
  -- the open immersions `j` and `j'`
  let j : X₁ ⟶ Xc := Over.homMk c₀.i c₀.comm.symm
  let j'l : X'.left ⟶ Xc'.left := pullback.lift (M.i ≫ c) X'.hom
    (by rw [Category.assoc, hcp, hM.isPullback_i.w])
  let j' : X' ⟶ Xc' := Over.homMk j'l (pullback.lift_snd _ _ _)
  have hj' : IsPullback j'l M.i Mc.i c := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback p (traitClosedPoint k')).flip
    rw [pullback.lift_snd, hcp]
    exact hM.isPullback_i.flip
  have hj'l : IsOpenImmersion j'l := MorphismProperty.of_isPullback hj'.flip hc
  -- the morphism of geometric generic fibres `X₁ ×_F Spec Ω ⟶ X̄₁ ×_F Spec Ω`
  let φgen : M.generic ⟶ pullback Xc.hom (γ' ≫ ι) := u ≫ pullback.map _ _ _ _ c₀.i (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans c₀.comm) (by rw [Category.comp_id, Category.id_comp])
  have hφfst : φgen ≫ pullback.fst _ _ = M.ε ≫ c₀.i := by
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hu₁]
  have hφsnd : φgen ≫ pullback.snd _ _ = g := by
    rw [Category.assoc, pullback.lift_snd, Category.comp_id, hu₂]
  have : IsOpenImmersion φgen := by
    have : IsOpenImmersion c₀.i := inferInstance
    infer_instance
  have hkey : φgen ≫ bc = genericFibreInclusion M q g hM.isPullback_j.w ≫ w ≫ jη := by
    apply pullback.hom_ext
    · rw [Category.assoc, genericFibreBaseChangeMap_fst, hφfst, Category.assoc, Category.assoc,
        hjη_fst, reassoc_of% hw₂]
    · rw [Category.assoc, genericFibreBaseChangeMap_snd, reassoc_of% hφsnd, Category.assoc,
        Category.assoc, hjη_snd, hw₁, genericFibreInclusion_snd]
  have hcomm_j : φgen ≫ bc ≫ s = M.j ≫ c := by
    rw [reassoc_of% hkey, ← Category.assoc w, ← has, genericFibreInclusion_fst_assoc]
  let φ : M.Hom Mc j.left j'.left :=
    { total := c
      generic := φgen
      comm_j := hcomm_j
      comm_i := pullback.lift_fst _ _ _
      comm_ε := hφfst }
  refine ⟨Xc, inferInstance, inferInstance, inferInstance,
    by simp only [toPoint_left]
       infer_instance,
    Xc',
    inferInstanceAs (LocallyOfFiniteType (pullback.snd p (traitClosedPoint k'))),
    inferInstanceAs (QuasiCompact (pullback.snd p (traitClosedPoint k'))),
    inferInstanceAs (IsSeparated (pullback.snd p (traitClosedPoint k'))),
    by simp only [toPoint_left]
       exact inferInstanceAs (IsProper (pullback.snd p (traitClosedPoint k'))),
    Mc, p, pullback.snd _ _, hMcG, IsPullback.of_hasPullback _ _,
    ⟨hps.isoPullback.inv, inferInstance, hps.isoPullback_inv_snd, hwc⟩, hp, j,
    inferInstanceAs (IsOpenImmersion c₀.i), c₀.i.denseRange, j', hj'l, φ, hc, ?_, hcp.symm,
    hφsnd.symm⟩
  refine IsPullback.of_right ?_ hcomm_j hMcj.flip
  rw [hφsnd, hcp]
  exact hM.isPullback_j.flip

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry

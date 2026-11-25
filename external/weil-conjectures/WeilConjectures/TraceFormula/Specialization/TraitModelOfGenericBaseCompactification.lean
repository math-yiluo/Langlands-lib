/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase

/-!

# Compactification of trait models over a generic base

Let `S = Spec k'⟦t⟧` be the trait and `η = Spec Frac k'⟦t⟧ ⟶ S` its generic point, an open
immersion. Every trait model `M` of `X₁` over the generic base `(F, ι : η ⟶ Spec F)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`) is an open sub-model of a trait model over the
generic base with proper total space, proper `X̄₁` and proper special fibre `X̄'`, whose generic
fibre is all of `X̄₁ ×_F η`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel`).

Construction: let `X̄₁` be a Nagata compactification of `X₁` over `F` and `V = X̄₁ ×_F η`, a
proper `η`-scheme containing the generic fibre `𝒳_η` as an open. Gluing `𝒳` and `V` along `𝒳_η`
gives a separated `S`-scheme of finite type, since the graph of `𝒳_η ⟶ V` over `η` is closed. A
dense compactification of the glued scheme over `S` has generic fibre `V`: the section
`V ⟶ B ×_S η` is an open immersion which is universally closed with dense image
(`AlgebraicGeometry.exists_isProper_isPullback_of_isProper`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable {S A A' E V : Scheme.{u}} {q : A ⟶ S} {ι : E ⟶ S} {a : A' ⟶ A} {pη : A' ⟶ E}
  {F' : A' ⟶ V} {r : V ⟶ E}

/-- **Compactification extending a proper scheme over an open.** Let `q : A ⟶ S` be separated,
quasi-compact and locally of finite type over a quasi-compact quasi-separated scheme `S`, let
`ι : E ⟶ S` be a quasi-compact open immersion with inverse image `A' = A ×_S E`, and let
`F' : A' ⟶ V` be an open immersion over `E` into a proper `E`-scheme `r : V ⟶ E`. Then there are
an open immersion `c : A ⟶ B` and a proper morphism `p : B ⟶ S` with `c ≫ p = q`, and a morphism
`s : V ⟶ B` extending `c` on `A'` which identifies `V` with the inverse image `B ×_S E`.

The scheme `B` is a dense compactification of the gluing of `A` and `V` along `A'`, which is
separated over `S` as the graph of `F'` over `E` is closed. -/
theorem exists_isProper_isPullback_of_isProper [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated q] [QuasiCompact q] [LocallyOfFiniteType q] [IsOpenImmersion ι] [QuasiCompact ι]
    [IsOpenImmersion F'] [IsProper r] (H : IsPullback a pη q ι) (hr : F' ≫ r = pη) :
    ∃ (B : Scheme.{u}) (c : A ⟶ B) (p : B ⟶ S) (s : V ⟶ B), IsOpenImmersion c ∧ IsProper p ∧
      c ≫ p = q ∧ a ≫ c = F' ≫ s ∧ IsPullback s r p ι := by
  have : IsOpenImmersion a := MorphismProperty.of_isPullback H.flip inferInstance
  have w : a ≫ q = F' ≫ r ≫ ι := by rw [H.w, ← hr, Category.assoc]
  -- the graph of `F'` over `E` is a closed immersion: a section of `A' ×_E V ⟶ A'`
  have hgraph : IsClosedImmersion (pullback.lift a F' w) := by
    let π : pullback q (r ≫ ι) ⟶ A' := H.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r)
      (by rw [pullback.condition, Category.assoc])
    have hπ : IsPullback π (pullback.snd q (r ≫ ι)) pη r := by
      refine IsPullback.of_right ?_ (H.lift_snd _ _ _) H
      rw [H.lift_fst]
      exact IsPullback.of_hasPullback q (r ≫ ι)
    have : IsSeparated π := MorphismProperty.of_isPullback hπ.flip inferInstance
    have hid : pullback.lift a F' w ≫ π = 𝟙 A' := by
      refine H.hom_ext ?_ ?_
      · rw [Category.assoc, H.lift_fst, pullback.lift_fst, Category.id_comp]
      · rw [Category.assoc, H.lift_snd, pullback.lift_snd_assoc, hr, Category.id_comp]
    have : IsClosedImmersion (pullback.lift a F' w ≫ π) := by
      rw [hid]
      infer_instance
    exact IsClosedImmersion.of_comp (pullback.lift a F' w) π
  have : IsSeparated (pushout.desc q (r ≫ ι) w) := IsSeparated.pushout_desc a F' w hgraph
  have : QuasiCompact (pushout.desc q (r ≫ ι) w) := QuasiCompact.pushout_desc a F' w
  have : LocallyOfFiniteType (pushout.desc q (r ≫ ι) w) :=
    IsZariskiLocalAtSource.pushout_desc a F' w ‹_› inferInstance
  let c₁ := denseCompactification (pushout.desc q (r ≫ ι) w)
  have : IsSchemeTheoreticallyDominant c₁.i := denseCompactification_isDense _
  have : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion_iff.mpr inferInstance
  refine ⟨c₁.Z, pushout.inl a F' ≫ c₁.i, c₁.g, pushout.inr a F' ≫ c₁.i, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← c₁.comm, pushout.inl_desc]
  · rw [pushout.condition_assoc]
  have hs : (pushout.inr a F' ≫ c₁.i) ≫ c₁.g = r ≫ ι := by
    rw [Category.assoc, ← c₁.comm, pushout.inr_desc]
  let l : V ⟶ pullback c₁.g ι := pullback.lift _ _ hs
  have : IsOpenImmersion (l ≫ pullback.fst c₁.g ι) := by
    rw [pullback.lift_fst]
    infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (pullback.fst c₁.g ι)
  have : UniversallyClosed (l ≫ pullback.snd c₁.g ι) := by
    rw [pullback.lift_snd]
    infer_instance
  have : UniversallyClosed l := UniversallyClosed.of_comp_of_isSeparated l (pullback.snd c₁.g ι)
  -- the range of `l` is dense: a point of `B ×_S E` in the glued scheme comes from `V`
  have hdense : Dense (Set.range l) := by
    refine (c₁.i.denseRange.preimage (pullback.fst c₁.g ι).isOpenEmbedding.isOpenMap).mono ?_
    rintro x ⟨y, hxy⟩
    obtain ⟨v, rfl⟩ : ∃ v, pushout.inr a F' v = y := by
      have hy : y ∈ Set.range (pushout.inl a F') ∪ Set.range (pushout.inr a F') := by
        rw [range_pushout_inl_union_range_pushout_inr]
        trivial
      obtain ⟨b, rfl⟩ | h := hy
      · have hb : q b = ι (pullback.snd c₁.g ι x) := by
          rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, ← hxy,
            ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← c₁.comm, pushout.inl_desc]
        obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hb
        refine ⟨F' (H.isoPullback.inv z), ?_⟩
        rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply,
          ← Scheme.Hom.comp_apply H.isoPullback.inv a, H.isoPullback_inv_fst, hz]
      · exact h
    refine ⟨v, (pullback.fst c₁.g ι).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hxy]
  have hsurj : Function.Surjective l := by
    rw [← Set.range_eq_univ, ← l.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_eq
  have : IsIso l := (isIso_iff_isOpenImmersion_and_surjective l).2 ⟨inferInstance, ⟨hsurj⟩⟩
  exact IsPullback.of_iso_pullback ⟨hs⟩ (asIso l) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {k' : Type u} [Field k'] {F : Type u} [Field F]

/-- **Compactification of trait models over a generic base**: a trait model `M` of `X₁` over the
generic base `(F, ι)` is an open sub-model of a trait model `M̄` of `X̄₁` over the generic base
`(F, ι)` with proper total space and proper `X̄₁`, `X̄'`, over open immersions `j : X₁ ⟶ X̄₁` and
`j' : X' ⟶ X̄'`, in the sense of `NearbyCyclesModel.isIso_nearbyDualityMap_of_openSubmodel`. The
generic fibre of `M̄` is all of `X̄₁ ×_F η`, and its geometric generic fibre is all of
`X̄₁ ×_F Spec Ω` (a pullback square). -/
theorem IsTraitModelOfGenericBase.exists_isProper_openSubmodel {X₁ : Over (Spec (.of F))}
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
      (_ : IsProper qc) (j : X₁ ⟶ Xc) (_ : IsOpenImmersion j.left) (j' : X' ⟶ Xc')
      (_ : IsOpenImmersion j'.left) (φ : M.Hom Mc j.left j'.left) (_ : IsOpenImmersion φ.total),
      IsPullback φ.generic M.j Mc.j φ.total ∧ q = φ.total ≫ qc ∧ g = φ.generic ≫ gc := by
  obtain ⟨w, hw, hw₁, hw₂⟩ := h.exists_openImmersion_genericFibre
  obtain ⟨u, hu, hu₁, hu₂⟩ := h.exists_openImmersion
  have hM := h.isTraitModelOver
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  -- the compactification `X̄₁` of `X₁` and the generic points of the trait
  let c₀ := NagataCompactification X₁.hom
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
    inferInstanceAs (IsOpenImmersion c₀.i), j', hj'l, φ, hc, ?_, hcp.symm, hφsnd.symm⟩
  refine IsPullback.of_right ?_ hcomm_j hMcj.flip
  rw [hφsnd, hcp]
  exact hM.isPullback_j.flip

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry

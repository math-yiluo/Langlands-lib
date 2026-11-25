/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.Compactification.ExtensionOverOpen
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseRefinement

/-!

# Common refinements of compactifications of trait models over a generic base

Any two compactifications of a trait model `N` over a generic base `(F, ι : η ⟶ Spec F)` have a
common refinement
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.exists_refinement`), as for trait
models over a base field
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`). This is the common
refinement of the proof of blueprint `prose-E-15` ("two compactifications have a
common proper refinement").

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfGenericBase

variable {F : Type u} [Field F] {k' : Type u} [Field k']
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {Y : Over (Spec (.of F))} {Y' : Over (Spec (.of k'))}
  {N : NearbyCyclesModel Y.left Y'.left} {q : N.total ⟶ trait k'}
  {g : N.generic ⟶ Spec (.of (traitGenericField k'))} {h : N.IsTraitModelOfGenericBase Y ι q g}

/-- **Common refinement of two compactifications** (the first step of the proof of blueprint
`prose-E-15`): any two compactifications `C₁`, `C₂` of a trait model over a generic
base have a common refinement `C₃`.

Construction: with `X₃` the closure of the graph of `Y` in `X₁ ×_F X₂`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.exists_common`), the generic fibre
`V = X₃ ×_F η` is a closed subscheme of `W ×_S η`, `W = 𝒳₁ ×_S 𝒳₂`, through
`Xᵢ ×_F η ≅ 𝒳ᵢ ×_S η` (it is proper over `η` and a monomorphism, `X₃ ⟶ X₁ ×_F X₂` being one).
Glue the total space of `N` and `V` along `N_η` and compactify over `W`
(`AlgebraicGeometry.exists_isProper_isPullback_of_isClosedImmersion`); the compactification is
`V` over the generic point, and the inclusion of `N` is the inverse image of `N ⊆ 𝒳ᵢ`, as `N_η`
is the inverse image of `N` in `V`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.isPullback_genericFibre`). -/
theorem Compactification.exists_refinement (C₁ C₂ : h.Compactification) :
    ∃ C₃ : h.Compactification, Nonempty (C₃.Refinement C₁) ∧ Nonempty (C₃.Refinement C₂) := by
  have hN := h.isTraitModelOver
  have := hN.locallyOfFiniteType
  have := hN.quasiCompact
  have := hN.isSeparated
  obtain ⟨wN, hwN, hwN₁, hwN₂⟩ := h.exists_openImmersion_genericFibre
  obtain ⟨w₁, hw₁, hw₁₁, hw₁₂⟩ := C₁.exists_isIso_genericFibre
  obtain ⟨w₂, hw₂, hw₂₁, hw₂₂⟩ := C₂.exists_isIso_genericFibre
  obtain ⟨X₃, _, ι₃, _, p₁, p₂, _, _, hι₁, hι₂, hιpb₁, hιpb₂, hmono⟩ :=
    Compactification.exists_common C₁ C₂
  -- `W = 𝒳₁ ×_S 𝒳₂`, proper over `S`
  let zW : pullback C₁.qc C₂.qc ⟶ trait k' := pullback.fst C₁.qc C₂.qc ≫ C₁.qc
  let pr₁ : pullback C₁.qc C₂.qc ⟶ C₁.model.total := pullback.fst C₁.qc C₂.qc
  let pr₂ : pullback C₁.qc C₂.qc ⟶ C₂.model.total := pullback.snd C₁.qc C₂.qc
  have hpr₂ : pr₂ ≫ C₂.qc = zW := pullback.condition.symm
  have : IsProper zW := inferInstanceAs (IsProper (pullback.fst C₁.qc C₂.qc ≫ C₁.qc))
  have := QuasiCompact.compactSpace_of_compactSpace zW
  have := quasiSeparatedSpace_of_quasiSeparated zW
  -- the morphism `Fm : 𝒩 ⟶ W`
  let Fm : N.total ⟶ pullback C₁.qc C₂.qc :=
    pullback.lift C₁.hom.total C₂.hom.total (by rw [← C₁.q_eq, ← C₂.q_eq])
  have hF₁ : Fm ≫ pr₁ = C₁.hom.total := pullback.lift_fst _ _ _
  have hF₂ : Fm ≫ pr₂ = C₂.hom.total := pullback.lift_snd _ _ _
  have hFz : Fm ≫ zW = q := by rw [← Category.assoc, hF₁, ← C₁.q_eq]
  have : QuasiCompact Fm := by
    have : QuasiCompact (Fm ≫ zW) := by
      rw [hFz]
      infer_instance
    exact QuasiCompact.of_comp Fm zW
  have : IsSeparated Fm := by
    have : IsSeparated (Fm ≫ zW) := by
      rw [hFz]
      infer_instance
    exact IsSeparated.of_comp Fm zW
  have : LocallyOfFiniteType Fm := by
    have : LocallyOfFiniteType (Fm ≫ zW) := by
      rw [hFz]
      infer_instance
    exact locallyOfFiniteType_of_comp Fm zW
  -- the generic fibre `V = X₃ ×_F η` and the open immersion `N_η ⟶ V`
  let F' : pullback q (traitGenericSpec k') ⟶ pullback X₃.hom ι := wN ≫ overBaseChangeMap ι ι₃
  have hF'snd : F' ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [Category.assoc, overBaseChangeMap_snd, hwN₁]
  have hQ₁ := C₁.isPullback_genericFibre hwN₁ hwN₂ hw₁₁ hw₁₂ hιpb₁
  have hQ₂ := C₂.isPullback_genericFibre hwN₁ hwN₂ hw₂₁ hw₂₂ hιpb₂
  have hinv₁ : inv w₁ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [← hw₁₁, IsIso.inv_hom_id_assoc]
  have hinv₂ : inv w₂ ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [← hw₂₁, IsIso.inv_hom_id_assoc]
  have hp₁K : overBaseChangeMap ι p₁ ≫ inv w₁ ≫ pullback.fst _ _ ≫ C₁.qc =
      pullback.snd _ _ ≫ traitGenericSpec k' := by
    rw [pullback.condition, reassoc_of% hinv₁, overBaseChangeMap_snd_assoc]
  have hp₂K : overBaseChangeMap ι p₂ ≫ inv w₂ ≫ pullback.fst _ _ ≫ C₂.qc =
      pullback.snd _ _ ≫ traitGenericSpec k' := by
    rw [pullback.condition, reassoc_of% hinv₂, overBaseChangeMap_snd_assoc]
  let κW : pullback X₃.hom ι ⟶ pullback C₁.qc C₂.qc :=
    pullback.lift (overBaseChangeMap ι p₁ ≫ inv w₁ ≫ pullback.fst _ _)
      (overBaseChangeMap ι p₂ ≫ inv w₂ ≫ pullback.fst _ _) (by
        simp only [Category.assoc, hp₁K, hp₂K])
  have hκW₁ : κW ≫ pr₁ = overBaseChangeMap ι p₁ ≫ inv w₁ ≫ pullback.fst _ _ :=
    pullback.lift_fst _ _ _
  have hκW₂ : κW ≫ pr₂ = overBaseChangeMap ι p₂ ≫ inv w₂ ≫ pullback.fst _ _ :=
    pullback.lift_snd _ _ _
  have hκWz : κW ≫ zW = pullback.snd _ _ ≫ traitGenericSpec k' := by
    rw [← Category.assoc, hκW₁, Category.assoc, Category.assoc, hp₁K]
  let κ : pullback X₃.hom ι ⟶ pullback zW (traitGenericSpec k') :=
    pullback.lift κW (pullback.snd _ _) hκWz
  have hκfst : κ ≫ pullback.fst _ _ = κW := pullback.lift_fst _ _ _
  have hκsnd : κ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  -- `V ⟶ W ×_S η` is a closed immersion: it is proper and a monomorphism
  have : IsClosedImmersion κ := by
    rw [IsClosedImmersion.iff_isProper_and_mono]
    refine ⟨?_, ⟨fun {T} a b hab ↦ ?_⟩⟩
    · have : IsProper (κ ≫ pullback.snd zW (traitGenericSpec k')) := by
        rw [hκsnd]
        infer_instance
      exact IsProper.of_comp κ (pullback.snd zW (traitGenericSpec k'))
    · have hsnd : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _ := by
        rw [← hκsnd, reassoc_of% hab]
      have hK₁ : a ≫ overBaseChangeMap ι p₁ = b ≫ overBaseChangeMap ι p₁ := by
        rw [← cancel_mono (inv w₁)]
        apply pullback.hom_ext
        · have := congrArg (· ≫ pullback.fst _ _ ≫ pr₁) hab
          simp only [Category.assoc] at this
          rw [reassoc_of% hκfst, hκW₁] at this
          simpa only [Category.assoc] using this
        · rw [Category.assoc, Category.assoc, hinv₁, overBaseChangeMap_snd, Category.assoc,
            Category.assoc, hinv₁, overBaseChangeMap_snd, hsnd]
      have hK₂ : a ≫ overBaseChangeMap ι p₂ = b ≫ overBaseChangeMap ι p₂ := by
        rw [← cancel_mono (inv w₂)]
        apply pullback.hom_ext
        · have := congrArg (· ≫ pullback.fst _ _ ≫ pr₂) hab
          simp only [Category.assoc] at this
          rw [reassoc_of% hκfst, hκW₂] at this
          simpa only [Category.assoc] using this
        · rw [Category.assoc, Category.assoc, hinv₂, overBaseChangeMap_snd, Category.assoc,
            Category.assoc, hinv₂, overBaseChangeMap_snd, hsnd]
      apply pullback.hom_ext _ hsnd
      refine hmono _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, ← overBaseChangeMap_fst, reassoc_of% hK₁]
      · rw [Category.assoc, Category.assoc, ← overBaseChangeMap_fst, reassoc_of% hK₂]
  -- `N ×_S η` is the inverse image of `V ⊆ W ×_S η` in `N`
  have H : IsPullback (pullback.fst q (traitGenericSpec k')) (F' ≫ κ) Fm
      (pullback.fst zW (traitGenericSpec k')) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback zW (traitGenericSpec k'))
    · rw [Category.assoc, hκsnd, hF'snd, hFz]
      exact IsPullback.of_hasPullback q (traitGenericSpec k')
    · rw [Category.assoc, hκfst]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc]
        exact (congrArg (_ ≫ ·) hF₁).trans (hQ₁.w.symm.trans (congrArg (F' ≫ ·) hκW₁.symm))
      · rw [Category.assoc, Category.assoc]
        exact (congrArg (_ ≫ ·) hF₂).trans (hQ₂.w.symm.trans (congrArg (F' ≫ ·) hκW₂.symm))
  have : IsOpenImmersion F' := inferInstanceAs (IsOpenImmersion (wN ≫ overBaseChangeMap ι ι₃))
  -- the compactification `B` of `𝒩 ∪ V` over `W`, which is `V` over `η`
  obtain ⟨B, c, p, s, hc, hp, hcp, has, hps, hdense⟩ :=
    exists_isProper_isPullback_of_isClosedImmersion H
  have : IsOpenImmersion c := hc
  have : IsProper p := hp
  let qc : B ⟶ trait k' := p ≫ zW
  have hqcP : IsProper qc := inferInstanceAs (IsProper (p ≫ zW))
  have hqc : q = c ≫ qc := by rw [← hFz, ← hcp, Category.assoc]
  have hsp₁ : s ≫ p ≫ pr₁ = overBaseChangeMap ι p₁ ≫ inv w₁ ≫ pullback.fst _ _ := by
    rw [reassoc_of% hps.w, reassoc_of% hκfst, hκW₁]
  have hsp₂ : s ≫ p ≫ pr₂ = overBaseChangeMap ι p₂ ≫ inv w₂ ≫ pullback.fst _ _ := by
    rw [reassoc_of% hps.w, reassoc_of% hκfst, hκW₂]
  have hsη : IsPullback s (pullback.snd _ _) qc (traitGenericSpec k') := by
    have h₂ := hps.paste_vert (IsPullback.of_hasPullback zW (traitGenericSpec k'))
    rwa [hκsnd] at h₂
  have hcj : pullback.lift (N.ε ≫ ι₃.left) g (by rw [Category.assoc, Over.w ι₃, h.ε_hom]) ≫
      genericFibreBaseChangeMap k' X₃ ι ≫ s = N.j ≫ c := by
    have hlift : pullback.lift (N.ε ≫ ι₃.left) g (by rw [Category.assoc, Over.w ι₃, h.ε_hom]) ≫
        genericFibreBaseChangeMap k' X₃ ι =
          genericFibreInclusion N q g hN.isPullback_j.w ≫ F' := by
      apply pullback.hom_ext
      · rw [Category.assoc, genericFibreBaseChangeMap_fst, pullback.lift_fst, Category.assoc,
          Category.assoc, overBaseChangeMap_fst, reassoc_of% hwN₂]
      · rw [Category.assoc, genericFibreBaseChangeMap_snd, pullback.lift_snd_assoc,
          Category.assoc, hF'snd, genericFibreInclusion_snd]
    rw [reassoc_of% hlift, ← has, genericFibreInclusion_fst_assoc]
  let C₃ : h.Compactification := Compactification.ofIsPullback ι₃ c qc s hsη hqc hcj
  -- the refinements `C₃ ⟶ C₁` and `C₃ ⟶ C₂`
  have hsep₁ : IsSeparated (p ≫ pr₁) := by
    have : IsSeparated ((p ≫ pr₁) ≫ C₁.qc) := by
      rw [Category.assoc]
      exact hqcP.toIsSeparated
    exact IsSeparated.of_comp _ C₁.qc
  have hsep₂ : IsSeparated (p ≫ pr₂) := by
    have : IsSeparated ((p ≫ pr₂) ≫ C₂.qc) := by
      rw [Category.assoc, hpr₂]
      exact hqcP.toIsSeparated
    exact IsSeparated.of_comp _ C₂.qc
  have htot₁ : c ≫ p ≫ pr₁ = C₁.hom.total := by rw [← Category.assoc, hcp, hF₁]
  have htot₂ : c ≫ p ≫ pr₂ = C₂.hom.total := by rw [← Category.assoc, hcp, hF₂]
  have hpb₁ : IsPullback c (𝟙 N.total) (p ≫ pr₁) C₁.hom.total := by
    refine isPullback_id_of_dense htot₁ hdense ?_
    rintro b (hb | ⟨v, rfl⟩) hπb
    · exact hb
    · obtain ⟨n, hn⟩ := Scheme.Pullback.mem_range_fst_of_isPullback hQ₁ (x := v) (by
        rwa [← hsp₁, Scheme.Hom.comp_apply])
      exact ⟨_, by rw [← Scheme.Hom.comp_apply, has, Scheme.Hom.comp_apply, hn]⟩
  have hpb₂ : IsPullback c (𝟙 N.total) (p ≫ pr₂) C₂.hom.total := by
    refine isPullback_id_of_dense htot₂ hdense ?_
    rintro b (hb | ⟨v, rfl⟩) hπb
    · exact hb
    · obtain ⟨n, hn⟩ := Scheme.Pullback.mem_range_fst_of_isPullback hQ₂ (x := v) (by
        rwa [← hsp₂, Scheme.Hom.comp_apply])
      exact ⟨_, by rw [← Scheme.Hom.comp_apply, has, Scheme.Hom.comp_apply, hn]⟩
  -- the morphisms of geometric generic fibres `X₃ ×_F Spec Ω ⟶ Xᵢ ×_F Spec Ω`
  let πg₁ : C₃.model.generic ⟶ C₁.model.generic := C₁.isPullback_ε.lift
    (pullback.fst _ _ ≫ p₁.left) (pullback.snd _ _)
    (by rw [Category.assoc, Over.w p₁, pullback.condition])
  let πg₂ : C₃.model.generic ⟶ C₂.model.generic := C₂.isPullback_ε.lift
    (pullback.fst _ _ ≫ p₂.left) (pullback.snd _ _)
    (by rw [Category.assoc, Over.w p₂, pullback.condition])
  have hincl₁ : πg₁ ≫ genericFibreInclusion C₁.model C₁.qc C₁.gc
      C₁.isTraitModelOfGenericBase.isTraitModelOver.isPullback_j.w ≫ w₁ =
        genericFibreBaseChangeMap k' X₃ ι ≫ overBaseChangeMap ι p₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hw₁₂, C₁.isPullback_ε.lift_fst, Category.assoc,
        overBaseChangeMap_fst, genericFibreBaseChangeMap_fst_assoc]
    · rw [Category.assoc, Category.assoc, hw₁₁, genericFibreInclusion_snd,
        C₁.isPullback_ε.lift_snd_assoc, Category.assoc, overBaseChangeMap_snd,
        genericFibreBaseChangeMap_snd]
  have hincl₂ : πg₂ ≫ genericFibreInclusion C₂.model C₂.qc C₂.gc
      C₂.isTraitModelOfGenericBase.isTraitModelOver.isPullback_j.w ≫ w₂ =
        genericFibreBaseChangeMap k' X₃ ι ≫ overBaseChangeMap ι p₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hw₂₂, C₂.isPullback_ε.lift_fst, Category.assoc,
        overBaseChangeMap_fst, genericFibreBaseChangeMap_fst_assoc]
    · rw [Category.assoc, Category.assoc, hw₂₁, genericFibreInclusion_snd,
        C₂.isPullback_ε.lift_snd_assoc, Category.assoc, overBaseChangeMap_snd,
        genericFibreBaseChangeMap_snd]
  have hπg₁ : πg₁ ≫ C₁.model.j = (genericFibreBaseChangeMap k' X₃ ι ≫ s) ≫ p ≫ pr₁ := by
    rw [Category.assoc, hsp₁, ← reassoc_of% hincl₁, IsIso.hom_inv_id_assoc,
      genericFibreInclusion_fst]
  have hπg₂ : πg₂ ≫ C₂.model.j = (genericFibreBaseChangeMap k' X₃ ι ≫ s) ≫ p ≫ pr₂ := by
    rw [Category.assoc, hsp₂, ← reassoc_of% hincl₂, IsIso.hom_inv_id_assoc,
      genericFibreInclusion_fst]
  exact ⟨C₃, Compactification.nonempty_refinement (C₃ := C₃) p₁ hι₁ hιpb₁ (p ≫ pr₁) htot₁
      (Category.assoc _ _ _).symm πg₁ hπg₁
      (C₁.isPullback_ε.lift_snd _ _ _) (C₁.isPullback_ε.lift_fst _ _ _) hpb₁,
    Compactification.nonempty_refinement (C₃ := C₃) p₂ hι₂ hιpb₂ (p ≫ pr₂) htot₂
      ((congrArg (p ≫ ·) hpr₂).symm.trans (Category.assoc _ _ _).symm) πg₂ hπg₂
      (C₂.isPullback_ε.lift_snd _ _ _) (C₂.isPullback_ε.lift_fst _ _ _) hpb₂⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfGenericBase

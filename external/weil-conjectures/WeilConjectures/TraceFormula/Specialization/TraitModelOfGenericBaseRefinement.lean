/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseCompactification

/-!

# Compactifications of trait models over a generic base and their refinements

Let `S = Spec k'⟦t⟧` be the trait, `η` its generic point and `N` a trait model of an `F`-scheme
`Y` over the generic base `(F, ι : η ⟶ Spec F)` (`NearbyCyclesModel.IsTraitModelOfGenericBase`).
A *compactification* of `N` (`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification`) is a
trait model `P` over the generic base of a proper `F`-scheme `X`, with proper total space over
`S`, proper special fibre, generic fibre all of `X ×_F η` and geometric generic fibre all of
`X ×_F Spec Ω`, containing `N` as an open sub-model over open immersions `Y ⟶ X` and `Y' ⟶ X'`.
Compactifications exist
(`NearbyCyclesModel.IsTraitModelOfGenericBase.nonempty_compactification`, from
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel`).

A *refinement* `C₃ ⟶ C₁` of compactifications
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.Refinement`) is a morphism of
models `P₃ ⟶ P₁` over proper morphisms `X₃ ⟶ X₁`, `X₃' ⟶ X₁'`, compatible with the inclusions of
`N`, over which `N` is cartesian. Any two compactifications have a common refinement
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.exists_refinement`, in
`TraceFormula.Specialization.TraitModelOfGenericBaseCommonRefinement`). This is the common
refinement of the proof of blueprint `prose-E-15` ("two compactifications
have a common proper refinement"), as for trait models over a base field
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`).

The common refinement is built as over a base field, with `X₃` the closure of the graph of `Y` in
`X₁ ×_F X₂`: the total space of `N` and the generic fibre `X₃ ×_F η` are glued along `N_η` and
compactified over `𝒳₁ ×_S 𝒳₂`. Over a generic base there is no morphism from the total spaces to
the bases; instead the generic fibres `𝒳ᵢ ×_S η ≅ Xᵢ ×_F η` are used: `X₃ ×_F η` is a closed
subscheme of `(𝒳₁ ×_S 𝒳₂) ×_S η`, being proper and a monomorphism, and `N_η` is the inverse image
of `N` in `X₃ ×_F η`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.isPullback_genericFibre`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section BaseChangeOver

variable {B E : Scheme.{u}} (ι : E ⟶ B)

/-- The base change `X ×_B E ⟶ Y ×_B E` along `ι : E ⟶ B` of a morphism `f : X ⟶ Y` over `B`. -/
noncomputable def overBaseChangeMap {X Y : Over B} (f : X ⟶ Y) :
    pullback X.hom ι ⟶ pullback Y.hom ι :=
  pullback.map _ _ _ _ f.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Over.w f])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma overBaseChangeMap_fst {X Y : Over B} (f : X ⟶ Y) :
    overBaseChangeMap ι f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma overBaseChangeMap_snd {X Y : Over B} (f : X ⟶ Y) :
    overBaseChangeMap ι f ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [overBaseChangeMap, pullback.lift_snd, Category.comp_id]

@[simp]
lemma overBaseChangeMap_id (X : Over B) : overBaseChangeMap ι (𝟙 X) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

instance {X Y : Over B} (f : X ⟶ Y) [IsOpenImmersion f.left] :
    IsOpenImmersion (overBaseChangeMap ι f) := by
  rw [overBaseChangeMap]
  infer_instance

/-- The base change along `ι` of a morphism `f` over `B` is the base change of `f.left`. -/
lemma isPullback_overBaseChangeMap {X Y : Over B} (f : X ⟶ Y) :
    IsPullback (pullback.fst _ _) (overBaseChangeMap ι f) f.left (pullback.fst _ _) := by
  refine IsPullback.of_bot ?_ (overBaseChangeMap_fst ι f).symm (IsPullback.of_hasPullback _ _)
  rw [overBaseChangeMap_snd, Over.w f]
  exact IsPullback.of_hasPullback _ _

/-- The base change along `ι` of a cartesian square of morphisms over `B` is cartesian. -/
lemma IsPullback.overBaseChangeMap {X₁ X₂ X₃ X₄ : Over B} {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃}
    {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (h : IsPullback f₁.left f₂.left f₃.left f₄.left) :
    IsPullback (AlgebraicGeometry.overBaseChangeMap ι f₁) (AlgebraicGeometry.overBaseChangeMap ι f₂)
      (AlgebraicGeometry.overBaseChangeMap ι f₃) (AlgebraicGeometry.overBaseChangeMap ι f₄) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_overBaseChangeMap ι f₃)
  · rw [overBaseChangeMap_fst, overBaseChangeMap_fst]
    exact (isPullback_overBaseChangeMap ι f₂).paste_horiz h
  · apply pullback.hom_ext
    · simp only [Category.assoc, overBaseChangeMap_fst, overBaseChangeMap_fst_assoc]
      rw [h.w]
    · simp

end BaseChangeOver

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k']
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}

/-- The identification `ε` of a trait model over the generic base lies over
`Spec Ω ⟶ η ⟶ Spec F`. -/
@[reassoc]
lemma IsTraitModelOfGenericBase.ε_hom {X₁ : Over (Spec (.of F))} {X' : Over (Spec (.of k'))}
    {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    M.ε ≫ X₁.hom = g ≫ traitGenericPointToSpec k' ≫ ι := by
  obtain ⟨u, -, hu₁, hu₂⟩ := h.exists_openImmersion
  rw [← hu₁, ← hu₂, Category.assoc, Category.assoc, pullback.condition]

variable {Y : Over (Spec (.of F))} {Y' : Over (Spec (.of k'))}
  {N : NearbyCyclesModel Y.left Y'.left} {q : N.total ⟶ trait k'}
  {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

variable (q g) in
/-- A *compactification* of a trait model `N` over the generic base `(F, ι)`: a trait model `P`
over the generic base `(F, ι)` of a proper `F`-scheme `X` with proper special fibre `X'`, proper
over the trait, with generic fibre all of `X ×_F η` and geometric generic fibre all of
`X ×_F Spec Ω`, containing `N` as an open sub-model over open immersions `ιX : Y ⟶ X` and
`ιX' : Y' ⟶ X'` (an open immersion of total spaces compatible with the structure morphisms,
whose square of geometric generic fibres is cartesian). -/
structure IsTraitModelOfGenericBase.Compactification
    (h : N.IsTraitModelOfGenericBase Y ι q g) where
  /-- the proper `F`-scheme `X`. -/
  X : Over (Spec (.of F))
  /-- the special fibre `X'`. -/
  X' : Over (Spec (.of k'))
  [locallyOfFiniteType : LocallyOfFiniteType X.hom]
  [quasiCompact : QuasiCompact X.hom]
  [isSeparated : IsSeparated X.hom]
  [isProper : IsProper (CondensedRing.toPoint X).left]
  [locallyOfFiniteType' : LocallyOfFiniteType X'.hom]
  [quasiCompact' : QuasiCompact X'.hom]
  [isSeparated' : IsSeparated X'.hom]
  [isProper' : IsProper (CondensedRing.toPoint X').left]
  /-- the model `P`. -/
  model : NearbyCyclesModel X.left X'.left
  /-- the structure morphism of the total space of `P` to the trait. -/
  qc : model.total ⟶ trait k'
  /-- the structure morphism of the geometric generic fibre of `P` to `Spec Ω`. -/
  gc : model.generic ⟶ Spec (.of (traitGenericField k'))
  isTraitModelOfGenericBase : model.IsTraitModelOfGenericBase X ι qc gc
  isPullback_ε : IsPullback model.ε gc X.hom (traitGenericPointToSpec k' ≫ ι)
  exists_isIso_genericFibre :
    ∃ w : pullback qc (traitGenericSpec k') ⟶ pullback X.hom ι, IsIso w ∧
      w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      genericFibreInclusion model qc gc isTraitModelOfGenericBase.isTraitModelOver.isPullback_j.w ≫
        w ≫ pullback.fst _ _ = model.ε
  [isProper_qc : IsProper qc]
  /-- the open immersion `ιX : Y ⟶ X`. -/
  ιX : Y ⟶ X
  /-- the open immersion `ιX' : Y' ⟶ X'` of special fibres. -/
  ιX' : Y' ⟶ X'
  [isOpenImmersion_ιX : IsOpenImmersion ιX.left]
  [isOpenImmersion_ιX' : IsOpenImmersion ιX'.left]
  /-- the inclusion of `N` in `P`. -/
  hom : N.Hom model ιX.left ιX'.left
  [isOpenImmersion_hom_total : IsOpenImmersion hom.total]
  isPullback_hom_j : IsPullback hom.generic N.j model.j hom.total
  q_eq : q = hom.total ≫ qc
  g_eq : g = hom.generic ≫ gc

namespace IsTraitModelOfGenericBase

attribute [instance] Compactification.locallyOfFiniteType Compactification.quasiCompact
  Compactification.isSeparated Compactification.isProper Compactification.locallyOfFiniteType'
  Compactification.quasiCompact' Compactification.isSeparated' Compactification.isProper'
  Compactification.isProper_qc Compactification.isOpenImmersion_ιX
  Compactification.isOpenImmersion_ιX' Compactification.isOpenImmersion_hom_total

/-- Every trait model over a generic base of a separated `F`-scheme of finite type has a
compactification (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel`). -/
lemma nonempty_compactification [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (h : N.IsTraitModelOfGenericBase Y ι q g) :
    Nonempty h.Compactification := by
  obtain ⟨X, _, _, _, _, X', _, _, _, _, P, qP, gP, hP, hgen, hw, _, ιX, _, ιX', _, φ, _, hφ, hq,
    hg⟩ := h.exists_isProper_openSubmodel
  exact ⟨⟨X, X', P, qP, gP, hP, hgen, hw, ιX, ιX', φ, hφ, hq, hg⟩⟩

variable {h : N.IsTraitModelOfGenericBase Y ι q g}

/-- The structure morphism of `Y` is quasi-compact as soon as `N` has a compactification: `Y` is
open in the noetherian scheme `X`. -/
lemma Compactification.quasiCompact_hom (C : h.Compactification) : QuasiCompact Y.hom := by
  have := LocallyOfFiniteType.isLocallyNoetherian C.X.hom
  rw [← Over.w C.ιX]
  infer_instance

/-- The compactification `Y ⟶ X ⟶ Spec F` of the structure morphism of `Y` underlying a
compactification of `N`. -/
noncomputable def Compactification.toCompactification (C : h.Compactification) :
    AlgebraicGeometry.Compactification Y.hom where
  Z := C.X.left
  g := C.X.hom
  i := C.ιX.left
  comm := (Over.w C.ιX).symm
  isProper := by
    rw [← CondensedRing.toPoint_left]
    infer_instance
  isOpenImmersion := inferInstance

/-- **Common compactification of `Y`.** For two compactifications `C₁`, `C₂` of `N` there is a
proper `F`-scheme `X₃` containing `Y` as an open, with proper morphisms `X₃ ⟶ X₁`, `X₃ ⟶ X₂`
under `Y` over which `Y` is cartesian and which are jointly monomorphic: the closure of the graph
of `Y` in `X₁ ×_F X₂` (`AlgebraicGeometry.Compactification.inf`). -/
lemma Compactification.exists_common (C₁ C₂ : h.Compactification) :
    ∃ (X₃ : Over (Spec (.of F))) (_ : IsProper X₃.hom) (ι₃ : Y ⟶ X₃)
      (_ : IsOpenImmersion ι₃.left) (p₁ : X₃ ⟶ C₁.X) (p₂ : X₃ ⟶ C₂.X) (_ : IsProper p₁.left)
      (_ : IsProper p₂.left), ι₃ ≫ p₁ = C₁.ιX ∧ ι₃ ≫ p₂ = C₂.ιX ∧
      IsPullback ι₃.left (𝟙 Y.left) p₁.left C₁.ιX.left ∧
      IsPullback ι₃.left (𝟙 Y.left) p₂.left C₂.ιX.left ∧
      ∀ {T : Scheme.{u}} (a b : T ⟶ X₃.left), a ≫ p₁.left = b ≫ p₁.left →
        a ≫ p₂.left = b ≫ p₂.left → a = b := by
  have := C₁.quasiCompact_hom
  let c₁ := C₁.toCompactification
  let c₂ := C₂.toCompactification
  refine ⟨Over.mk (c₁.inf c₂).g, (c₁.inf c₂).isProper,
    Over.homMk (c₁.inf c₂).i (c₁.inf c₂).comm.symm, (c₁.inf c₂).isOpenImmersion,
    Over.homMk (c₁.infFst c₂).hom (c₁.infFst c₂).hom_g,
    Over.homMk (c₁.infSnd c₂).hom (c₁.infSnd c₂).hom_g,
    inferInstanceAs (IsProper (c₁.infFst c₂).hom), inferInstanceAs (IsProper (c₁.infSnd c₂).hom),
    ?_, ?_, c₁.isPullback_infFst c₂, c₁.isPullback_infSnd c₂, ?_⟩
  · ext1
    exact (c₁.infFst c₂).i_hom
  · ext1
    exact (c₁.infSnd c₂).i_hom
  · intro T a b h₁ h₂
    rw [← cancel_mono (AlgebraicGeometry.Compactification.graph c₁ c₂).imageι]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact h₁
    · rw [Category.assoc, Category.assoc]
      exact h₂

/-- **The generic fibre of `N` in a compactification.** Over the generic point `η` of the trait,
`N_η` is the inverse image of `N ⊆ 𝒳` along `X₃ ×_F η ⟶ X ×_F η ≅ 𝒳 ×_S η`, for
`p : X₃ ⟶ X` under `Y` with `Y = X₃ ×_X Y`, where `N_η ⟶ X₃ ×_F η` is the open immersion
`N_η ⟶ Y ×_F η` of the trait model `N` followed by `Y ×_F η ⟶ X₃ ×_F η`. The key point is that
`N_η ⟶ 𝒳_η ≅ X ×_F η` is `N_η ⟶ Y ×_F η ⟶ X ×_F η`, as it is on the geometric generic fibre,
which is faithfully flat over `N_η`. -/
lemma Compactification.isPullback_genericFibre (C : h.Compactification)
    {wN : pullback q (traitGenericSpec k') ⟶ pullback Y.hom ι}
    (hwN₁ : wN ≫ pullback.snd _ _ = pullback.snd _ _)
    (hwN₂ : genericFibreInclusion N q g h.isTraitModelOver.isPullback_j.w ≫ wN ≫
      pullback.fst _ _ = N.ε)
    {w : pullback C.qc (traitGenericSpec k') ⟶ pullback C.X.hom ι} [IsIso w]
    (hw₁ : w ≫ pullback.snd _ _ = pullback.snd _ _)
    (hw₂ : genericFibreInclusion C.model C.qc C.gc
      C.isTraitModelOfGenericBase.isTraitModelOver.isPullback_j.w ≫ w ≫ pullback.fst _ _ =
        C.model.ε)
    {X₃ : Over (Spec (.of F))} {ι₃ : Y ⟶ X₃} {p : X₃ ⟶ C.X}
    (hιpb : IsPullback ι₃.left (𝟙 Y.left) p.left C.ιX.left) :
    IsPullback (wN ≫ overBaseChangeMap ι ι₃) (pullback.fst q (traitGenericSpec k'))
      (overBaseChangeMap ι p ≫ inv w ≫ pullback.fst _ _) C.hom.total := by
  have hN := h.isTraitModelOver
  let nC := pullback.map q (traitGenericSpec k') C.qc (traitGenericSpec k') C.hom.total (𝟙 _)
    (𝟙 _) ((Category.comp_id _).trans C.q_eq) (by rw [Category.comp_id, Category.id_comp])
  have hnC_fst : nC ≫ pullback.fst _ _ = pullback.fst _ _ ≫ C.hom.total :=
    pullback.lift_fst _ _ _
  have hnC_snd : nC ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [pullback.lift_snd, Category.comp_id]
  have hbase : IsPullback nC (pullback.fst q (traitGenericSpec k'))
      (pullback.fst C.qc (traitGenericSpec k')) C.hom.total := by
    refine IsPullback.of_right ?_ hnC_fst (IsPullback.of_hasPullback C.qc _).flip
    rw [hnC_snd, ← C.q_eq]
    exact (IsPullback.of_hasPullback q (traitGenericSpec k')).flip
  have hbot : IsPullback (nC ≫ w) (pullback.fst q (traitGenericSpec k'))
      (inv w ≫ pullback.fst _ _) C.hom.total :=
    IsPullback.of_iso hbase (Iso.refl _) (asIso w) (Iso.refl _) (Iso.refl _) (by simp)
      (by simp) (by simp) (by simp)
  -- `N_η ⟶ 𝒳_η ≅ X ×_F η` is `N_η ⟶ Y ×_F η ⟶ X ×_F η`, as it is over `Spec Ω`
  have hcomp : nC ≫ w = wN ≫ overBaseChangeMap ι C.ιX := by
    have : Epi (genericFibreInclusion N q g hN.isPullback_j.w) :=
      hN.epi_lift_traitGenericPointToSpec
    have hincl : genericFibreInclusion N q g hN.isPullback_j.w ≫ nC =
        C.hom.generic ≫ genericFibreInclusion C.model C.qc C.gc
          C.isTraitModelOfGenericBase.isTraitModelOver.isPullback_j.w := by
      apply pullback.hom_ext
      · rw [Category.assoc, hnC_fst, genericFibreInclusion_fst_assoc, Category.assoc,
          genericFibreInclusion_fst, C.hom.comm_j]
      · rw [Category.assoc, hnC_snd, genericFibreInclusion_snd, Category.assoc,
          genericFibreInclusion_snd, ← Category.assoc, ← C.g_eq]
    apply pullback.hom_ext
    · rw [← cancel_epi (genericFibreInclusion N q g hN.isPullback_j.w), Category.assoc,
        Category.assoc, reassoc_of% hincl, hw₂, overBaseChangeMap_fst,
        reassoc_of% hwN₂, C.hom.comm_ε]
    · rw [Category.assoc, hw₁, hnC_snd, Category.assoc, overBaseChangeMap_snd, hwN₁]
  rw [hcomp] at hbot
  have htop : IsPullback (wN ≫ overBaseChangeMap ι ι₃) (𝟙 _) (overBaseChangeMap ι p)
      (wN ≫ overBaseChangeMap ι C.ιX) := by
    have := IsPullback.overBaseChangeMap ι (f₁ := ι₃) (f₂ := 𝟙 Y) (f₃ := p) (f₄ := C.ιX) hιpb
    rw [overBaseChangeMap_id] at this
    exact (IsPullback.id_vert wN).paste_horiz this
  simpa using htop.paste_vert hbot

/-- **A compactification from a proper model over the trait.** Let `X₃` be a proper `F`-scheme
containing `Y` as an open, and `B` a scheme proper over the trait containing the total space of
`N` as an open over the trait, whose generic fibre is `X₃ ×_F η` (via `s : X₃ ×_F η ⟶ B`)
compatibly with `N_Ω ⟶ Y ×_F Spec Ω ⟶ X₃ ×_F Spec Ω`. Then the model with total space `B`,
geometric generic fibre `X₃ ×_F Spec Ω` and special fibre `B ×_S Spec k'` is a compactification
of `N`. -/
noncomputable def Compactification.ofIsPullback {X₃ : Over (Spec (.of F))} [IsProper X₃.hom]
    (ι₃ : Y ⟶ X₃) [IsOpenImmersion ι₃.left] {B : Scheme.{u}} (c : N.total ⟶ B)
    [IsOpenImmersion c] (qc : B ⟶ trait k') [IsProper qc] (s : pullback X₃.hom ι ⟶ B)
    (hs : IsPullback s (pullback.snd _ _) qc (traitGenericSpec k')) (hq : q = c ≫ qc)
    (hcj : pullback.lift (N.ε ≫ ι₃.left) g (by rw [Category.assoc, Over.w ι₃, h.ε_hom]) ≫
      genericFibreBaseChangeMap k' X₃ ι ≫ s = N.j ≫ c) :
    h.Compactification :=
  have hN := h.isTraitModelOver
  have hι' : IsPullback (pullback.lift (N.i ≫ c) Y'.hom
      (by rw [Category.assoc, ← hq, hN.isPullback_i.w]) :
        Y'.left ⟶ pullback qc (traitClosedPoint k'))
      N.i (pullback.fst qc (traitClosedPoint k')) c := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback qc (traitClosedPoint k')).flip
    rw [pullback.lift_snd, ← hq]
    exact hN.isPullback_i.flip
  have hP : IsProper (pullback.snd qc (traitClosedPoint k')) := inferInstance
  have hMcj : IsPullback (genericFibreBaseChangeMap k' X₃ ι ≫ s) (pullback.snd _ _) qc
      (traitGenericPoint k') := by
    rw [← traitGenericPointToSpec_traitGenericSpec]
    exact (isPullback_genericFibreBaseChangeMap k' X₃ ι).paste_horiz hs
  have key
      (x : pullback X₃.hom (traitGenericPointToSpec k' ≫ ι) ⟶ pullback qc (traitGenericSpec k'))
      (h₁ : x ≫ pullback.fst _ _ = genericFibreBaseChangeMap k' X₃ ι ≫ s)
      (h₂ : x ≫ pullback.snd _ _ = pullback.snd _ _ ≫ traitGenericPointToSpec k') :
      x ≫ hs.isoPullback.inv ≫ pullback.fst _ _ = pullback.fst _ _ := by
    have hx : x = genericFibreBaseChangeMap k' X₃ ι ≫ hs.isoPullback.hom := by
      apply pullback.hom_ext
      · rw [h₁, Category.assoc, IsPullback.isoPullback_hom_fst]
      · rw [h₂, Category.assoc, IsPullback.isoPullback_hom_snd, genericFibreBaseChangeMap_snd]
    rw [hx, Category.assoc, Iso.hom_inv_id_assoc, genericFibreBaseChangeMap_fst]
  { X := X₃
    X' := Over.mk (pullback.snd qc (traitClosedPoint k'))
    isProper := by
      rw [CondensedRing.toPoint_left]
      infer_instance
    locallyOfFiniteType' := hP.toLocallyOfFiniteType
    quasiCompact' := inferInstanceAs (QuasiCompact (pullback.snd qc (traitClosedPoint k')))
    isSeparated' := hP.toIsSeparated
    isProper' := by
      rw [CondensedRing.toPoint_left]
      exact hP
    model :=
      { total := B
        generic := pullback X₃.hom (traitGenericPointToSpec k' ≫ ι)
        j := genericFibreBaseChangeMap k' X₃ ι ≫ s
        i := pullback.fst qc (traitClosedPoint k')
        ε := pullback.fst _ _ }
    qc := qc
    gc := pullback.snd _ _
    isTraitModelOfGenericBase :=
      ⟨⟨inferInstance, inferInstance, inferInstance, hMcj, IsPullback.of_hasPullback _ _⟩,
        hs.isoPullback.inv, inferInstance, hs.isoPullback_inv_snd,
        key _ (genericFibreInclusion_fst _ _ _ _) (genericFibreInclusion_snd _ _ _ _)⟩
    isPullback_ε := IsPullback.of_hasPullback _ _
    exists_isIso_genericFibre := ⟨hs.isoPullback.inv, inferInstance, hs.isoPullback_inv_snd,
      key _ (genericFibreInclusion_fst _ _ _ _) (genericFibreInclusion_snd _ _ _ _)⟩
    ιX := ι₃
    ιX' := Over.homMk (pullback.lift (N.i ≫ c) Y'.hom
      (by rw [Category.assoc, ← hq, hN.isPullback_i.w])) (pullback.lift_snd _ _ _)
    isOpenImmersion_ιX' := MorphismProperty.of_isPullback hι'.flip ‹_›
    hom :=
      { total := c
        generic := pullback.lift (N.ε ≫ ι₃.left) g
          (by rw [Category.assoc, Over.w ι₃, h.ε_hom])
        comm_j := hcj
        comm_i := pullback.lift_fst _ _ _
        comm_ε := pullback.lift_fst _ _ _ }
    isPullback_hom_j := by
      refine IsPullback.of_right ?_ hcj hMcj.flip
      rw [pullback.lift_snd, ← hq]
      exact hN.isPullback_j.flip
    q_eq := hq
    g_eq := (pullback.lift_snd _ _ _).symm }

/-- A *refinement* `C₃ ⟶ C₁` of compactifications of `N`: a morphism of models `π : P₃ ⟶ P₁` over
proper morphisms `p : X₃ ⟶ X₁` and `p' : X₃' ⟶ X₁'`, compatible with the inclusions of `N` and
with the structure morphisms, such that `N` is the inverse image of itself: the squares of the
inclusions of `Y`, `Y'`, of the total spaces and of the geometric generic fibres along `p`, `p'`,
`π` are cartesian. -/
structure Compactification.Refinement (C₃ C₁ : h.Compactification) where
  /-- the morphism `X₃ ⟶ X₁`. -/
  p : C₃.X ⟶ C₁.X
  /-- the morphism `X₃' ⟶ X₁'` of special fibres. -/
  p' : C₃.X' ⟶ C₁.X'
  [isProper_p : IsProper p.left]
  [isProper_p' : IsProper p'.left]
  /-- the morphism of models `P₃ ⟶ P₁`. -/
  π : C₃.model.Hom C₁.model p.left p'.left
  ιX_comp : C₃.ιX ≫ p = C₁.ιX
  ιX'_comp : C₃.ιX' ≫ p' = C₁.ιX'
  hom_total_comp : C₃.hom.total ≫ π.total = C₁.hom.total
  hom_generic_comp : C₃.hom.generic ≫ π.generic = C₁.hom.generic
  qc_eq : C₃.qc = π.total ≫ C₁.qc
  gc_eq : C₃.gc = π.generic ≫ C₁.gc
  isPullback_ιX : IsPullback C₃.ιX.left (𝟙 Y.left) p.left C₁.ιX.left
  isPullback_ιX' : IsPullback C₃.ιX'.left (𝟙 Y'.left) p'.left C₁.ιX'.left
  isPullback_total : IsPullback C₃.hom.total (𝟙 N.total) π.total C₁.hom.total
  isPullback_generic : IsPullback C₃.hom.generic (𝟙 N.generic) π.generic C₁.hom.generic

attribute [instance] Compactification.Refinement.isProper_p
  Compactification.Refinement.isProper_p'

/-- **Refinements from the total spaces.** A morphism `π : 𝒳₃ ⟶ 𝒳` of total spaces of
compactifications `C₃`, `C` of `N` over the trait, compatible with the inclusions of `N`, over
a proper `p : X₃ ⟶ X` under `Y` with `Y = X₃ ×_X Y`, together with a morphism `πg` of geometric
generic fibres compatible with `π`, the structure morphisms and the identifications `ε`, and with
`N = 𝒳₃ ×_𝒳 N`, induces a refinement `C₃ ⟶ C`: the morphism of special fibres is the base change
of `π`, and the remaining cartesian squares are base changes of `N = 𝒳₃ ×_𝒳 N`. -/
lemma Compactification.nonempty_refinement {C₃ C : h.Compactification} (p : C₃.X ⟶ C.X)
    [IsProper p.left] (hι : C₃.ιX ≫ p = C.ιX)
    (hιpb : IsPullback C₃.ιX.left (𝟙 Y.left) p.left C.ιX.left)
    (π : C₃.model.total ⟶ C.model.total) (htot : C₃.hom.total ≫ π = C.hom.total)
    (hq : C₃.qc = π ≫ C.qc) (πg : C₃.model.generic ⟶ C.model.generic)
    (hπg : πg ≫ C.model.j = C₃.model.j ≫ π) (hπgg : πg ≫ C.gc = C₃.gc)
    (hε : πg ≫ C.model.ε = C₃.model.ε ≫ p.left)
    (hpb : IsPullback C₃.hom.total (𝟙 N.total) π C.hom.total) :
    Nonempty (C₃.Refinement C) := by
  have hC := C.isTraitModelOfGenericBase.isTraitModelOver
  have hC₃ := C₃.isTraitModelOfGenericBase.isTraitModelOver
  let p'l : C₃.X'.left ⟶ C.X'.left := hC.isPullback_i.lift (C₃.model.i ≫ π) C₃.X'.hom
    (by rw [Category.assoc, ← hq, hC₃.isPullback_i.w])
  have hp'l : p'l ≫ C.X'.hom = C₃.X'.hom := hC.isPullback_i.lift_snd _ _ _
  have : IsProper (p'l ≫ C.X'.hom) := by
    rw [hp'l, ← CondensedRing.toPoint_left]
    infer_instance
  have : IsProper p'l := IsProper.of_comp p'l C.X'.hom
  let p' : C₃.X' ⟶ C.X' := Over.homMk p'l hp'l
  have : IsProper p'.left := ‹IsProper p'l›
  have hp'i : p'l ≫ C.model.i = C₃.model.i ≫ π := hC.isPullback_i.lift_fst _ _ _
  let φ : C₃.model.Hom C.model p.left p'.left :=
    { total := π
      generic := πg
      comm_j := hπg
      comm_i := hp'i
      comm_ε := hε }
  have hR_i : IsPullback C₃.model.i p'l π C.model.i := by
    refine IsPullback.of_bot ?_ hp'i.symm hC.isPullback_i
    rw [hp'l, ← hq]
    exact hC₃.isPullback_i
  have hR_j : IsPullback C₃.model.j πg π C.model.j := by
    refine IsPullback.of_bot ?_ hπg.symm hC.isPullback_j
    rw [hπgg, ← hq]
    exact hC₃.isPullback_j
  have hι' : C₃.ιX'.left ≫ p'l = C.ιX'.left := by
    refine hC.isPullback_i.hom_ext ?_ ?_
    · rw [Category.assoc, hp'i, ← Category.assoc, C₃.hom.comm_i, Category.assoc, htot,
        C.hom.comm_i]
    · rw [Category.assoc, hp'l, Over.w C₃.ιX', Over.w C.ιX']
  have hgen : C₃.hom.generic ≫ πg = C.hom.generic := by
    refine hC.isPullback_j.hom_ext ?_ ?_
    · rw [Category.assoc, hπg, ← Category.assoc, C₃.hom.comm_j, Category.assoc, htot,
        C.hom.comm_j]
    · rw [Category.assoc, hπgg, ← C₃.g_eq]
      exact C.g_eq
  exact ⟨{ p := p
           p' := p'
           π := φ
           ιX_comp := hι
           ιX'_comp := Over.OverMorphism.ext hι'
           hom_total_comp := htot
           hom_generic_comp := hgen
           qc_eq := hq
           gc_eq := hπgg.symm
           isPullback_ιX := hιpb
           isPullback_ιX' := hpb.of_id_of_isPullback hR_i C₃.hom.comm_i C.hom.comm_i hι'
           isPullback_total := hpb
           isPullback_generic := hpb.of_id_of_isPullback hR_j C₃.hom.comm_j C.hom.comm_j hgen }⟩

end IsTraitModelOfGenericBase

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry

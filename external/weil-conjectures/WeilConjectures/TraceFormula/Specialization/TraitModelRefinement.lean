/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import WeilConjectures.TraceFormula.Specialization.TraitModelGenericSpec

/-!

# Compactifications of trait models over the base and their common refinements

Let `S = Spec k'⟦t⟧` be the trait and `N` a trait model over the base of a separated `k`-scheme
`Y` of finite type (`NearbyCyclesModel.IsTraitModelOfBase`). A *compactification* of `N`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification`) is a trait model `P` over the base of a
proper `k`-scheme `X`, with proper total space over `S`, proper special fibre and geometric generic
fibre all of `X ×_k Spec Ω`, containing `N` as an open sub-model over open immersions `Y ⟶ X` and
`Y' ⟶ X'`. Compactifications exist
(`NearbyCyclesModel.IsTraitModelOfBase.nonempty_compactification`, from
`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`).

A *refinement* `C₃ ⟶ C₁` of compactifications
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.Refinement`) is a morphism of models
`P₃ ⟶ P₁` over proper morphisms `X₃ ⟶ X₁`, `X₃' ⟶ X₁'`, compatible with the inclusions of `N`,
over which `N` is cartesian: `N = P₃ ×_{P₁} N` on the total spaces, the geometric generic fibres
and the special fibres, and `Y = X₃ ×_{X₁} Y`. Any two compactifications have a common refinement
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`). This is the common
refinement of the proof of blueprint `prose-E-15` ("two compactifications have a
common proper refinement"), used to show that the compact-support exchange, and hence the
dualizing map of nearby cycles, does not depend on the compactification.

The common refinement is built from a proper model `B` over `(X₃ ×_k S) ×_S 𝒳₁ ×_S 𝒳₂`, with
`X₃` the closure of the graph of `Y` in `X₁ ×_k X₂`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_common`), assembled into a
compactification by `NearbyCyclesModel.IsTraitModelOfBase.Compactification.ofIsPullback`. The
refinements are induced by morphisms of total spaces
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.nonempty_refinement`); the cartesian
square of total spaces comes from the description of `N` over the generic point of the trait
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.isPullback_traitGenericSpec`) and a
density argument (`AlgebraicGeometry.isPullback_id_of_dense`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {Y : Over (Spec (.of k))} {Y' : Over (Spec (.of k'))} {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

variable (q g) in
/-- A *compactification* of a trait model `N` over the base: a trait model `P` over the base of a
proper `k`-scheme `X` with proper special fibre `X'`, proper over the trait, with geometric
generic fibre all of `X ×_k Spec Ω`, containing `N` as an open sub-model over open immersions
`ι : Y ⟶ X` and `ι' : Y' ⟶ X'` (an open immersion of total spaces compatible with the structure
morphisms, whose square of geometric generic fibres is cartesian). -/
structure IsTraitModelOfBase.Compactification (h : N.IsTraitModelOfBase k q g) where
  /-- the proper `k`-scheme `X`. -/
  X : Over (Spec (.of k))
  /-- the special fibre `X'`. -/
  X' : Over (Spec (.of k'))
  [locallyOfFiniteType : LocallyOfFiniteType X.hom]
  [quasiCompact : QuasiCompact X.hom]
  [isSeparated : IsSeparated X.hom]
  [isProper : IsProper (toPoint X).left]
  [locallyOfFiniteType' : LocallyOfFiniteType X'.hom]
  [quasiCompact' : QuasiCompact X'.hom]
  [isSeparated' : IsSeparated X'.hom]
  [isProper' : IsProper (toPoint X').left]
  /-- the model `P`. -/
  model : NearbyCyclesModel X.left X'.left
  /-- the structure morphism of the total space of `P` to the trait. -/
  qc : model.total ⟶ trait k'
  /-- the structure morphism of the geometric generic fibre of `P` to `Spec Ω`. -/
  gc : model.generic ⟶ Spec (.of (traitGenericField k'))
  isTraitModelOfBase : model.IsTraitModelOfBase k qc gc
  isPullback_ε : IsPullback model.ε gc X.hom (traitGenericPoint k' ≫ traitToBase k k')
  [isProper_qc : IsProper qc]
  /-- the open immersion `ι : Y ⟶ X`. -/
  ι : Y ⟶ X
  /-- the open immersion `ι' : Y' ⟶ X'` of special fibres. -/
  ι' : Y' ⟶ X'
  [isOpenImmersion_ι : IsOpenImmersion ι.left]
  [isOpenImmersion_ι' : IsOpenImmersion ι'.left]
  /-- the inclusion of `N` in `P`. -/
  hom : N.Hom model ι.left ι'.left
  [isOpenImmersion_hom_total : IsOpenImmersion hom.total]
  isPullback_hom_j : IsPullback hom.generic N.j model.j hom.total
  q_eq : q = hom.total ≫ qc
  g_eq : g = hom.generic ≫ gc

namespace IsTraitModelOfBase

attribute [instance] Compactification.locallyOfFiniteType Compactification.quasiCompact
  Compactification.isSeparated Compactification.isProper Compactification.locallyOfFiniteType'
  Compactification.quasiCompact' Compactification.isSeparated' Compactification.isProper'
  Compactification.isProper_qc Compactification.isOpenImmersion_ι
  Compactification.isOpenImmersion_ι' Compactification.isOpenImmersion_hom_total

/-- Every trait model over the base of a separated `k`-scheme of finite type has a
compactification (`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`). -/
lemma nonempty_compactification [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (h : N.IsTraitModelOfBase k q g) : Nonempty h.Compactification := by
  obtain ⟨X, _, _, _, _, X', _, _, _, _, P, qP, gP, hP, hgen, _, ι, _, ι', _, φ, _, hφ, hq, hg⟩ :=
    h.exists_isProper_openSubmodel
  exact ⟨⟨X, X', P, qP, gP, hP, hgen, ι, ι', φ, hφ, hq, hg⟩⟩

variable {h : N.IsTraitModelOfBase k q g}

/-- The structure morphism of `Y` is quasi-compact as soon as `N` has a compactification: `Y` is
open in the noetherian scheme `X`. -/
lemma Compactification.quasiCompact_hom (C : h.Compactification) : QuasiCompact Y.hom := by
  have := LocallyOfFiniteType.isLocallyNoetherian C.X.hom
  rw [← Over.w C.ι]
  infer_instance

/-- The compactification `Y ⟶ X ⟶ Spec k` of the structure morphism of `Y` underlying a
compactification of `N`. -/
noncomputable def Compactification.toCompactification (C : h.Compactification) :
    AlgebraicGeometry.Compactification Y.hom where
  Z := C.X.left
  g := C.X.hom
  i := C.ι.left
  comm := (Over.w C.ι).symm
  isProper := by
    rw [← toPoint_left]
    infer_instance
  isOpenImmersion := inferInstance

/-- **Common compactification of `Y`.** For two compactifications `C₁`, `C₂` of `N` there is a
proper `k`-scheme `X₃` containing `Y` as an open, with proper morphisms `X₃ ⟶ X₁`, `X₃ ⟶ X₂`
under `Y` over which `Y` is cartesian: the closure of the graph of `Y` in `X₁ ×_k X₂`
(`AlgebraicGeometry.Compactification.inf`). -/
lemma Compactification.exists_common (C₁ C₂ : h.Compactification) :
    ∃ (X₃ : Over (Spec (.of k))) (_ : IsProper X₃.hom) (ι₃ : Y ⟶ X₃)
      (_ : IsOpenImmersion ι₃.left) (p₁ : X₃ ⟶ C₁.X) (p₂ : X₃ ⟶ C₂.X) (_ : IsProper p₁.left)
      (_ : IsProper p₂.left), ι₃ ≫ p₁ = C₁.ι ∧ ι₃ ≫ p₂ = C₂.ι ∧
      IsPullback ι₃.left (𝟙 Y.left) p₁.left C₁.ι.left ∧
      IsPullback ι₃.left (𝟙 Y.left) p₂.left C₂.ι.left := by
  have := C₁.quasiCompact_hom
  let c₁ := C₁.toCompactification
  let c₂ := C₂.toCompactification
  refine ⟨Over.mk (c₁.inf c₂).g, (c₁.inf c₂).isProper,
    Over.homMk (c₁.inf c₂).i (c₁.inf c₂).comm.symm, (c₁.inf c₂).isOpenImmersion,
    Over.homMk (c₁.infFst c₂).hom (c₁.infFst c₂).hom_g,
    Over.homMk (c₁.infSnd c₂).hom (c₁.infSnd c₂).hom_g,
    inferInstanceAs (IsProper (c₁.infFst c₂).hom), inferInstanceAs (IsProper (c₁.infSnd c₂).hom),
    ?_, ?_, c₁.isPullback_infFst c₂, c₁.isPullback_infSnd c₂⟩
  · ext1
    exact (c₁.infFst c₂).i_hom
  · ext1
    exact (c₁.infSnd c₂).i_hom

/-- **A compactification from a proper model over the trait.** Let `X₃` be a proper `k`-scheme
containing `Y` as an open, and `B` a scheme proper over the trait containing the total space of
`N` as an open over the trait, whose geometric generic fibre is `X₃ ×_k Spec Ω` (via
`j : X₃ ×_k Spec Ω ⟶ B`) compatibly with `N_Ω ⟶ Y ×_k Spec Ω ⟶ X₃ ×_k Spec Ω`, with a morphism
`e : B ⟶ X₃` restricting to the projection on `X₃ ×_k Spec Ω`. Then the model with total space
`B` and special fibre `B ×_S Spec k'` is a compactification of `N`. -/
noncomputable def Compactification.ofIsPullback {X₃ : Over (Spec (.of k))} [IsProper X₃.hom]
    (ι₃ : Y ⟶ X₃) [IsOpenImmersion ι₃.left] {B : Scheme.{u}} (c : N.total ⟶ B)
    [IsOpenImmersion c] (qc : B ⟶ trait k') [IsProper qc]
    (j : pullback X₃.hom (traitGenericPoint k' ≫ traitToBase k k') ⟶ B)
    (hj : IsPullback j (pullback.snd _ _) qc (traitGenericPoint k')) (e : B ⟶ X₃.left)
    (he : j ≫ e = pullback.fst _ _) (he' : e ≫ X₃.hom = qc ≫ traitToBase k k')
    (hq : q = c ≫ qc)
    (hcj : pullback.lift (N.ε ≫ ι₃.left) g (by rw [Category.assoc, Over.w ι₃, h.ε_hom]) ≫ j =
      N.j ≫ c) :
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
  { X := X₃
    X' := Over.mk (pullback.snd qc (traitClosedPoint k'))
    isProper := by
      rw [toPoint_left]
      infer_instance
    locallyOfFiniteType' := hP.toLocallyOfFiniteType
    quasiCompact' := inferInstanceAs (QuasiCompact (pullback.snd qc (traitClosedPoint k')))
    isSeparated' := hP.toIsSeparated
    isProper' := by
      rw [toPoint_left]
      exact hP
    model :=
      { total := B
        generic := pullback X₃.hom (traitGenericPoint k' ≫ traitToBase k k')
        j := j
        i := pullback.fst qc (traitClosedPoint k')
        ε := pullback.fst _ _ }
    qc := qc
    gc := pullback.snd _ _
    isTraitModelOfBase := IsTraitModelOfBase.of_isPullback ⟨inferInstance, inferInstance,
      inferInstance, hj, IsPullback.of_hasPullback _ _⟩ ⟨e, he, he'⟩
      (IsPullback.of_hasPullback _ _)
    isPullback_ε := IsPullback.of_hasPullback _ _
    ι := ι₃
    ι' := Over.homMk (pullback.lift (N.i ≫ c) Y'.hom
      (by rw [Category.assoc, ← hq, hN.isPullback_i.w])) (pullback.lift_snd _ _ _)
    isOpenImmersion_ι' := MorphismProperty.of_isPullback hι'.flip ‹_›
    hom :=
      { total := c
        generic := pullback.lift (N.ε ≫ ι₃.left) g (by rw [Category.assoc, Over.w ι₃, h.ε_hom])
        comm_j := hcj
        comm_i := pullback.lift_fst _ _ _
        comm_ε := pullback.lift_fst _ _ _ }
    isPullback_hom_j := by
      refine IsPullback.of_right ?_ hcj hj.flip
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
  ι_comp : C₃.ι ≫ p = C₁.ι
  ι'_comp : C₃.ι' ≫ p' = C₁.ι'
  hom_total_comp : C₃.hom.total ≫ π.total = C₁.hom.total
  hom_generic_comp : C₃.hom.generic ≫ π.generic = C₁.hom.generic
  qc_eq : C₃.qc = π.total ≫ C₁.qc
  gc_eq : C₃.gc = π.generic ≫ C₁.gc
  isPullback_ι : IsPullback C₃.ι.left (𝟙 Y.left) p.left C₁.ι.left
  isPullback_ι' : IsPullback C₃.ι'.left (𝟙 Y'.left) p'.left C₁.ι'.left
  isPullback_total : IsPullback C₃.hom.total (𝟙 N.total) π.total C₁.hom.total
  isPullback_generic : IsPullback C₃.hom.generic (𝟙 N.generic) π.generic C₁.hom.generic

attribute [instance] Compactification.Refinement.isProper_p
  Compactification.Refinement.isProper_p'

/-- **Refinements from the total spaces.** A morphism `π : 𝒳₃ ⟶ 𝒳` of total spaces of
compactifications `C₃`, `C` of `N` over the trait, compatible with the inclusions of `N`, over
a proper `p : X₃ ⟶ X` under `Y` with `Y = X₃ ×_X Y`, compatible with the factorisations of the
identifications `ε` on the geometric generic fibres, and with `N = 𝒳₃ ×_𝒳 N`, induces a
refinement `C₃ ⟶ C`: the morphisms of geometric generic and special fibres are the base changes
of `π`, and the remaining cartesian squares are base changes of `N = 𝒳₃ ×_𝒳 N`. -/
lemma Compactification.nonempty_refinement {C₃ C : h.Compactification} (p : C₃.X ⟶ C.X)
    [IsProper p.left] (hι : C₃.ι ≫ p = C.ι)
    (hιpb : IsPullback C₃.ι.left (𝟙 Y.left) p.left C.ι.left)
    (π : C₃.model.total ⟶ C.model.total) (htot : C₃.hom.total ≫ π = C.hom.total)
    (hq : C₃.qc = π ≫ C.qc) {e : C.model.total ⟶ C.X.left} (he : C.model.j ≫ e = C.model.ε)
    (hε : C₃.model.j ≫ π ≫ e = C₃.model.ε ≫ p.left)
    (hpb : IsPullback C₃.hom.total (𝟙 N.total) π C.hom.total) :
    Nonempty (C₃.Refinement C) := by
  have hC := C.isTraitModelOfBase.isTraitModelOver
  have hC₃ := C₃.isTraitModelOfBase.isTraitModelOver
  let πg : C₃.model.generic ⟶ C.model.generic := hC.isPullback_j.lift (C₃.model.j ≫ π) C₃.gc
    (by rw [Category.assoc, ← hq, hC₃.isPullback_j.w])
  let p'l : C₃.X'.left ⟶ C.X'.left := hC.isPullback_i.lift (C₃.model.i ≫ π) C₃.X'.hom
    (by rw [Category.assoc, ← hq, hC₃.isPullback_i.w])
  have hp'l : p'l ≫ C.X'.hom = C₃.X'.hom := hC.isPullback_i.lift_snd _ _ _
  have : IsProper (p'l ≫ C.X'.hom) := by
    rw [hp'l, ← toPoint_left]
    infer_instance
  have : IsProper p'l := IsProper.of_comp p'l C.X'.hom
  let p' : C₃.X' ⟶ C.X' := Over.homMk p'l hp'l
  have : IsProper p'.left := ‹IsProper p'l›
  have hπg : πg ≫ C.model.j = C₃.model.j ≫ π := hC.isPullback_j.lift_fst _ _ _
  have hp'i : p'l ≫ C.model.i = C₃.model.i ≫ π := hC.isPullback_i.lift_fst _ _ _
  let φ : C₃.model.Hom C.model p.left p'.left :=
    { total := π
      generic := πg
      comm_j := hπg
      comm_i := hp'i
      comm_ε := by rw [← he, ← Category.assoc, hπg, Category.assoc, hε] }
  have hR_i : IsPullback C₃.model.i p'l π C.model.i := by
    refine IsPullback.of_bot ?_ hp'i.symm hC.isPullback_i
    rw [hp'l, ← hq]
    exact hC₃.isPullback_i
  have hR_j : IsPullback C₃.model.j πg π C.model.j := by
    refine IsPullback.of_bot ?_ hπg.symm hC.isPullback_j
    rw [hC.isPullback_j.lift_snd, ← hq]
    exact hC₃.isPullback_j
  have hι' : C₃.ι'.left ≫ p'l = C.ι'.left := by
    refine hC.isPullback_i.hom_ext ?_ ?_
    · rw [Category.assoc, hp'i, ← Category.assoc, C₃.hom.comm_i, Category.assoc, htot,
        C.hom.comm_i]
    · rw [Category.assoc, hp'l, Over.w C₃.ι', Over.w C.ι']
  have hgen : C₃.hom.generic ≫ πg = C.hom.generic := by
    refine hC.isPullback_j.hom_ext ?_ ?_
    · rw [Category.assoc, hπg, ← Category.assoc, C₃.hom.comm_j, Category.assoc, htot,
        C.hom.comm_j]
    · rw [Category.assoc, hC.isPullback_j.lift_snd, ← C₃.g_eq]
      exact C.g_eq
  exact ⟨{ p := p
           p' := p'
           π := φ
           ι_comp := hι
           ι'_comp := Over.OverMorphism.ext hι'
           hom_total_comp := htot
           hom_generic_comp := hgen
           qc_eq := hq
           gc_eq := (hC.isPullback_j.lift_snd _ _ _).symm
           isPullback_ι := hιpb
           isPullback_ι' := hpb.of_id_of_isPullback hR_i C₃.hom.comm_i C.hom.comm_i hι'
           isPullback_total := hpb
           isPullback_generic := hpb.of_id_of_isPullback hR_j C₃.hom.comm_j C.hom.comm_j hgen }⟩

/-- **The generic fibre of `N` in a compactification.** Over the generic point `Spec K` of the
trait, `N` is the inverse image of `N ⊆ 𝒳` along `X₃ ×_k Spec K ⟶ X ×_k Spec K ≅ 𝒳 ×_S Spec K`,
for `p : X₃ ⟶ X` under `Y` with `Y = X₃ ×_X Y`. The key point is that `(e, q) : 𝒳 ⟶ X ×_k S`
restricts on `N ×_S Spec K` to `N ⟶ Y ⟶ X`, as it does on the geometric generic fibre, which is
faithfully flat over `N ×_S Spec K`. -/
lemma Compactification.isPullback_traitGenericSpec (C : h.Compactification)
    {eN : N.total ⟶ Y.left} (heN : N.j ≫ eN = N.ε) (heN' : eN ≫ Y.hom = q ≫ traitToBase k k')
    {X₃ : Over (Spec (.of k))} {ι₃ : Y ⟶ X₃} {p : X₃ ⟶ C.X} (hι : ι₃ ≫ p = C.ι)
    (hιpb : IsPullback ι₃.left (𝟙 Y.left) p.left C.ι.left) {e : C.model.total ⟶ C.X.left}
    (he : C.model.j ≫ e = C.model.ε)
    {σ : pullback C.X.hom (traitGenericSpec k' ≫ traitToBase k k') ⟶ C.model.total}
    (hσe : σ ≫ e = pullback.fst _ _)
    (hσ : IsPullback σ (pullback.snd _ _) C.qc (traitGenericSpec k')) :
    IsPullback
      (pullback.map q (traitGenericSpec k') X₃.hom (traitGenericSpec k' ≫ traitToBase k k')
        (eN ≫ ι₃.left) (𝟙 _) (traitToBase k k') (by rw [Category.assoc, Over.w ι₃, heN'])
        (by rw [Category.id_comp]))
      (pullback.fst q (traitGenericSpec k'))
      (pullback.map X₃.hom (traitGenericSpec k' ≫ traitToBase k k') C.X.hom
        (traitGenericSpec k' ≫ traitToBase k k') p.left (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, Over.w p]) (by rw [Category.comp_id, Category.id_comp]) ≫ σ)
      C.hom.total := by
  have hN := h.isTraitModelOver
  have hιl : ι₃.left ≫ p.left = C.ι.left := by rw [← Over.comp_left, hι]
  let nC := pullback.map q (traitGenericSpec k') C.X.hom (traitGenericSpec k' ≫ traitToBase k k')
    (eN ≫ C.ι.left) (𝟙 _) (traitToBase k k') (by rw [Category.assoc, Over.w C.ι, heN'])
    (by rw [Category.id_comp])
  have hnC_fst : nC ≫ pullback.fst _ _ = pullback.fst _ _ ≫ eN ≫ C.ι.left :=
    pullback.lift_fst _ _ _
  have hnC_snd : nC ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 _ := pullback.lift_snd _ _ _
  -- `(e, q)` restricts to `N ⟶ Y ⟶ X` over `Spec K`, as it does over `Spec Ω`
  have hepi : pullback.fst q (traitGenericSpec k') ≫ C.hom.total ≫ e =
      pullback.fst q (traitGenericSpec k') ≫ eN ≫ C.ι.left := by
    have := hN.epi_lift_traitGenericPointToSpec
    rw [← cancel_epi (pullback.lift N.j (g ≫ traitGenericPointToSpec k') _),
      pullback.lift_fst_assoc, pullback.lift_fst_assoc, ← Category.assoc N.j, ← C.hom.comm_j,
      Category.assoc, he,
      C.hom.comm_ε, ← Category.assoc N.j eN, heN]
  have hbot : IsPullback nC (pullback.fst q (traitGenericSpec k')) σ C.hom.total := by
    refine IsPullback.of_right ?_ ?_ hσ.flip
    · rw [hnC_snd, Category.comp_id, ← C.q_eq]
      exact (IsPullback.of_hasPullback q (traitGenericSpec k')).flip
    · refine eq_of_isPullback_traitGenericSpec hσe hσ (t := pullback.snd _ _) ?_ ?_ ?_
      · rw [Category.assoc, hσ.w, ← Category.assoc, hnC_snd, Category.comp_id]
      · rw [Category.assoc, ← C.q_eq, pullback.condition]
      · rw [Category.assoc, hσe, hnC_fst, Category.assoc, hepi]
  have htop : IsPullback
      (pullback.map q (traitGenericSpec k') X₃.hom (traitGenericSpec k' ≫ traitToBase k k')
        (eN ≫ ι₃.left) (𝟙 _) (traitToBase k k') (by rw [Category.assoc, Over.w ι₃, heN'])
        (by rw [Category.id_comp])) (𝟙 _)
      (pullback.map X₃.hom (traitGenericSpec k' ≫ traitToBase k k') C.X.hom
        (traitGenericSpec k' ≫ traitToBase k k') p.left (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, Over.w p]) (by rw [Category.comp_id, Category.id_comp])) nC := by
    have hX : IsPullback (pullback.fst X₃.hom (traitGenericSpec k' ≫ traitToBase k k'))
        (pullback.map X₃.hom (traitGenericSpec k' ≫ traitToBase k k') C.X.hom
          (traitGenericSpec k' ≫ traitToBase k k') p.left (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, Over.w p]) (by rw [Category.comp_id, Category.id_comp]))
        p.left (pullback.fst _ _) := by
      refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
      rw [pullback.lift_snd, Category.comp_id, Over.w p]
      exact IsPullback.of_hasPullback _ _
    refine IsPullback.of_right ?_ ?_ hX
    · rw [pullback.lift_fst, hnC_fst, ← Category.assoc, ← Category.assoc]
      exact (IsPullback.id_vert _).paste_horiz hιpb
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp,
          hnC_fst, Category.assoc, Category.assoc, hιl]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp,
          hnC_snd, Category.comp_id]
  simpa using htop.paste_vert hbot

/-- **Common refinement of two compactifications** (the first step of the proof of blueprint
`prose-E-15`): any two compactifications `C₁`, `C₂` of a trait model over the base
have a common refinement `C₃`.

Construction: with `X₃` a dense compactification of `(ι₁, ι₂) : Y ⟶ X₁ ×_k X₂` (so that
`Y = X₃ ×_{X₁} Y`, `Y` being closed in the inverse image of `Y ×_k X₂` as the section of a
separated morphism, and open and dense), glue the total space of `N` and the generic fibre
`X₃ ×_k K` (`K = Frac k'⟦t⟧`) along `N_K` and compactify over
`(X₃ ×_k S) ×_S 𝒳₁ ×_S 𝒳₂`, where `𝒳ᵢ ×_S K ≅ Xᵢ ×_k K` by fpqc descent from the geometric
generic fibres; the compactification is an isomorphism `X₃ ×_k K` over the generic point, and the
inclusion of `N` is the inverse image of `N ⊆ P_i`, being open and closed in it and dense. -/
theorem Compactification.exists_refinement (C₁ C₂ : h.Compactification) :
    ∃ C₃ : h.Compactification, Nonempty (C₃.Refinement C₁) ∧ Nonempty (C₃.Refinement C₂) := by
  have hN := h.isTraitModelOver
  have := hN.locallyOfFiniteType
  have := hN.quasiCompact
  have := hN.isSeparated
  obtain ⟨eN, heN, heN'⟩ := h.exists_comp_ε
  obtain ⟨u, hu, hu₁, hu₂⟩ := h.exists_openImmersion
  obtain ⟨e₁, he₁, he₁'⟩ := C₁.isTraitModelOfBase.exists_comp_ε
  obtain ⟨e₂, he₂, he₂'⟩ := C₂.isTraitModelOfBase.exists_comp_ε
  obtain ⟨σ₁, hσ₁e, hσ₁⟩ :=
    C₁.isTraitModelOfBase.exists_isPullback_traitGenericSpec C₁.isPullback_ε he₁ he₁'
  obtain ⟨σ₂, hσ₂e, hσ₂⟩ :=
    C₂.isTraitModelOfBase.exists_isPullback_traitGenericSpec C₂.isPullback_ε he₂ he₂'
  obtain ⟨X₃, _, ι₃, _, p₁, p₂, _, _, hι₁, hι₂, hιpb₁, hιpb₂⟩ :=
    Compactification.exists_common C₁ C₂
  -- `W = (X₃ ×_k S) ×_S (𝒳₁ ×_S 𝒳₂)`, proper over `S`
  let z₃ := pullback.snd X₃.hom (traitToBase k k')
  let zT : pullback C₁.qc C₂.qc ⟶ trait k' := pullback.fst C₁.qc C₂.qc ≫ C₁.qc
  let zW : pullback z₃ zT ⟶ trait k' := pullback.fst z₃ zT ≫ z₃
  let pr₁ : pullback z₃ zT ⟶ C₁.model.total := pullback.snd z₃ zT ≫ pullback.fst _ _
  let pr₂ : pullback z₃ zT ⟶ C₂.model.total := pullback.snd z₃ zT ≫ pullback.snd _ _
  let pr₃ : pullback z₃ zT ⟶ X₃.left := pullback.fst z₃ zT ≫ pullback.fst _ _
  have hpr₁ : pr₁ ≫ C₁.qc = zW := by
    rw [Category.assoc]
    exact pullback.condition.symm
  have hpr₂ : pr₂ ≫ C₂.qc = zW := by
    rw [Category.assoc, ← pullback.condition (f := C₁.qc) (g := C₂.qc)]
    exact pullback.condition.symm
  have hpr₃ : pr₃ ≫ X₃.hom = zW ≫ traitToBase k k' := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  have : IsProper zT := inferInstanceAs (IsProper (pullback.fst C₁.qc C₂.qc ≫ C₁.qc))
  have : IsProper zW := inferInstanceAs (IsProper (pullback.fst z₃ zT ≫ z₃))
  have := QuasiCompact.compactSpace_of_compactSpace zW
  have := quasiSeparatedSpace_of_quasiSeparated zW
  -- the morphism `F : 𝒩 ⟶ W`
  let F : N.total ⟶ pullback z₃ zT :=
    pullback.lift (pullback.lift (eN ≫ ι₃.left) q (by rw [Category.assoc, Over.w ι₃, heN']))
      (pullback.lift C₁.hom.total C₂.hom.total (by rw [← C₁.q_eq, ← C₂.q_eq]))
      (by
        simp [z₃, zT, ← C₁.q_eq, -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])
  have hF₁ : F ≫ pr₁ = C₁.hom.total := by simp [F, pr₁]
  have hF₂ : F ≫ pr₂ = C₂.hom.total := by simp [F, pr₂]
  have hFz : F ≫ zW = q := by
    simp [F, zW, z₃, -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase]
  have : QuasiCompact F := by
    have : QuasiCompact (F ≫ zW) := by
      rw [hFz]
      infer_instance
    exact QuasiCompact.of_comp F zW
  have : IsSeparated F := by
    have : IsSeparated (F ≫ zW) := by
      rw [hFz]
      infer_instance
    exact IsSeparated.of_comp F zW
  have : LocallyOfFiniteType F := by
    have : LocallyOfFiniteType (F ≫ zW) := by
      rw [hFz]
      infer_instance
    exact locallyOfFiniteType_of_comp F zW
  -- the generic fibre `V = X₃ ×_k Spec K`, embedded in `W ×_S Spec K` as a graph
  let F' : pullback q (traitGenericSpec k') ⟶
      pullback X₃.hom (traitGenericSpec k' ≫ traitToBase k k') :=
    pullback.map q (traitGenericSpec k') X₃.hom (traitGenericSpec k' ≫ traitToBase k k')
      (eN ≫ ι₃.left) (𝟙 _) (traitToBase k k') (by rw [Category.assoc, Over.w ι₃, heN'])
      (by rw [Category.id_comp])
  have hF'fst : F' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ eN ≫ ι₃.left :=
    pullback.lift_fst _ _ _
  have hF'snd : F' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 _ := pullback.lift_snd _ _ _
  let p₁K := pullback.map X₃.hom (traitGenericSpec k' ≫ traitToBase k k') C₁.X.hom
    (traitGenericSpec k' ≫ traitToBase k k') p₁.left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, Over.w p₁]) (by rw [Category.comp_id, Category.id_comp])
  let p₂K := pullback.map X₃.hom (traitGenericSpec k' ≫ traitToBase k k') C₂.X.hom
    (traitGenericSpec k' ≫ traitToBase k k') p₂.left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, Over.w p₂]) (by rw [Category.comp_id, Category.id_comp])
  have hQ₁ : IsPullback F' (pullback.fst _ _) (p₁K ≫ σ₁) C₁.hom.total :=
    C₁.isPullback_traitGenericSpec heN heN' hι₁ hιpb₁ he₁ hσ₁e hσ₁
  have hQ₂ : IsPullback F' (pullback.fst _ _) (p₂K ≫ σ₂) C₂.hom.total :=
    C₂.isPullback_traitGenericSpec heN heN' hι₂ hιpb₂ he₂ hσ₂e hσ₂
  have hp₁K : p₁K ≫ σ₁ ≫ C₁.qc = pullback.snd _ _ ≫ traitGenericSpec k' := by
    rw [hσ₁.w, pullback.lift_snd_assoc, Category.comp_id]
  have hp₂K : p₂K ≫ σ₂ ≫ C₂.qc = pullback.snd _ _ ≫ traitGenericSpec k' := by
    rw [hσ₂.w, pullback.lift_snd_assoc, Category.comp_id]
  let κW : pullback X₃.hom (traitGenericSpec k' ≫ traitToBase k k') ⟶ pullback z₃ zT :=
    pullback.lift
      (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ traitGenericSpec k')
        (by rw [pullback.condition, Category.assoc]))
      (pullback.lift (p₁K ≫ σ₁) (p₂K ≫ σ₂) (by rw [Category.assoc, Category.assoc, hp₁K, hp₂K]))
      (by rw [pullback.lift_snd, pullback.lift_fst_assoc, Category.assoc, hp₁K])
  have hκW₁ : κW ≫ pr₁ = p₁K ≫ σ₁ := by simp [κW, pr₁]
  have hκW₂ : κW ≫ pr₂ = p₂K ≫ σ₂ := by simp [κW, pr₂]
  have hκW₃ : κW ≫ pr₃ = pullback.fst _ _ := by simp [κW, pr₃]
  have hκWz : κW ≫ zW = pullback.snd _ _ ≫ traitGenericSpec k' := by
    simp [κW, zW, z₃, -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase]
  let κ : pullback X₃.hom (traitGenericSpec k' ≫ traitToBase k k') ⟶
      pullback zW (traitGenericSpec k') := pullback.lift κW (pullback.snd _ _) hκWz
  have hκfst : κ ≫ pullback.fst _ _ = κW := pullback.lift_fst _ _ _
  have hκsnd : κ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion κ := by
    let ρ : pullback zW (traitGenericSpec k') ⟶
        pullback X₃.hom (traitGenericSpec k' ≫ traitToBase k k') :=
      pullback.lift (pullback.fst _ _ ≫ pr₃) (pullback.snd _ _)
        (by rw [Category.assoc, hpr₃, pullback.condition_assoc])
    have : IsSeparated (ρ ≫ pullback.snd _ _) := by
      rw [pullback.lift_snd]
      infer_instance
    have : IsSeparated ρ := IsSeparated.of_comp ρ (pullback.snd _ _)
    have : IsClosedImmersion (κ ≫ ρ) := by
      have : κ ≫ ρ = 𝟙 _ := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, reassoc_of% hκfst, hκW₃, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, hκsnd, Category.id_comp]
      rw [this]
      infer_instance
    exact IsClosedImmersion.of_comp κ ρ
  -- `N ×_S Spec K` is the inverse image of `V ⊆ W ×_S Spec K` in `N`
  have H : IsPullback (pullback.fst q (traitGenericSpec k')) (F' ≫ κ) F
      (pullback.fst zW (traitGenericSpec k')) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback zW (traitGenericSpec k'))
    · rw [Category.assoc, hκsnd, hF'snd, Category.comp_id, hFz]
      exact IsPullback.of_hasPullback q (traitGenericSpec k')
    · rw [Category.assoc, hκfst]
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, κW, F, pullback.lift_fst, hF'fst]
        · simp only [Category.assoc, κW, F, pullback.lift_fst, pullback.lift_snd,
            pullback.condition, reassoc_of% hF'snd]
      · apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]
          exact (congrArg (_ ≫ ·) hF₁).trans (hQ₁.w.symm.trans (congrArg (F' ≫ ·) hκW₁.symm))
        · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]
          exact (congrArg (_ ≫ ·) hF₂).trans (hQ₂.w.symm.trans (congrArg (F' ≫ ·) hκW₂.symm))
  -- `F'` is an open immersion, by descent from the geometric generic fibre
  let φgen : N.generic ⟶ pullback X₃.hom (traitGenericPoint k' ≫ traitToBase k k') :=
    pullback.lift (N.ε ≫ ι₃.left) g (by
      rw [Category.assoc, Over.w ι₃, ← hu₁, Category.assoc, pullback.condition,
        ← Category.assoc, hu₂])
  have hφgen_fst : φgen ≫ pullback.fst _ _ = N.ε ≫ ι₃.left := pullback.lift_fst _ _ _
  have hφgen_snd : φgen ≫ pullback.snd _ _ = g := pullback.lift_snd _ _ _
  have : IsOpenImmersion φgen := by
    have : φgen = u ≫ pullback.map Y.hom (traitGenericPoint k' ≫ traitToBase k k') X₃.hom
        (traitGenericPoint k' ≫ traitToBase k k') ι₃.left (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, Over.w ι₃]) (by rw [Category.comp_id, Category.id_comp]) := by
      apply pullback.hom_ext
      · rw [hφgen_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hu₁]
      · rw [hφgen_snd, Category.assoc, pullback.lift_snd, Category.comp_id, hu₂]
    rw [this]
    infer_instance
  have hP : IsPullback (pullback.lift N.j (g ≫ traitGenericPointToSpec k') (by
        rw [Category.assoc, traitGenericPointToSpec_traitGenericSpec, hN.isPullback_j.w]) :
        N.generic ⟶ pullback q (traitGenericSpec k')) φgen F'
      (traitGenericBaseChangeMap k' X₃) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_traitGenericBaseChangeMap k' X₃)
    · rw [hφgen_snd, hF'snd, Category.comp_id]
      exact hN.isPullback_traitGenericPointToSpec
    · apply pullback.hom_ext
      · rw [Category.assoc, hF'fst, pullback.lift_fst_assoc, reassoc_of% heN, Category.assoc,
          traitGenericBaseChangeMap_fst, hφgen_fst]
      · rw [Category.assoc, hF'snd, pullback.lift_snd_assoc, Category.comp_id, Category.assoc,
          traitGenericBaseChangeMap_snd, reassoc_of% hφgen_snd]
  have : IsOpenImmersion F' :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion) hP.flip
      (traitGenericBaseChangeMap_mem k' X₃) inferInstance
  -- the compactification `B` of `𝒩 ∪ V` over `W`, which is `V` over `Spec K`
  obtain ⟨B, c, p, s, hc, hp, hcp, has, hps, hdense⟩ :=
    exists_isProper_isPullback_of_isClosedImmersion H
  have : IsOpenImmersion c := hc
  have : IsProper p := hp
  let qc : B ⟶ trait k' := p ≫ zW
  have hqcP : IsProper qc := inferInstanceAs (IsProper (p ≫ zW))
  have hqc : q = c ≫ qc := by rw [← hFz, ← hcp, Category.assoc]
  have hsp₁ : s ≫ p ≫ pr₁ = p₁K ≫ σ₁ := by rw [reassoc_of% hps.w, reassoc_of% hκfst, hκW₁]
  have hsp₂ : s ≫ p ≫ pr₂ = p₂K ≫ σ₂ := by rw [reassoc_of% hps.w, reassoc_of% hκfst, hκW₂]
  have hsp₃ : s ≫ p ≫ pr₃ = pullback.fst _ _ := by
    rw [reassoc_of% hps.w, reassoc_of% hκfst, hκW₃]
  -- the geometric generic fibre `X₃ ×_k Spec Ω` of `B`
  have hMcj : IsPullback (traitGenericBaseChangeMap k' X₃ ≫ s) (pullback.snd _ _) qc
      (traitGenericPoint k') := by
    have h₂ := hps.paste_vert (IsPullback.of_hasPullback zW (traitGenericSpec k'))
    rw [hκsnd] at h₂
    have h₃ := (isPullback_traitGenericBaseChangeMap k' X₃).paste_horiz h₂
    rwa [traitGenericPointToSpec_traitGenericSpec] at h₃
  have hcomm_j : φgen ≫ traitGenericBaseChangeMap k' X₃ ≫ s = N.j ≫ c := by
    rw [← Category.assoc, ← hP.w, Category.assoc, ← has, pullback.lift_fst_assoc]
  let C₃ : h.Compactification := Compactification.ofIsPullback ι₃ c qc _ hMcj (p ≫ pr₃)
    (by rw [Category.assoc, hsp₃, traitGenericBaseChangeMap_fst])
    ((Category.assoc _ _ _).trans ((congrArg (p ≫ ·) hpr₃).trans (Category.assoc _ _ _).symm))
    hqc hcomm_j
  -- the refinements `C₃ ⟶ C₁` and `C₃ ⟶ C₂`
  have hsep₁ : IsSeparated (p ≫ pr₁) := by
    have : IsSeparated ((p ≫ pr₁) ≫ C₁.qc) := by
      rw [Category.assoc, hpr₁]
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
  have hε₁ : (traitGenericBaseChangeMap k' X₃ ≫ s) ≫ (p ≫ pr₁) ≫ e₁ =
      pullback.fst _ _ ≫ p₁.left := by
    rw [Category.assoc, Category.assoc, reassoc_of% hsp₁, hσ₁e, pullback.lift_fst,
      traitGenericBaseChangeMap_fst_assoc]
  have hε₂ : (traitGenericBaseChangeMap k' X₃ ≫ s) ≫ (p ≫ pr₂) ≫ e₂ =
      pullback.fst _ _ ≫ p₂.left := by
    rw [Category.assoc, Category.assoc, reassoc_of% hsp₂, hσ₂e, pullback.lift_fst,
      traitGenericBaseChangeMap_fst_assoc]
  exact ⟨C₃, Compactification.nonempty_refinement (C₃ := C₃) p₁ hι₁ hιpb₁ (p ≫ pr₁) htot₁
      ((congrArg (p ≫ ·) hpr₁).symm.trans (Category.assoc _ _ _).symm) he₁ hε₁ hpb₁,
    Compactification.nonempty_refinement (C₃ := C₃) p₂ hι₂ hιpb₂ (p ≫ pr₂) htot₂
      ((congrArg (p ≫ ·) hpr₂).symm.trans (Category.assoc _ _ _).symm) he₂ hε₂ hpb₂⟩

end IsTraitModelOfBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.CategoryTheory.Filtered.Basic

/-!
# Twisted sections over inverse limits

Let `f : V ⟶ Y` be quasi-compact and quasi-separated and `c` a descent cocycle on the constant
sheaf `S_V` (`AlgebraicGeometry.IsDescentCocycle`). For a cofiltered system `(Dⱼ)` of quasi-compact
quasi-separated `Y`-schemes with affine transition maps and limit `D`, every twisted section of
`c` over `D` comes from a twisted section over some `Dⱼ`
(`AlgebraicGeometry.IsTwistedSection.exists_of_isLimit`): a locally constant function on the
quasi-compact `V ×_Y D = lim V ×_Y Dⱼ` is given by finitely many quasi-compact open and closed
subsets, which come from a finite stage, and the compatibility with `c`, an equality of two
locally constant functions on `(V ×_Y D) ×_D (V ×_Y D)`, holds at a finite stage, a closed
subset with empty preimage in the limit being empty at a finite stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section Limit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)] {c : Cone D}

/-- **Locally constant functions on a stage of a limit which agree on the limit agree at a
finite stage.** Let `(Dᵢ)` be a cofiltered system of quasi-compact schemes with affine transition
maps. Two locally constant functions on `Dᵢ` which agree on the limit agree on some `Dⱼ`: the
locus where they differ is closed, and its preimages in the `Dⱼ` are quasi-compact closed
subsets, which are empty at some stage as soon as their limit is. -/
lemma Scheme.exists_comp_eq_comp_of_isLimit_of_isLocallyConstant (hc : IsLimit c) {i : I}
    {S : Type*} {φ₁ φ₂ : D.obj i → S} (h₁ : IsLocallyConstant φ₁) (h₂ : IsLocallyConstant φ₂)
    (h : φ₁ ∘ (c.π.app i).base = φ₂ ∘ (c.π.app i).base) :
    ∃ (j : I) (g : j ⟶ i), φ₁ ∘ (D.map g).base = φ₂ ∘ (D.map g).base := by
  by_contra! H
  have hcl (j : I) (g : j ⟶ i) :
      IsClosed {x | φ₁ ((D.map g).base x) ≠ φ₂ ((D.map g).base x)} := by
    have hl : IsLocallyConstant fun x ↦ (φ₁ ((D.map g).base x), φ₂ ((D.map g).base x)) :=
      (h₁.comp_continuous (D.map g).base.hom.continuous).prodMk
        (h₂.comp_continuous (D.map g).base.hom.continuous)
    exact (hl {p | p.1 = p.2}).isClosed_compl
  obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' D c hc (j := i)
    (fun j g ↦ {x | φ₁ ((D.map g).base x) ≠ φ₂ ((D.map g).base x)}) hcl
    (fun j g ↦ Function.ne_iff.1 (H j g)) (fun j g ↦ (hcl j g).isCompact)
    (fun j j' g g' x hx ↦ by
      simp only [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_apply] at hx
      exact hx)
  exact hs i (𝟙 i) (by simpa using congrFun h s)

/-- **Locally constant functions on a limit come from a finite stage.** Let `(Dᵢ)` be a
cofiltered system of quasi-compact quasi-separated schemes with affine transition maps. Every
locally constant function on the limit is the pullback of a locally constant function on some
`Dᵢ`: it has finitely many values, its fibres are quasi-compact opens, which come from
quasi-compact opens of some `Dᵢ`, and these cover `Dᵢ` and are pairwise disjoint at some
stage. -/
lemma Scheme.exists_isLocallyConstant_comp_eq_of_isLimit [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : IsLimit c) {S : Type*} {σ : c.pt → S} (hσ : IsLocallyConstant σ) :
    ∃ (i : I) (σᵢ : D.obj i → S), IsLocallyConstant σᵢ ∧ σᵢ ∘ (c.π.app i).base = σ := by
  classical
  have := Scheme.compactSpace_of_isLimit D c hc
  let R := Set.range σ
  have : Finite R := hσ.range_finite.to_subtype
  have := Fintype.ofFinite R
  let U (r : R) : c.pt.Opens := ⟨σ ⁻¹' {r.1}, hσ.isOpen_fiber _⟩
  have hU (r : R) : IsCompact (U r : Set c.pt) := (hσ.isClosed_fiber _).isCompact
  choose i V hVc hVU using fun r ↦ exists_preimage_eq D c hc (U r) (hU r)
  obtain ⟨j₀, hj₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let g (r : R) : j₀ ⟶ i r := (hj₀ (Finset.mem_image_of_mem i (Finset.mem_univ r))).some
  let V' (r : R) : (D.obj j₀).Opens := D.map (g r) ⁻¹ᵁ V r
  have hV'c (r : R) : IsCompact (V' r : Set (D.obj j₀)) :=
    QuasiCompact.isCompact_preimage (f := D.map (g r)) _ (V r).2 (hVc r)
  have hV'U (r : R) : c.π.app j₀ ⁻¹ᵁ V' r = U r := by
    rw [← hVU r, ← Scheme.Hom.comp_preimage, c.w]
  -- the properties to be achieved at a finite stage
  let P : Option (R × R) → ∀ {j : I}, (j ⟶ j₀) → Prop
    | none, _, a => D.map a ⁻¹ᵁ (⨆ r, V' r) = ⊤
    | some (r, r'), _, a => r ≠ r' → D.map a ⁻¹ᵁ (V' r ⊓ V' r') ≤ D.map a ⁻¹ᵁ ⊥
  have hP (k : Option (R × R)) {j j' : I} (b : j' ⟶ j) (a : j ⟶ j₀) (hk : P k a) :
      P k (b ≫ a) := by
    rcases k with _ | ⟨r, r'⟩
    · simp only [P, CategoryTheory.Functor.map_comp, Scheme.Hom.comp_preimage] at hk ⊢
      rw [hk, Scheme.Hom.preimage_top]
    · intro hrr
      simp only [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ (hk hrr)
  obtain ⟨j, a, ha⟩ := CategoryTheory.IsCofiltered.exists_forall_of_finite P hP fun k ↦ by
    rcases k with _ | ⟨r, r'⟩
    · refine exists_map_eq_top D c hc _ ?_
      rw [Scheme.Hom.preimage_iSup, eq_top_iff]
      rintro x -
      rw [TopologicalSpace.Opens.mem_iSup]
      refine ⟨⟨σ x, x, rfl⟩, ?_⟩
      rw [hV'U]
      rfl
    · by_cases hrr : r = r'
      · exact ⟨j₀, 𝟙 j₀, fun h ↦ (h hrr).elim⟩
      · obtain ⟨j, a, ha⟩ := exists_map_preimage_le_map_preimage D c hc (U := V' r ⊓ V' r')
          (QuasiSeparatedSpace.inter_isCompact _ _ (V' r).2 (hV'c r) (V' r').2 (hV'c r'))
          (V := ⊥) (by
            rw [Scheme.Hom.preimage_inf, hV'U r, hV'U r']
            intro x hx
            exact (hrr (Subtype.ext (hx.1.symm.trans hx.2))).elim)
        exact ⟨j, a, fun _ ↦ ha⟩
  have hcov (x : D.obj j) : ∃ r, (D.map a).base x ∈ V' r := by
    have hx : x ∈ D.map a ⁻¹ᵁ (⨆ r, V' r) := by
      rw [ha none]
      trivial
    obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.1
      (by simpa only [Scheme.Hom.preimage_iSup] using hx)
    exact ⟨r, hr⟩
  have huniq (x : D.obj j) (r r' : R) (hr : (D.map a).base x ∈ V' r)
      (hr' : (D.map a).base x ∈ V' r') : r = r' := by
    by_contra hrr
    have := ha (some (r, r')) hrr ⟨hr, hr'⟩
    simp at this
  let σᵢ (x : D.obj j) : S := (hcov x).choose.1
  have hσᵢ (x : D.obj j) (r : R) (hr : (D.map a).base x ∈ V' r) : σᵢ x = r.1 :=
    congrArg Subtype.val (huniq x _ _ (hcov x).choose_spec hr)
  refine ⟨j, σᵢ, ?_, funext fun y ↦ ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨r, hr⟩ := hcov x
    filter_upwards [((V' r).2.preimage (D.map a).base.hom.continuous).mem_nhds hr] with x' hx'
    rw [hσᵢ x' r hx', hσᵢ x r hr]
  · refine hσᵢ _ ⟨σ y, y, rfl⟩ ?_
    have : y ∈ c.π.app j₀ ⁻¹ᵁ V' ⟨σ y, y, rfl⟩ := by
      rw [hV'U]
      rfl
    rwa [← c.w a, Scheme.Hom.comp_preimage] at this

end Limit

section BaseChange

variable {Y V : Scheme.{u}} (f : V ⟶ Y)

/-- The map `R_{T'} ⟶ R_T` of the schemes of pairs `R_T = (V ×_Y T) ×_T (V ×_Y T)` is the base
change of `V ×_Y T' ⟶ V ×_Y T` along the first projection. -/
lemma isPullback_pairMapRight {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') :
    IsPullback (pairMapRight f t ht) (pullback.fst _ _) (pullback.fst _ _)
      (pullbackMapRight f t ht) := by
  have h₁ := (IsPullback.of_hasPullback (pullback.snd f π') (pullback.snd f π')).flip.paste_horiz
    (isPullback_pullbackMapRight (f := f) t ht)
  refine IsPullback.of_right ?_ (pairMapRight_fst t ht)
    (IsPullback.of_hasPullback (pullback.snd f π) (pullback.snd f π)).flip
  rw [pairMapRight_snd, pullbackMapRight_snd]
  exact h₁

variable {J : Type u} [SmallCategory J] {D : J ⥤ Scheme.{u}} (π : ∀ j, D.obj j ⟶ Y)
  (hπ : ∀ {i j} (g : i ⟶ j), D.map g ≫ π j = π i)

/-- The base change `j ↦ V ×_Y Dⱼ` along `f : V ⟶ Y` of a diagram `(Dⱼ)` of `Y`-schemes. -/
@[simps]
noncomputable def pullbackRightDiagram : J ⥤ Scheme.{u} where
  obj j := pullback f (π j)
  map g := pullbackMapRight f (D.map g) (hπ g)
  map_id j := pullback.hom_ext (by simp) (by simp)
  map_comp g g' := pullback.hom_ext (by simp) (by simp)

/-- The diagram `j ↦ (V ×_Y Dⱼ) ×_{Dⱼ} (V ×_Y Dⱼ)` of the schemes of pairs of a diagram `(Dⱼ)` of
`Y`-schemes. -/
@[simps]
noncomputable def pairRightDiagram : J ⥤ Scheme.{u} where
  obj j := pullback (pullback.snd f (π j)) (pullback.snd f (π j))
  map g := pairMapRight f (D.map g) (hπ g)
  map_id j := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp
  map_comp g g' := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp

variable {C : Cone D} (π' : C.pt ⟶ Y) (hπ' : ∀ j, C.π.app j ≫ π j = π')

/-- The cone `V ×_Y lim Dⱼ` over the diagram `j ↦ V ×_Y Dⱼ`. -/
@[simps]
noncomputable def pullbackRightCone : Cone (pullbackRightDiagram f π hπ) where
  pt := pullback f π'
  π :=
    { app j := pullbackMapRight f (C.π.app j) (hπ' j)
      naturality i j g := pullback.hom_ext (by simp) (by simp) }

/-- The cone `R_{lim Dⱼ}` over the diagram of the schemes of pairs `j ↦ R_{Dⱼ}`. -/
@[simps]
noncomputable def pairRightCone : Cone (pairRightDiagram f π hπ) where
  pt := pullback (pullback.snd f π') (pullback.snd f π')
  π :=
    { app j := pairMapRight f (C.π.app j) (hπ' j)
      naturality i j g := by
        apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp }

/-- The projection `V ×_Y Dⱼ ⟶ Dⱼ`, as a natural transformation. -/
noncomputable def pullbackRightDiagramSnd : pullbackRightDiagram f π hπ ⟶ D where
  app j := pullback.snd f (π j)
  naturality _ _ g := pullbackMapRight_snd (D.map g) (hπ g)

/-- The first projection `R_{Dⱼ} ⟶ V ×_Y Dⱼ`, as a natural transformation. -/
noncomputable def pairRightDiagramFst :
    pairRightDiagram f π hπ ⟶ pullbackRightDiagram f π hπ where
  app j := pullback.fst (pullback.snd f (π j)) (pullback.snd f (π j))
  naturality _ _ g := pairMapRight_fst (D.map g) (hπ g)

variable {π hπ π' hπ'}

/-- **Base change commutes with cofiltered limits**: `V ×_Y lim Dⱼ = lim V ×_Y Dⱼ`. -/
noncomputable def isLimitPullbackRightCone [IsCofiltered J] (hC : IsLimit C) :
    IsLimit (pullbackRightCone f π hπ π' hπ') :=
  have := IsCofiltered.isConnected J
  isLimitOfIsPullbackOfIsConnected (pullbackRightDiagramSnd f π hπ) _ C
    { hom := pullback.snd f π'
      w j := (pullbackMapRight_snd (C.π.app j) (hπ' j)).symm }
    (fun j ↦ isPullback_pullbackMapRight (C.π.app j) (hπ' j)) hC

/-- The schemes of pairs commute with cofiltered limits: `R_{lim Dⱼ} = lim R_{Dⱼ}`. -/
noncomputable def isLimitPairRightCone [IsCofiltered J] (hC : IsLimit C) :
    IsLimit (pairRightCone f π hπ π' hπ') :=
  have := IsCofiltered.isConnected J
  isLimitOfIsPullbackOfIsConnected (pairRightDiagramFst f π hπ) _
    (pullbackRightCone f π hπ π' hπ')
    { hom := pullback.fst _ _
      w j := (pairMapRight_fst (C.π.app j) (hπ' j)).symm }
    (fun j ↦ isPullback_pairMapRight f (C.π.app j) (hπ' j)) (isLimitPullbackRightCone f hC)

end BaseChange

variable {Y V : Scheme.{u}} {f : V ⟶ Y}

/-- **Twisted sections over a limit come from a finite stage.** Let `f : V ⟶ Y` be quasi-compact
and quasi-separated, `c` a descent cocycle and `(Dⱼ)` a cofiltered system of quasi-compact
quasi-separated `Y`-schemes with affine transition maps. Every twisted section of `c` over the
limit `lim Dⱼ` is the pullback of a twisted section over some `Dⱼ`. -/
theorem IsTwistedSection.exists_of_isLimit [QuasiCompact f] [QuasiSeparated f] {S : Type*}
    {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c) {J : Type u} [SmallCategory J]
    [IsCofiltered J] {D : J ⥤ Scheme.{u}} [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    {C : Cone D} (hC : IsLimit C) (π : ∀ j, D.obj j ⟶ Y)
    (hπ : ∀ {i j} (g : i ⟶ j), D.map g ≫ π j = π i) (π' : C.pt ⟶ Y)
    (hπ' : ∀ j, C.π.app j ≫ π j = π') {σ : ↥(pullback f π') → S}
    (hσ : IsTwistedSection f c π' σ) :
    ∃ (j : J) (σⱼ : ↥(pullback f (π j)) → S), IsTwistedSection f c (π j) σⱼ ∧
      σⱼ ∘ (pullbackMapRight f (C.π.app j) (hπ' j)).base = σ := by
  have : ∀ j, CompactSpace ((pullbackRightDiagram f π hπ).obj j) := fun j ↦
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (π j))
  have : ∀ j, QuasiSeparatedSpace ((pullbackRightDiagram f π hπ).obj j) := fun j ↦
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (π j))
  have hEa : ∀ {i j} (g : i ⟶ j), IsAffineHom ((pullbackRightDiagram f π hπ).map g) := fun g ↦
    MorphismProperty.of_isPullback (isPullback_pullbackMapRight (D.map g) (hπ g)).flip
      inferInstance
  have : ∀ j, CompactSpace ((pairRightDiagram f π hπ).obj j) := fun j ↦
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst (pullback.snd f (π j)) (pullback.snd f (π j)))
  have : ∀ {i j} (g : i ⟶ j), IsAffineHom ((pairRightDiagram f π hπ).map g) := fun g ↦
    MorphismProperty.of_isPullback (isPullback_pairMapRight f (D.map g) (hπ g)).flip
      (hEa g)
  obtain ⟨j₀, σ₀, hσ₀, hσ₀σ⟩ := Scheme.exists_isLocallyConstant_comp_eq_of_isLimit
    (isLimitPullbackRightCone f (hπ := hπ) (hπ' := hπ') hC) (σ := σ) hσ.1
  -- the two sides of the compatibility with `c` at the stage `j₀`
  let φ₁ (w : ↥(pullback (pullback.snd f (π j₀)) (pullback.snd f (π j₀)))) : S :=
    σ₀ ((pullback.fst (pullback.snd f (π j₀)) (pullback.snd f (π j₀))).base w)
  let φ₂ (w : ↥(pullback (pullback.snd f (π j₀)) (pullback.snd f (π j₀)))) : S :=
    c ((twistedPairMap f (π j₀)).base w)
      (σ₀ ((pullback.snd (pullback.snd f (π j₀)) (pullback.snd f (π j₀))).base w))
  have hφ₁ : IsLocallyConstant φ₁ := hσ₀.comp_continuous
    (pullback.fst (pullback.snd f (π j₀)) (pullback.snd f (π j₀))).base.hom.continuous
  have hφ₂ : IsLocallyConstant φ₂ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w₀
    have h₁ := (IsLocallyConstant.iff_eventually_eq _).1
      (hσ₀.comp_continuous
        (pullback.snd (pullback.snd f (π j₀)) (pullback.snd f (π j₀))).base.hom.continuous) w₀
    have h₂ := (IsLocallyConstant.iff_eventually_eq _).1
      ((hc.isLocallyConstant
        (σ₀ ((pullback.snd (pullback.snd f (π j₀)) (pullback.snd f (π j₀))).base w₀)))
          |>.comp_continuous
        (twistedPairMap f (π j₀)).base.hom.continuous) w₀
    filter_upwards [h₁, h₂] with w hw₁ hw₂
    simp only [Function.comp_apply] at hw₁ hw₂
    simp only [φ₂, hw₁]
    exact hw₂
  have hσ₀' (x : ↥(pullback f π')) :
      σ₀ ((pullbackMapRight f (C.π.app j₀) (hπ' j₀)).base x) = σ x :=
    congrFun hσ₀σ x
  have hagree : φ₁ ∘ (pairMapRight f (C.π.app j₀) (hπ' j₀)).base =
      φ₂ ∘ (pairMapRight f (C.π.app j₀) (hπ' j₀)).base := by
    funext (w : ↥(pullback (pullback.snd f π') (pullback.snd f π')))
    have e₁ := congrArg (fun m ↦ m.base w) (pairMapRight_fst (f := f) (C.π.app j₀) (hπ' j₀))
    have e₂ := congrArg (fun m ↦ m.base w) (pairMapRight_snd (f := f) (C.π.app j₀) (hπ' j₀))
    have e₃ := congrArg (fun m ↦ m.base w)
      (pairMapRight_twistedPairMap (f := f) (C.π.app j₀) (hπ' j₀))
    simp only [Scheme.Hom.comp_apply] at e₁ e₂ e₃
    simp only [Function.comp_apply, φ₁, φ₂, e₁, e₂, e₃, hσ₀']
    exact hσ.2 w
  obtain ⟨j, g, hg⟩ := Scheme.exists_comp_eq_comp_of_isLimit_of_isLocallyConstant
    (isLimitPairRightCone f (hπ := hπ) (hπ' := hπ') hC) hφ₁ hφ₂ hagree
  refine ⟨j, σ₀ ∘ (pullbackMapRight f (D.map g) (hπ g)).base,
    ⟨hσ₀.comp_continuous (pullbackMapRight f (D.map g) (hπ g)).base.hom.continuous,
      fun w ↦ ?_⟩, funext fun x ↦ ?_⟩
  · have e₁ := congrArg (fun m ↦ m.base w) (pairMapRight_fst (f := f) (D.map g) (hπ g))
    have e₂ := congrArg (fun m ↦ m.base w) (pairMapRight_snd (f := f) (D.map g) (hπ g))
    have e₃ := congrArg (fun m ↦ m.base w) (pairMapRight_twistedPairMap (f := f) (D.map g) (hπ g))
    simp only [Scheme.Hom.comp_apply] at e₁ e₂ e₃
    have hg' : φ₁ ∘ (pairMapRight f (D.map g) (hπ g)).base =
        φ₂ ∘ (pairMapRight f (D.map g) (hπ g)).base := hg
    have := congrFun hg' w
    simp only [Function.comp_apply, φ₁, φ₂, e₁, e₂, e₃] at this
    exact this
  · have e : pullbackMapRight f (C.π.app j) (hπ' j) ≫ pullbackMapRight f (D.map g) (hπ g) =
        pullbackMapRight f (C.π.app j₀) (hπ' j₀) :=
      pullback.hom_ext (by simp) (by simp)
    have := congrArg (fun m ↦ m.base x) e
    simp only [Scheme.Hom.comp_apply] at this
    simp only [Function.comp_apply, this, hσ₀']

end AlgebraicGeometry

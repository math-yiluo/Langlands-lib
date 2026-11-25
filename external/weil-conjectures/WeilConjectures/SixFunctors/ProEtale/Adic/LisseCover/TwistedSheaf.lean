/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSection
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Gluing

/-!
# The étale sheaf of sections of a descent cocycle

Let `f : V ⟶ Y` be weakly étale and `c` a descent cocycle on the constant sheaf `S_V`
(`AlgebraicGeometry.IsDescentCocycle`). The sections of the sheaf of sets defined by `c` over
étale `Y`-schemes (`AlgebraicGeometry.IsTwistedSection`) form a sheaf of sets on the small étale
site of `Y` (`AlgebraicGeometry.twistedSectionsPresheaf`,
`AlgebraicGeometry.isSheaf_twistedSectionsPresheaf`): sections glue along jointly surjective
étale families, the base changes of étale morphisms being open maps.

Twisted sections can be computed on any weakly étale `W ⟶ V` whose image covers the image of the
base (`AlgebraicGeometry.IsTwistedSection.bijective_restrict`): a section over a smaller cover
extends uniquely, by transport along the cocycle.
-/

@[expose] public section

universe u w

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {Y V : Scheme.{u}} {f : V ⟶ Y}

/-- The map `V ×_Y T' ⟶ V ×_Y T` induced by a morphism `t : T' ⟶ T` over `Y`. -/
noncomputable abbrev pullbackMapRight {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (f : V ⟶ Y) (t : T' ⟶ T) (ht : t ≫ π = π') : pullback f π' ⟶ pullback f π :=
  pullback.map f π' f π (𝟙 V) t (𝟙 Y) (by simp) (by simp [ht])

/-- Points of `V ×_Y T` lift along `V ×_Y T' ⟶ V ×_Y T` over any preimage in `T'` of their
image in `T`. -/
lemma exists_pullbackMapRight_eq {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (t : T' ⟶ T) (ht : t ≫ π = π') (x : ↥(pullback f π)) (t' : T')
    (h : t.base t' = (pullback.snd f π).base x) :
    ∃ x' : ↥(pullback f π'), (pullbackMapRight f t ht).base x' = x ∧
      (pullback.snd f π').base x' = t' := by
  obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f π)
    (g := t) x t' h.symm
  let L : pullback (pullback.snd f π) t ⟶ pullback f π' :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition, ← ht, pullback.condition_assoc])
  have hL₁ : L ≫ pullbackMapRight f t ht = pullback.fst _ _ := by
    apply pullback.hom_ext
    · simp [L]
    · simp [L, pullback.condition]
  have hL₂ : L ≫ pullback.snd f π' = pullback.snd _ _ := pullback.lift_snd _ _ _
  refine ⟨L.base y, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hL₁, hy₁]
  · rw [← Scheme.Hom.comp_apply, hL₂, hy₂]

@[reassoc (attr := simp)]
lemma pullbackMapRight_fst {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pullbackMapRight f t ht ≫ pullback.fst f π = pullback.fst f π' := by
  simp [pullbackMapRight]

@[reassoc (attr := simp)]
lemma pullbackMapRight_snd {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pullbackMapRight f t ht ≫ pullback.snd f π = pullback.snd f π' ≫ t := by
  simp [pullbackMapRight]

lemma pullbackMapRight_id {T : Scheme.{u}} (π : T ⟶ Y) (h : 𝟙 T ≫ π = π) :
    pullbackMapRight f (𝟙 T) h = 𝟙 _ :=
  pullback.hom_ext (by simp) (by simp)

lemma pullbackMapRight_comp {T T' T'' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    {π'' : T'' ⟶ Y} (t : T' ⟶ T) (ht : t ≫ π = π') (t' : T'' ⟶ T') (ht' : t' ≫ π' = π'')
    (h : (t' ≫ t) ≫ π = π'') :
    pullbackMapRight f (t' ≫ t) h = pullbackMapRight f t' ht' ≫ pullbackMapRight f t ht :=
  pullback.hom_ext (by simp) (by simp)

/-- The map `R_{T'} ⟶ R_T` of the schemes of pairs `R_T = (V ×_Y T) ×_T (V ×_Y T)` induced by a
morphism `t : T' ⟶ T` over `Y`. -/
noncomputable abbrev pairMapRight {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (f : V ⟶ Y) (t : T' ⟶ T) (ht : t ≫ π = π') :
    pullback (pullback.snd f π') (pullback.snd f π') ⟶
      pullback (pullback.snd f π) (pullback.snd f π) :=
  pullback.map _ _ _ _ (pullbackMapRight f t ht) (pullbackMapRight f t ht) t (by simp)
    (by simp)

lemma pairMapRight_fst {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pairMapRight f t ht ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullbackMapRight f t ht := by
  simp [pairMapRight]

lemma pairMapRight_snd {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pairMapRight f t ht ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullbackMapRight f t ht := by
  simp [pairMapRight]

lemma pairMapRight_twistedPairMap {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') : pairMapRight f t ht ≫ twistedPairMap f π = twistedPairMap f π' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [reassoc_of% pairMapRight_fst]
    simp
  · simp only [Category.assoc, pullback.lift_snd]
    rw [reassoc_of% pairMapRight_snd]
    simp

/-- Points of `R_T` lift along `R_{T'} ⟶ R_T` over any preimage in `T'` of their image in
`T`. -/
lemma exists_pairMapRight_eq {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (t : T' ⟶ T) (ht : t ≫ π = π') (w : ↥(pullback (pullback.snd f π) (pullback.snd f π)))
    (t' : T') (h : t.base t' =
      (pullback.fst (pullback.snd f π) (pullback.snd f π) ≫ pullback.snd f π).base w) :
    ∃ w' : ↥(pullback (pullback.snd f π') (pullback.snd f π')),
      (pairMapRight f t ht).base w' = w := by
  set τ := pullback.fst (pullback.snd f π) (pullback.snd f π) ≫ pullback.snd f π
  obtain ⟨y, hy₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := τ) (g := t) w t' h.symm
  have e : pullback.fst τ t ≫ τ = pullback.snd τ t ≫ t := pullback.condition
  have h₁ : (pullback.fst τ t ≫ pullback.fst (pullback.snd f π) (pullback.snd f π) ≫
      pullback.fst f π) ≫ f = pullback.snd τ t ≫ π' := by
    rw [Category.assoc, Category.assoc, pullback.condition (f := f) (g := π), ← ht,
      ← Category.assoc (pullback.snd τ t), ← e]
    simp [τ]
  have h₂ : (pullback.fst τ t ≫ pullback.snd (pullback.snd f π) (pullback.snd f π) ≫
      pullback.fst f π) ≫ f = pullback.snd τ t ≫ π' := by
    rw [Category.assoc, Category.assoc, pullback.condition (f := f) (g := π),
      ← pullback.condition_assoc (f := pullback.snd f π) (g := pullback.snd f π), ← ht,
      ← Category.assoc (pullback.snd τ t), ← e]
    simp [τ]
  let L : pullback τ t ⟶ pullback (pullback.snd f π') (pullback.snd f π') :=
    pullback.lift (pullback.lift _ _ h₁) (pullback.lift _ _ h₂) (by simp)
  have hL : L ≫ pairMapRight f t ht = pullback.fst τ t := by
    apply pullback.hom_ext
    · rw [Category.assoc, pairMapRight_fst]
      apply pullback.hom_ext
      · simp [L]
      · simp only [L, Category.assoc, pullbackMapRight_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
        rw [← pullback.condition (f := τ) (g := t)]
    · rw [Category.assoc, pairMapRight_snd]
      apply pullback.hom_ext
      · simp [L]
      · simp only [L, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd]
        rw [← pullback.condition (f := τ) (g := t)]
        simp only [τ, pullback.condition]
  exact ⟨L.base y, by rw [← Scheme.Hom.comp_apply, hL, hy₁]⟩

variable (f) in
/-- The presheaf of sections of the sheaf of sets defined by a descent cocycle `c`, on the
small étale site of `Y`. -/
noncomputable def twistedSectionsPresheaf {S : Type w} (c : ↥(pullback f f) → S → S) :
    Y.Etaleᵒᵖ ⥤ Type (max u w) where
  obj U := {σ : ↥(pullback f U.unop.hom) → S // IsTwistedSection f c U.unop.hom σ}
  map {U U'} g := ↾fun σ ↦
    ⟨σ.1 ∘ (pullbackMapRight f g.unop.left (MorphismProperty.Over.w g.unop)).base,
      σ.2.comp g.unop.left (MorphismProperty.Over.w g.unop)⟩
  map_id U := by
    ext σ : 3
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (𝟙 U.unop.left) _).base = σ.1
    rw [pullbackMapRight_id]
    rfl
  map_comp {U U' U''} g g' := by
    ext σ : 3
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (g'.unop.left ≫ g.unop.left) _).base =
      (σ.1 ∘ (pullbackMapRight f g.unop.left _).base) ∘ (pullbackMapRight f g'.unop.left _).base
    rw [pullbackMapRight_comp g.unop.left (MorphismProperty.Over.w g.unop) g'.unop.left
      (MorphismProperty.Over.w g'.unop)]
    rfl

lemma twistedSectionsPresheaf_map_coe {S : Type w} (c : ↥(pullback f f) → S → S)
    {U U' : Y.Etale} (g : U' ⟶ U) (σ : (twistedSectionsPresheaf f c).obj (op U)) :
    ((twistedSectionsPresheaf f c).map g.op σ).1 =
      σ.1 ∘ (pullbackMapRight f g.left (MorphismProperty.Over.w g)).base :=
  rfl

/-- The square of `V ×_Y T' ⟶ V ×_Y T` over `t : T' ⟶ T` is cartesian. -/
lemma isPullback_pullbackMapRight {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T)
    (ht : t ≫ π = π') :
    IsPullback (pullbackMapRight f t ht) (pullback.snd f π') (pullback.snd f π) t := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f π) (v₁₃ := f) (h₂₂ := π) ?_ (by simp)
    (IsPullback.of_hasPullback f π)
  rw [pullbackMapRight_fst, ht]
  exact IsPullback.of_hasPullback f π'

instance {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y} (t : T' ⟶ T) [Etale t]
    (ht : t ≫ π = π') : Etale (pullbackMapRight f t ht) :=
  MorphismProperty.of_isPullback (isPullback_pullbackMapRight t ht).flip ‹_›

/-- The morphisms of the small étale site are étale. -/
lemma etale_left {U U' : Y.Etale} (g : U' ⟶ U) : Etale g.left := by
  have : Etale (g.left ≫ U.hom) := by rw [MorphismProperty.Over.w g]; exact U'.prop
  exact Etale.of_comp g.left U.hom

variable (f) in
/-- **Twisted sections glue along jointly surjective étale families.** -/
lemma isSheafFor_ofArrows_twistedSectionsPresheaf {S : Type w} (c : ↥(pullback f f) → S → S)
    {U : Y.Etale} {ι : Type*} (Ui : ι → Y.Etale) (π : ∀ i, Ui i ⟶ U)
    (hsurj : ∀ u : U.left, ∃ i, ∃ x, (π i).left.base x = u) :
    (Presieve.ofArrows Ui π).IsSheafFor (twistedSectionsPresheaf f c) := by
  classical
  have := fun i ↦ etale_left (π i)
  let M (i : ι) := pullbackMapRight f (π i).left (MorphismProperty.Over.w (π i))
  have hMs (i : ι) : M i ≫ pullback.snd f U.hom = pullback.snd f (Ui i).hom ≫ (π i).left :=
    pullbackMapRight_snd _ _
  have hMf (i : ι) : M i ≫ pullback.fst f U.hom = pullback.fst f (Ui i).hom :=
    pullbackMapRight_fst _ _
  have hM (p : ↥(pullback f U.hom)) : ∃ i, ∃ q, (M i).base q = p := by
    obtain ⟨i, u, hu⟩ := hsurj ((pullback.snd f U.hom).base p)
    obtain ⟨q, hq, -⟩ := exists_pullbackMapRight_eq (f := f) (π i).left
      (MorphismProperty.Over.w (π i)) p u hu
    exact ⟨i, q, hq⟩
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- compatibility at points
  have hcompat (i j : ι) (q : ↥(pullback f (Ui i).hom)) (q' : ↥(pullback f (Ui j).hom))
      (h : (M i).base q = (M j).base q') : (x i).1 q = (x j).1 q' := by
    have : Etale (pullback.fst (π i).left (π j).left ≫ (Ui i).hom) := by
      have := etale_left (π j)
      infer_instance
    let Z : Y.Etale := Scheme.Etale.mk (pullback.fst (π i).left (π j).left ≫ (Ui i).hom)
    let g₁ : Z ⟶ Ui i := MorphismProperty.Over.homMk (pullback.fst _ _) rfl trivial
    let g₂ : Z ⟶ Ui j := MorphismProperty.Over.homMk (pullback.snd _ _) (by
      change pullback.snd _ _ ≫ (Ui j).hom = pullback.fst _ _ ≫ (Ui i).hom
      rw [← MorphismProperty.Over.w (π i), ← MorphismProperty.Over.w (π j),
        pullback.condition_assoc]) trivial
    have hg : g₁ ≫ π i = g₂ ≫ π j :=
      MorphismProperty.Over.Hom.ext pullback.condition
    have e := congrArg Subtype.val (hx i j Z g₁ g₂ hg)
    obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := M i) (g := M j) q q' h
    have hc : (pullback.fst (M i) (M j) ≫ pullback.snd f (Ui i).hom) ≫ (π i).left =
        (pullback.snd (M i) (M j) ≫ pullback.snd f (Ui j).hom) ≫ (π j).left := by
      rw [Category.assoc, Category.assoc, ← hMs, ← hMs]
      exact pullback.condition_assoc _
    let L : pullback (M i) (M j) ⟶ pullback f Z.hom :=
      pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.lift _ _ hc) (by
        change _ = _ ≫ pullback.fst _ _ ≫ (Ui i).hom
        simp [pullback.condition])
    have hL₁ : L ≫ pullbackMapRight f g₁.left (MorphismProperty.Over.w g₁) =
        pullback.fst (M i) (M j) := pullback.hom_ext (by simp [L]) (by simp [L, g₁])
    have hL₂ : L ≫ pullbackMapRight f g₂.left (MorphismProperty.Over.w g₂) =
        pullback.snd (M i) (M j) := by
      apply pullback.hom_ext
      · have := pullback.condition_assoc (f := M i) (g := M j) (pullback.fst f U.hom)
        rw [hMf, hMf] at this
        rw [Category.assoc, pullbackMapRight_fst]
        exact (pullback.lift_fst _ _ _).trans this
      · simp [L, g₂]
    have e' := congrFun e (L.base y)
    simp only [twistedSectionsPresheaf_map_coe, Function.comp_apply] at e'
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hL₁, hL₂, hy₁, hy₂] at e'
    exact e'
  choose ii qq hqq using hM
  let σ : ↥(pullback f U.hom) → S := fun p ↦ (x (ii p)).1 (qq p)
  have hσM (i : ι) (q : ↥(pullback f (Ui i).hom)) : σ ((M i).base q) = (x i).1 q :=
    hcompat _ _ _ _ (hqq _)
  have hσ : IsTwistedSection f c U.hom σ := by
    refine ⟨?_, fun w ↦ ?_⟩
    · refine IsLocallyConstant.iff_isOpen_fiber.2 fun a ↦ ?_
      have : σ ⁻¹' {a} = ⋃ i, (M i).base '' ((x i).1 ⁻¹' {a}) := by
        ext p
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_image]
        refine ⟨fun hp ↦ ⟨ii p, qq p, hp, hqq p⟩, ?_⟩
        rintro ⟨i, q, hq, rfl⟩
        rw [hσM, hq]
      rw [this]
      exact isOpen_iUnion fun i ↦ (M i).isOpenMap _ ((x i).2.1.isOpen_fiber a)
    · obtain ⟨i, u, hu⟩ := hsurj
        ((pullback.fst (pullback.snd f U.hom) (pullback.snd f U.hom) ≫ pullback.snd f U.hom).base
          w)
      obtain ⟨w', hw'⟩ := exists_pairMapRight_eq (f := f) (π i).left
        (MorphismProperty.Over.w (π i)) w u hu
      have h₁ := congrArg (fun φ ↦ φ.base w') (pairMapRight_fst (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      have h₂ := congrArg (fun φ ↦ φ.base w') (pairMapRight_snd (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      have h₃ := congrArg (fun φ ↦ φ.base w') (pairMapRight_twistedPairMap (f := f) (π i).left
        (MorphismProperty.Over.w (π i)))
      simp only [Scheme.Hom.comp_apply, hw'] at h₁ h₂ h₃
      rw [h₁, h₂, h₃, hσM, hσM]
      exact (x i).2.2 w'
  refine ⟨⟨σ, hσ⟩, fun i ↦ Subtype.ext (funext fun q ↦ hσM i q), fun t ht ↦ ?_⟩
  refine Subtype.ext (funext fun p ↦ ?_)
  obtain ⟨i, q, rfl⟩ : ∃ i q, (M i).base q = p := ⟨ii p, qq p, hqq p⟩
  have := congrFun (congrArg Subtype.val (ht i)) q
  simp only [twistedSectionsPresheaf_map_coe, Function.comp_apply] at this
  change t.1 ((M i).base q) = σ ((M i).base q)
  rw [this, hσM]

variable (f) in
/-- **The sections of a descent cocycle form a sheaf on the small étale site.** -/
theorem isSheaf_twistedSectionsPresheaf {S : Type w} (c : ↥(pullback f f) → S → S) :
    Presheaf.IsSheaf Y.smallEtaleTopology (twistedSectionsPresheaf f c) := by
  rw [isSheaf_iff_isSheaf_of_type, Scheme.smallEtaleTopology,
    Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Presieve.isSheaf_pretopology]
  rintro U R ⟨hsurj, _⟩
  obtain ⟨ι, Ui, π, rfl⟩ := R.exists_eq_ofArrows
  refine isSheafFor_ofArrows_twistedSectionsPresheaf f c _ _ fun u ↦ ?_
  obtain ⟨_, _, ⟨⟨⟨⟨i⟩⟩⟩⟩, x, hx⟩ := hsurj u
  exact ⟨i, x, hx⟩

section Restrict

variable {W : Scheme.{u}} (j : W ⟶ V) {S : Type*}

/-- The map `W ×_Y W ⟶ V ×_Y V` induced by `j : W ⟶ V`. -/
noncomputable abbrev pairRestrict : pullback (j ≫ f) (j ≫ f) ⟶ pullback f f :=
  pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 Y) (by simp) (by simp)

variable (c : ↥(pullback f f) → S → S)

/-- The restriction of a descent cocycle along `j : W ⟶ V`. -/
noncomputable def restrictCocycle : ↥(pullback (j ≫ f) (j ≫ f)) → S → S :=
  fun z ↦ c ((pairRestrict j).base z)

/-- The map `W ×_Y T ⟶ V ×_Y T` induced by `j : W ⟶ V`. -/
noncomputable abbrev pullbackMapLeft {T : Scheme.{u}} (π : T ⟶ Y) :
    pullback (j ≫ f) π ⟶ pullback f π :=
  pullback.map (j ≫ f) π f π j (𝟙 T) (𝟙 Y) (by simp) (by simp)

variable {j c}

lemma IsDescentCocycle.restrict (hc : IsDescentCocycle f c) :
    IsDescentCocycle (j ≫ f) (restrictCocycle j c) := by
  refine ⟨fun s ↦ (hc.isLocallyConstant s).comp_continuous (pairRestrict j).base.hom.continuous,
    fun z ↦ hc.bijective _, fun w ↦ ?_, fun w ↦ ?_⟩
  · have e : pullback.diagonal (j ≫ f) ≫ pairRestrict j = j ≫ pullback.diagonal f :=
      pullback.hom_ext (by simp) (by simp)
    change c ((pullback.diagonal (j ≫ f) ≫ pairRestrict j).base w) = id
    rw [e, Scheme.Hom.comp_apply]
    exact hc.diagonal _
  · let T₃ : tripleProduct (j ≫ f) ⟶ tripleProduct f :=
      pullback.map _ _ _ _ (pairRestrict j) (pairRestrict j) j (by simp) (by simp)
    have e₁ : T₃ ≫ tripleProj₁₃ f = tripleProj₁₃ (j ≫ f) ≫ pairRestrict j := by
      apply pullback.hom_ext <;> simp [T₃]
    have e₂ : T₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pairRestrict j := by simp [T₃]
    have e₃ : T₃ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pairRestrict j := by simp [T₃]
    have := hc.cocycle (T₃.base w)
    simp only [← Scheme.Hom.comp_apply, e₁, e₂, e₃] at this
    exact this

lemma IsTwistedSection.restrict {T : Scheme.{u}} {π : T ⟶ Y} {σ : ↥(pullback f π) → S}
    (hσ : IsTwistedSection f c π σ) :
    IsTwistedSection (j ≫ f) (restrictCocycle j c) π (σ ∘ (pullbackMapLeft j π).base) := by
  let P₂ : pullback (pullback.snd (j ≫ f) π) (pullback.snd (j ≫ f) π) ⟶
      pullback (pullback.snd f π) (pullback.snd f π) :=
    pullback.map _ _ _ _ (pullbackMapLeft j π) (pullbackMapLeft j π) (𝟙 T) (by simp) (by simp)
  have e₁ : P₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullbackMapLeft j π := by simp [P₂]
  have e₂ : P₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullbackMapLeft j π := by simp [P₂]
  have e₃ : P₂ ≫ twistedPairMap f π = twistedPairMap (j ≫ f) π ≫ pairRestrict j := by
    apply pullback.hom_ext <;> simp [P₂]
  refine ⟨hσ.1.comp_continuous (pullbackMapLeft j π).base.hom.continuous, fun w ↦ ?_⟩
  have := hσ.2 (P₂.base w)
  simp only [← Scheme.Hom.comp_apply, e₁, e₂, e₃] at this
  exact this

variable {T : Scheme.{u}} {π : T ⟶ Y}

/-- Twisted sections are determined by their restrictions to a cover `W` of the image of the
base. -/
lemma IsTwistedSection.eq_of_restrict_eq (hcov : ∀ t, ∃ w, (j ≫ f).base w = π.base t)
    {σ₁ σ₂ : ↥(pullback f π) → S} (h₁ : IsTwistedSection f c π σ₁)
    (h₂ : IsTwistedSection f c π σ₂)
    (h : σ₁ ∘ (pullbackMapLeft j π).base = σ₂ ∘ (pullbackMapLeft j π).base) : σ₁ = σ₂ := by
  funext x
  obtain ⟨w, hw⟩ := hcov ((pullback.snd f π).base x)
  obtain ⟨x', -, hx'⟩ := Scheme.Pullback.exists_preimage_pullback (f := j ≫ f) (g := π) w _ hw
  have hx : (pullback.snd f π).base x =
      (pullback.snd f π).base ((pullbackMapLeft j π).base x') := by
    rw [← Scheme.Hom.comp_apply]
    simp [hx']
  obtain ⟨r, hr₁, hr₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd f π)
    (g := pullback.snd f π) x _ hx
  rw [← hr₁, h₁.2 r, h₂.2 r, hr₂]
  exact congrArg _ (congrFun h x')

/-- **Twisted sections extend from a cover `W` of the image of the base.** -/
lemma IsTwistedSection.exists_restrict_eq (hc : IsDescentCocycle f c)
    (hcov : ∀ t, ∃ w, (j ≫ f).base w = π.base t) [WeaklyEtale (j ≫ f)]
    [QuasiCompact (pullback.snd (j ≫ f) π)] {τ : ↥(pullback (j ≫ f) π) → S}
    (hτ : IsTwistedSection (j ≫ f) (restrictCocycle j c) π τ) :
    ∃ σ, IsTwistedSection f c π σ ∧ σ ∘ (pullbackMapLeft j π).base = τ := by
  classical
  set J := pullbackMapLeft j π
  set sP := pullback.snd f π
  set sW := pullback.snd (j ≫ f) π
  have hJs : J ≫ sP = sW := by simp [J, sP, sW]
  have hJf : J ≫ pullback.fst f π = pullback.fst (j ≫ f) π ≫ j := by simp [J]
  have hsW : Function.Surjective sW.base := by
    intro t
    obtain ⟨w, hw⟩ := hcov t
    obtain ⟨x', -, hx'⟩ := Scheme.Pullback.exists_preimage_pullback (f := j ≫ f) (g := π) w t hw
    exact ⟨x', hx'⟩
  have : Surjective sW := ⟨hsW⟩
  -- the cover `R' = (V ×_Y T) ×_T (W ×_Y T)` of `V ×_Y T`
  set a₁ := pullback.fst sP sW
  set a₂ := pullback.snd sP sW
  have hm : (a₁ ≫ pullback.fst f π) ≫ f = (a₂ ≫ pullback.fst (j ≫ f) π ≫ j) ≫ f := by
    simp only [Category.assoc, pullback.condition]
    simp only [← Category.assoc]
    exact congrArg (· ≫ π) pullback.condition
  set mR := pullback.lift (a₁ ≫ pullback.fst f π) (a₂ ≫ pullback.fst (j ≫ f) π ≫ j) hm
  let φ : ↥(pullback sP sW) → S := fun r ↦ c (mR.base r) (τ (a₂.base r))
  have hφlc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro r₀
    have h₁ := (IsLocallyConstant.iff_eventually_eq _).1
      (hτ.1.comp_continuous a₂.base.hom.continuous) r₀
    have h₂ := (IsLocallyConstant.iff_eventually_eq _).1
      ((hc.isLocallyConstant (τ (a₂.base r₀))).comp_continuous mR.base.hom.continuous) r₀
    filter_upwards [h₁, h₂] with r hr₁ hr₂
    simp only [Function.comp_apply] at hr₁ hr₂
    simp only [φ, hr₁, hr₂]
  -- `φ` is constant on the fibres of `a₁`
  have hφfib (r₁ r₂ : ↥(pullback sP sW)) (h : a₁.base r₁ = a₁.base r₂) : φ r₁ = φ r₂ := by
    obtain ⟨ρ, hρ₁, hρ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := a₁) (g := a₁) r₁ r₂ h
    set b₁ := pullback.fst a₁ a₁
    set b₂ := pullback.snd a₁ a₁
    have hb : (b₁ ≫ a₂) ≫ sW = (b₂ ≫ a₂) ≫ sW := by
      have e1 : a₂ ≫ sW = a₁ ≫ sP := pullback.condition.symm
      have e2 : b₁ ≫ a₁ = b₂ ≫ a₁ := pullback.condition
      rw [Category.assoc, Category.assoc, e1, reassoc_of% e2]
    let Ψ : pullback a₁ a₁ ⟶ pullback sW sW := pullback.lift _ _ hb
    have hΨ₁ : Ψ ≫ pullback.fst sW sW = b₁ ≫ a₂ := pullback.lift_fst _ _ _
    have hΨ₂ : Ψ ≫ pullback.snd sW sW = b₂ ≫ a₂ := pullback.lift_snd _ _ _
    have hm₂ : mR ≫ pullback.snd f f = a₂ ≫ pullback.fst (j ≫ f) π ≫ j := pullback.lift_snd _ _ _
    have hm₁ : mR ≫ pullback.fst f f = a₁ ≫ pullback.fst f π := pullback.lift_fst _ _ _
    have hW₁ : twistedPairMap (j ≫ f) π ≫ pairRestrict j ≫ pullback.fst f f =
        pullback.fst sW sW ≫ pullback.fst (j ≫ f) π ≫ j := by simp +zetaDelta
    have hW₂ : twistedPairMap (j ≫ f) π ≫ pairRestrict j ≫ pullback.snd f f =
        pullback.snd sW sW ≫ pullback.fst (j ≫ f) π ≫ j := by simp +zetaDelta
    have hΦ : (b₁ ≫ mR) ≫ pullback.snd f f =
        (Ψ ≫ twistedPairMap (j ≫ f) π ≫ pairRestrict j) ≫ pullback.fst f f := by
      rw [Category.assoc, hm₂, Category.assoc, Category.assoc, hW₁, reassoc_of% hΨ₁]
    let Φ : pullback a₁ a₁ ⟶ tripleProduct f := pullback.lift _ _ hΦ
    have hΦ₁₃ : Φ ≫ tripleProj₁₃ f = b₂ ≫ mR := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, hm₁,
          Category.assoc, hm₁, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ pullback.fst f π) pullback.condition
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc,
          Category.assoc, hW₂, Category.assoc, hm₂, reassoc_of% hΨ₂]
    have hco := hc.cocycle (Φ.base ρ)
    have hτρ := hτ.2 (Ψ.base ρ)
    have e₁ : Φ ≫ pullback.fst _ _ = b₁ ≫ mR := pullback.lift_fst _ _ _
    have e₂ : Φ ≫ pullback.snd _ _ = Ψ ≫ twistedPairMap (j ≫ f) π ≫ pairRestrict j :=
      pullback.lift_snd _ _ _
    simp only [← Scheme.Hom.comp_apply, hΦ₁₃, e₁, e₂] at hco
    have hco' := congrFun hco (τ (a₂.base (b₂.base ρ)))
    simp only [restrictCocycle] at hτρ
    simp only [Scheme.Hom.comp_apply, Function.comp_apply] at hco' hτρ
    have p₁ : (pullback.fst sW sW).base (Ψ.base ρ) = a₂.base (b₁.base ρ) := by
      rw [← Scheme.Hom.comp_apply, hΨ₁, Scheme.Hom.comp_apply]
    have p₂ : (pullback.snd sW sW).base (Ψ.base ρ) = a₂.base (b₂.base ρ) := by
      rw [← Scheme.Hom.comp_apply, hΨ₂, Scheme.Hom.comp_apply]
    rw [p₁, p₂] at hτρ
    change c (mR.base r₁) (τ (a₂.base r₁)) = c (mR.base r₂) (τ (a₂.base r₂))
    rw [← hρ₁, ← hρ₂, hco', hτρ]
  -- the descended function
  have ha₁ : Function.Surjective a₁.base := by
    intro x
    obtain ⟨x', hx'⟩ := hsW (sP.base x)
    obtain ⟨r, hr, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := sP) (g := sW) x x'
      hx'.symm
    exact ⟨r, hr⟩
  choose ra hra using ha₁
  let σ : ↥(pullback f π) → S := fun x ↦ φ (ra x)
  have hσa (r : ↥(pullback sP sW)) : σ (a₁.base r) = φ r := hφfib _ _ (hra _)
  have hcov' : Presieve.ofArrows (fun _ : Unit ↦ pullback sP sW) (fun _ ↦ a₁) ∈
      Scheme.proetalePrecoverage (pullback f π) := by
    rw [Presieve.ofArrows_pUnit]
    have : Surjective a₁ := ⟨fun x ↦ ⟨ra x, hra x⟩⟩
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  refine ⟨σ, ⟨IsLocallyConstant.iff_isOpen_fiber.2 fun s ↦ ?_, fun w ↦ ?_⟩, ?_⟩
  · refine Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage _ hcov' _ fun _ ↦ ?_
    have : a₁.base ⁻¹' (σ ⁻¹' {s}) = φ ⁻¹' {s} := by
      ext r
      simp +zetaDelta [hσa]
    rw [this]
    exact hφlc.isOpen_fiber s
  · -- the twisted condition, through a point of `R_T ×_{V ×_Y T} R'`
    set r₁ := pullback.fst sP sP
    set r₂ := pullback.snd sP sP
    obtain ⟨ζ, hζ₁, hζ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := r₂) (g := a₁) w
      (ra (r₂.base w)) (hra _).symm
    set d₁ := pullback.fst r₂ a₁
    set d₂ := pullback.snd r₂ a₁
    have e₀ : d₁ ≫ r₂ = d₂ ≫ a₁ := pullback.condition
    have eR : r₁ ≫ sP = r₂ ≫ sP := pullback.condition
    have eA : a₁ ≫ sP = a₂ ≫ sW := pullback.condition
    have hΛ : (d₁ ≫ r₁) ≫ sP = (d₂ ≫ a₂) ≫ sW := by
      rw [Category.assoc, eR, reassoc_of% e₀, eA, Category.assoc]
    let Λ : pullback r₂ a₁ ⟶ pullback sP sW := pullback.lift _ _ hΛ
    have hΛ₁ : Λ ≫ a₁ = d₁ ≫ r₁ := pullback.lift_fst _ _ _
    have hΛ₂ : Λ ≫ a₂ = d₂ ≫ a₂ := pullback.lift_snd _ _ _
    have hm₂ : mR ≫ pullback.snd f f = a₂ ≫ pullback.fst (j ≫ f) π ≫ j := pullback.lift_snd _ _ _
    have hm₁ : mR ≫ pullback.fst f f = a₁ ≫ pullback.fst f π := pullback.lift_fst _ _ _
    have hT₁ : twistedPairMap f π ≫ pullback.fst f f = r₁ ≫ pullback.fst f π :=
      pullback.lift_fst _ _ _
    have hT₂ : twistedPairMap f π ≫ pullback.snd f f = r₂ ≫ pullback.fst f π :=
      pullback.lift_snd _ _ _
    have hΦ' : (d₁ ≫ twistedPairMap f π) ≫ pullback.snd f f =
        (d₂ ≫ mR) ≫ pullback.fst f f := by
      rw [Category.assoc, hT₂, reassoc_of% e₀, Category.assoc, hm₁]
    let Φ' : pullback r₂ a₁ ⟶ tripleProduct f := pullback.lift _ _ hΦ'
    have hΦ'₁₃ : Φ' ≫ tripleProj₁₃ f = Λ ≫ mR := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, hT₁,
          Category.assoc, hm₁, reassoc_of% hΛ₁]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, hm₂,
          Category.assoc, hm₂, reassoc_of% hΛ₂]
    have hco := hc.cocycle (Φ'.base ζ)
    have e₁ : Φ' ≫ pullback.fst _ _ = d₁ ≫ twistedPairMap f π := pullback.lift_fst _ _ _
    have e₂ : Φ' ≫ pullback.snd _ _ = d₂ ≫ mR := pullback.lift_snd _ _ _
    simp only [← Scheme.Hom.comp_apply, hΦ'₁₃, e₁, e₂] at hco
    have hco' := congrFun hco (τ (a₂.base (d₂.base ζ)))
    simp only [Scheme.Hom.comp_apply, Function.comp_apply] at hco'
    have q₁ : r₁.base w = a₁.base (Λ.base ζ) := by
      rw [← Scheme.Hom.comp_apply, hΛ₁, Scheme.Hom.comp_apply, hζ₁]
    have q₂ : a₂.base (Λ.base ζ) = a₂.base (d₂.base ζ) := by
      rw [← Scheme.Hom.comp_apply, hΛ₂, Scheme.Hom.comp_apply]
    have q₃ : r₂.base w = a₁.base (d₂.base ζ) := by
      rw [← hζ₁, ← Scheme.Hom.comp_apply, e₀, Scheme.Hom.comp_apply]
    change σ (r₁.base w) = c ((twistedPairMap f π).base w) (σ (r₂.base w))
    rw [q₁, hσa, q₃, hσa]
    change c (mR.base (Λ.base ζ)) (τ (a₂.base (Λ.base ζ))) =
      c ((twistedPairMap f π).base w) (c (mR.base (d₂.base ζ)) (τ (a₂.base (d₂.base ζ))))
    rw [q₂, hco', hζ₁]
  · -- the restriction is `τ`
    funext x'
    have hδ : J ≫ sP = 𝟙 _ ≫ sW := by rw [hJs, Category.id_comp]
    let δ : pullback (j ≫ f) π ⟶ pullback sP sW := pullback.lift J (𝟙 _) hδ
    have h₁ : δ ≫ a₁ = J := pullback.lift_fst _ _ _
    have h₂ : δ ≫ a₂ = 𝟙 _ := pullback.lift_snd _ _ _
    have hm₂ : mR ≫ pullback.snd f f = a₂ ≫ pullback.fst (j ≫ f) π ≫ j := pullback.lift_snd _ _ _
    have hm₁ : mR ≫ pullback.fst f f = a₁ ≫ pullback.fst f π := pullback.lift_fst _ _ _
    have hδm : δ ≫ mR = (pullback.fst (j ≫ f) π ≫ j) ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · rw [Category.assoc, hm₁, reassoc_of% h₁, hJf]
        simp
      · rw [Category.assoc, hm₂, reassoc_of% h₂]
        simp
    simp only [Function.comp_apply]
    rw [← h₁, Scheme.Hom.comp_apply, hσa]
    change c (mR.base (δ.base x')) (τ (a₂.base (δ.base x'))) = τ x'
    rw [← Scheme.Hom.comp_apply, hδm, ← Scheme.Hom.comp_apply δ a₂, h₂, Scheme.Hom.comp_apply,
      hc.diagonal]
    rfl

end Restrict

end AlgebraicGeometry

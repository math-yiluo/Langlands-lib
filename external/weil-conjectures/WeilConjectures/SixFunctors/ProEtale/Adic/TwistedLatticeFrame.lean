/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf

/-!
# Twisted sections over schemes mapping to the cover

Let `f : V ⟶ Y` be a morphism and `c` a descent cocycle on the constant sheaf `S_V`
(`AlgebraicGeometry.IsDescentCocycle`). Over a `Y`-scheme `π : W ⟶ Y` which factors through `f`,
`π = a ≫ f`, the twisted sections of `c` are the locally constant functions `W → S`: a twisted
section `σ` is determined by its restriction `σ ∘ δ` along the section
`δ = (a, 𝟙) : W ⟶ V ×_Y W` (`AlgebraicGeometry.frameSection`), and conversely a locally
constant `τ : W → S` extends to the twisted section `(v, w) ↦ c(v, a w) (τ w)`
(`AlgebraicGeometry.frameExt`, `AlgebraicGeometry.isTwistedSection_frameExt`). These are inverse
bijections (`AlgebraicGeometry.frameEval_frameExt`, `AlgebraicGeometry.frameExt_frameEval`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Y V W : Scheme.{u}} (f : V ⟶ Y) {π : W ⟶ Y} (a : W ⟶ V) (ha : a ≫ f = π)

/-- The section `(a, 𝟙) : W ⟶ V ×_Y W` of the projection, for `π = a ≫ f`. -/
noncomputable abbrev frameSection : W ⟶ pullback f π :=
  pullback.lift a (𝟙 W) (by rw [ha, Category.id_comp])

/-- The map `V ×_Y W ⟶ V ×_Y V`, `(v, w) ↦ (v, a w)`. -/
noncomputable abbrev frameTransport : pullback f π ⟶ pullback f f :=
  pullback.lift (pullback.fst f π) (pullback.snd f π ≫ a) (by
    rw [Category.assoc, ha, pullback.condition])

@[reassoc (attr := simp)]
lemma frameSection_snd : frameSection f a ha ≫ pullback.snd f π = 𝟙 W :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma frameSection_fst : frameSection f a ha ≫ pullback.fst f π = a :=
  pullback.lift_fst _ _ _

lemma frameSection_frameTransport :
    frameSection f a ha ≫ frameTransport f a ha = a ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc,
      pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp,
      Category.assoc, pullback.diagonal_snd, Category.comp_id]

variable {S : Type*} (c : ↥(pullback f f) → S → S)

/-- The restriction of a function on `V ×_Y W` along `frameSection`. -/
noncomputable def frameEval (σ : ↥(pullback f π) → S) : W → S :=
  σ ∘ (frameSection f a ha).base

/-- The extension `(v, w) ↦ c(v, a w) (τ w)` of a function on `W` to `V ×_Y W`. -/
noncomputable def frameExt (τ : W → S) : ↥(pullback f π) → S :=
  fun x ↦ c ((frameTransport f a ha).base x) (τ ((pullback.snd f π).base x))

variable {f c}

lemma frameEval_frameExt (hc : IsDescentCocycle f c) (τ : W → S) :
    frameEval f a ha (frameExt f a ha c τ) = τ := by
  funext w
  have h₁ := congrArg (fun φ ↦ φ.base w) (frameSection_frameTransport f a ha)
  have h₂ := congrArg (fun φ ↦ φ.base w) (frameSection_snd f a ha)
  simp only [Scheme.Hom.comp_apply] at h₁ h₂
  simp only [frameEval, frameExt, Function.comp_apply]
  rw [h₁, h₂, hc.diagonal]
  rfl

lemma frameExt_frameEval {σ : ↥(pullback f π) → S} (hσ : IsTwistedSection f c π σ) :
    frameExt f a ha c (frameEval f a ha σ) = σ := by
  funext x
  let L : pullback f π ⟶ pullback (pullback.snd f π) (pullback.snd f π) :=
    pullback.lift (𝟙 _) (pullback.snd f π ≫ frameSection f a ha) (by
      rw [Category.id_comp, Category.assoc, frameSection_snd, Category.comp_id])
  have h₁ : L ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have h₂ : L ≫ pullback.snd _ _ = pullback.snd f π ≫ frameSection f a ha :=
    pullback.lift_snd _ _ _
  have h₃ : L ≫ twistedPairMap f π = frameTransport f a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, h₁, Category.id_comp,
        pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, h₂, Category.assoc,
        frameSection_fst, pullback.lift_snd]
  have e₁ := congrArg (fun φ ↦ φ.base x) h₁
  have e₂ := congrArg (fun φ ↦ φ.base x) h₂
  have e₃ := congrArg (fun φ ↦ φ.base x) h₃
  simp only [Scheme.Hom.comp_apply] at e₁ e₂ e₃
  have := hσ.2 (L.base x)
  rw [e₁, e₂, e₃] at this
  refine Eq.trans ?_ this.symm
  rfl

/-- A function `F(x, g x)` is locally constant if `g` is and every `F(·, s)` is. -/
lemma isLocallyConstant_apply_of_isLocallyConstant {X A B : Type*} [TopologicalSpace X]
    {F : X → A → B} (hF : ∀ s, IsLocallyConstant fun x ↦ F x s) {g : X → A}
    (hg : IsLocallyConstant g) : IsLocallyConstant fun x ↦ F x (g x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [(IsLocallyConstant.iff_eventually_eq g).1 hg x,
    (IsLocallyConstant.iff_eventually_eq _).1 (hF (g x)) x] with y hy₁ hy₂
  rw [hy₁, hy₂]

lemma isTwistedSection_frameExt (hc : IsDescentCocycle f c) {τ : W → S}
    (hτ : IsLocallyConstant τ) : IsTwistedSection f c π (frameExt f a ha c τ) := by
  refine ⟨?_, fun w ↦ ?_⟩
  · exact isLocallyConstant_apply_of_isLocallyConstant
      (fun s ↦ (hc.isLocallyConstant s).comp_continuous (frameTransport f a ha).base.hom.continuous)
      (hτ.comp_continuous (pullback.snd f π).base.hom.continuous)
  · set r₁ := pullback.fst (pullback.snd f π) (pullback.snd f π)
    set r₂ := pullback.snd (pullback.snd f π) (pullback.snd f π)
    have hr : r₁ ≫ pullback.snd f π = r₂ ≫ pullback.snd f π := pullback.condition
    let t : pullback (pullback.snd f π) (pullback.snd f π) ⟶ tripleProduct f :=
      pullback.lift (twistedPairMap f π) (r₂ ≫ frameTransport f a ha) (by
        rw [pullback.lift_snd, Category.assoc, pullback.lift_fst])
    have h₁₂ : t ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) = twistedPairMap f π :=
      pullback.lift_fst _ _ _
    have h₂₃ : t ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) =
        r₂ ≫ frameTransport f a ha :=
      pullback.lift_snd _ _ _
    have h₁₃ : t ≫ tripleProj₁₃ f = r₁ ≫ frameTransport f a ha := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, h₁₂, pullback.lift_fst,
          Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, h₂₃, Category.assoc,
          pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc, ← hr,
          Category.assoc]
    have e₁₂ := congrArg (fun φ ↦ φ.base w) h₁₂
    have e₂₃ := congrArg (fun φ ↦ φ.base w) h₂₃
    have e₁₃ := congrArg (fun φ ↦ φ.base w) h₁₃
    have er := congrArg (fun φ ↦ φ.base w) hr
    simp only [Scheme.Hom.comp_apply] at e₁₂ e₂₃ e₁₃ er
    have e := congrFun (hc.cocycle (t.base w)) (τ ((pullback.snd f π).base (r₂.base w)))
    rw [e₁₃, e₁₂, e₂₃] at e
    simp only [frameExt, Function.comp_apply] at e ⊢
    rw [er]
    exact e

/-- `frameEval` is natural: restricting along `g : W' ⟶ W` and then along the section of
`g ≫ a` is restricting along the section of `a` and then along `g`. -/
lemma frameEval_comp {W' : Scheme.{u}} {π' : W' ⟶ Y} (g : W' ⟶ W) (hg : g ≫ π = π')
    (σ : ↥(pullback f π) → S) :
    frameEval f (g ≫ a) (by rw [Category.assoc, ha, hg]) (σ ∘ (pullbackMapRight f g hg).base) =
      frameEval f a ha σ ∘ g.base := by
  have h : frameSection f (g ≫ a) (by rw [Category.assoc, ha, hg]) ≫ pullbackMapRight f g hg =
      g ≫ frameSection f a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackMapRight_fst, frameSection_fst, Category.assoc,
        frameSection_fst]
    · rw [Category.assoc, pullbackMapRight_snd, frameSection_snd_assoc,
        Category.assoc, frameSection_snd, Category.comp_id]
  funext w
  have e := congrArg (fun φ ↦ φ.base w) h
  simp only [Scheme.Hom.comp_apply] at e
  simp only [frameEval, Function.comp_apply]
  rw [e]

/-- `frameExt` is natural: extending `τ ∘ g` along the factorization `g ≫ a` is extending `τ`
along `a` and restricting along `g : W' ⟶ W`. -/
lemma frameExt_comp {W' : Scheme.{u}} {π' : W' ⟶ Y} (g : W' ⟶ W) (hg : g ≫ π = π')
    (τ : W → S) :
    frameExt f (g ≫ a) (by rw [Category.assoc, ha, hg]) c (τ ∘ g.base) =
      frameExt f a ha c τ ∘ (pullbackMapRight f g hg).base := by
  have h₁ : frameTransport f (g ≫ a) (by rw [Category.assoc, ha, hg]) =
      pullbackMapRight f g hg ≫ frameTransport f a ha := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullbackMapRight_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullbackMapRight_snd_assoc]
  have h₂ : pullback.snd f π' ≫ g = pullbackMapRight f g hg ≫ pullback.snd f π :=
    (pullbackMapRight_snd g hg).symm
  funext x
  have e₁ := congrArg (fun φ ↦ φ.base x) h₁
  have e₂ := congrArg (fun φ ↦ φ.base x) h₂
  simp only [Scheme.Hom.comp_apply] at e₁ e₂
  simp only [frameExt, Function.comp_apply]
  rw [e₁, e₂]

/-- `frameEval_comp`, for any factorization `a'` of `π'` equal to `g ≫ a`. -/
lemma frameEval_comp_eq {W' : Scheme.{u}} {π' : W' ⟶ Y} (g : W' ⟶ W) (hg : g ≫ π = π')
    {a' : W' ⟶ V} (ha' : a' ≫ f = π') (h : g ≫ a = a') (σ : ↥(pullback f π) → S) :
    frameEval f a' ha' (σ ∘ (pullbackMapRight f g hg).base) = frameEval f a ha σ ∘ g.base := by
  subst h
  exact frameEval_comp a ha g hg σ

/-- `frameExt_comp`, for any factorization `a'` of `π'` equal to `g ≫ a`. -/
lemma frameExt_comp_eq {W' : Scheme.{u}} {π' : W' ⟶ Y} (g : W' ⟶ W) (hg : g ≫ π = π')
    {a' : W' ⟶ V} (ha' : a' ≫ f = π') (h : g ≫ a = a') (τ : W → S) :
    frameExt f a' ha' c (τ ∘ g.base) = frameExt f a ha c τ ∘ (pullbackMapRight f g hg).base := by
  subst h
  exact frameExt_comp a ha g hg τ

section Linear

variable {Λ : Type*} [CommRing Λ] {M : Type*} [AddCommGroup M] [Module Λ M]
  (cl : ↥(pullback f f) → M ≃ₗ[Λ] M)

lemma frameExt_add (τ₁ τ₂ : W → M) :
    frameExt f a ha (fun z ↦ cl z) (τ₁ + τ₂) =
      frameExt f a ha (fun z ↦ cl z) τ₁ + frameExt f a ha (fun z ↦ cl z) τ₂ :=
  funext fun _ ↦ map_add (cl _) _ _

lemma frameExt_smul (r : Λ) (τ : W → M) :
    frameExt f a ha (fun z ↦ cl z) (r • τ) = r • frameExt f a ha (fun z ↦ cl z) τ :=
  funext fun _ ↦ map_smul (cl _) _ _

lemma frameExt_zero : frameExt f a ha (fun z ↦ cl z) 0 = 0 :=
  funext fun _ ↦ map_zero (cl _)

end Linear

end AlgebraicGeometry

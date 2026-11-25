/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf

/-!
# Pulling back descent cocycles

Let `f : V ⟶ Y` be a morphism, `c` a descent cocycle on the constant sheaf `S_V` and
`π : T ⟶ Y`. The cover `f_T : V ×_Y T ⟶ T` carries the pulled back cocycle
`c_T = c ∘ (V ×_Y T ×_T V ×_Y T ⟶ V ×_Y V)` (`AlgebraicGeometry.pullbackDescentCocycle`), again a
descent cocycle (`AlgebraicGeometry.IsDescentCocycle.pullbackCover`). The twisted sections of `c`
over `π` are the twisted sections of `c_T` over `𝟙 T`
(`AlgebraicGeometry.IsTwistedSection.pullbackCover`,
`AlgebraicGeometry.IsTwistedSection.ofPullbackCover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Y V T : Scheme.{u}} {f : V ⟶ Y} {S : Type*} {c : ↥(pullback f f) → S → S}

variable (f c) in
/-- The pullback of a descent cocycle along `π : T ⟶ Y`, for the cover `V ×_Y T ⟶ T`. -/
noncomputable def pullbackDescentCocycle (π : T ⟶ Y) :
    ↥(pullback (pullback.snd f π) (pullback.snd f π)) → S → S :=
  fun w ↦ c ((twistedPairMap f π).base w)

lemma pullback_diagonal_comp_twistedPairMap (π : T ⟶ Y) :
    pullback.diagonal (pullback.snd f π) ≫ twistedPairMap f π =
      pullback.fst f π ≫ pullback.diagonal f := by
  apply pullback.hom_ext <;> simp [twistedPairMap]

/-- **Pulled back descent cocycles are descent cocycles.** -/
lemma IsDescentCocycle.pullbackCover (hc : IsDescentCocycle f c) (π : T ⟶ Y) :
    IsDescentCocycle (pullback.snd f π) (pullbackDescentCocycle f c π) := by
  refine ⟨fun s ↦ (hc.isLocallyConstant s).comp_continuous (twistedPairMap f π).base.hom.continuous,
    fun z ↦ hc.bijective _, fun x ↦ ?_, fun w ↦ ?_⟩
  · change c ((pullback.diagonal (pullback.snd f π) ≫ twistedPairMap f π).base x) = id
    rw [pullback_diagonal_comp_twistedPairMap, Scheme.Hom.comp_apply]
    exact hc.diagonal _
  · let T₃ : tripleProduct (pullback.snd f π) ⟶ tripleProduct f :=
      pullback.map _ _ _ _ (twistedPairMap f π) (twistedPairMap f π) (pullback.fst f π)
        (by simp [twistedPairMap]) (by simp [twistedPairMap])
    have e₁ : T₃ ≫ tripleProj₁₃ f = tripleProj₁₃ (pullback.snd f π) ≫ twistedPairMap f π := by
      apply pullback.hom_ext <;> simp [T₃, twistedPairMap]
    have e₂ : T₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ twistedPairMap f π := by simp [T₃]
    have e₃ : T₃ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ twistedPairMap f π := by simp [T₃]
    have := hc.cocycle (T₃.base w)
    simp only [← Scheme.Hom.comp_apply, e₁, e₂, e₃] at this
    exact this

/-- The identification `V ×_Y T ⟶ (V ×_Y T) ×_T T`. -/
noncomputable abbrev pullbackToPullbackId (π : T ⟶ Y) :
    pullback f π ⟶ pullback (pullback.snd f π) (𝟙 T) :=
  pullback.lift (𝟙 _) (pullback.snd f π) (by simp)

/-- **Twisted sections of a pulled back cocycle.** A twisted section of `c` over `π` gives a
twisted section of the pulled back cocycle over `𝟙 T`. -/
lemma IsTwistedSection.pullbackCover {π : T ⟶ Y} {σ : ↥(pullback f π) → S}
    (hσ : IsTwistedSection f c π σ) :
    IsTwistedSection (pullback.snd f π) (pullbackDescentCocycle f c π) (𝟙 T)
      (σ ∘ (pullback.fst (pullback.snd f π) (𝟙 T)).base) := by
  set p := pullback.fst (pullback.snd f π) (𝟙 T)
  let P₂ : pullback (pullback.snd (pullback.snd f π) (𝟙 T))
      (pullback.snd (pullback.snd f π) (𝟙 T)) ⟶
        pullback (pullback.snd f π) (pullback.snd f π) :=
    pullback.map _ _ _ _ p p (𝟙 T) (by simp [p, pullback.condition])
      (by simp [p, pullback.condition])
  have e₁ : P₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p := by simp [P₂]
  have e₂ : P₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := by simp [P₂]
  have e₃ : P₂ ≫ twistedPairMap f π =
      twistedPairMap (pullback.snd f π) (𝟙 T) ≫ twistedPairMap f π := by
    apply pullback.hom_ext <;> simp [P₂, p, twistedPairMap]
  refine ⟨hσ.1.comp_continuous p.base.hom.continuous, fun w ↦ ?_⟩
  have := hσ.2 (P₂.base w)
  have h₁ := congrArg (fun g ↦ g.base w) e₁
  have h₂ := congrArg (fun g ↦ g.base w) e₂
  have h₃ := congrArg (fun g ↦ g.base w) e₃
  simp only [Scheme.Hom.comp_apply] at h₁ h₂ h₃
  rw [h₁, h₂, h₃] at this
  simpa only [Function.comp_apply, pullbackDescentCocycle] using this

/-- **Twisted sections from a pulled back cocycle.** A twisted section of the pulled back
cocycle over `𝟙 T` gives a twisted section of `c` over `π`. -/
lemma IsTwistedSection.ofPullbackCover {π : T ⟶ Y} {τ : ↥(pullback (pullback.snd f π) (𝟙 T)) → S}
    (hτ : IsTwistedSection (pullback.snd f π) (pullbackDescentCocycle f c π) (𝟙 T) τ) :
    IsTwistedSection f c π (τ ∘ (pullbackToPullbackId π).base) := by
  set ψ := pullbackToPullbackId (f := f) π
  have hψ : ψ ≫ pullback.snd (pullback.snd f π) (𝟙 T) = (pullback.snd f π) := by simp [ψ]
  let P₂ : pullback (pullback.snd f π) (pullback.snd f π) ⟶
      pullback (pullback.snd (pullback.snd f π) (𝟙 T)) (pullback.snd (pullback.snd f π) (𝟙 T)) :=
    pullback.map _ _ _ _ ψ ψ (𝟙 T) (by simp [hψ]) (by simp [hψ])
  have e₁ : P₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ψ := by simp [P₂]
  have e₂ : P₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ ψ := by simp [P₂]
  have e₃ : P₂ ≫ twistedPairMap (pullback.snd f π) (𝟙 T) ≫ twistedPairMap f π =
      twistedPairMap f π := by
    apply pullback.hom_ext <;> simp [P₂, ψ, twistedPairMap]
  refine ⟨hτ.1.comp_continuous ψ.base.hom.continuous, fun w ↦ ?_⟩
  have := hτ.2 (P₂.base w)
  have h₁ := congrArg (fun g ↦ g.base w) e₁
  have h₂ := congrArg (fun g ↦ g.base w) e₂
  have h₃ := congrArg (fun g ↦ g.base w) e₃
  simp only [Scheme.Hom.comp_apply] at h₁ h₂ h₃
  simp only [pullbackDescentCocycle, h₁, h₂, h₃] at this
  simpa only [Function.comp_apply] using this

end AlgebraicGeometry

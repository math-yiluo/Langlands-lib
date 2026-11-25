/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStrictlyHenselian

/-!
# Local properties of twisted sections

Let `f : V ⟶ Y` be weakly étale, surjective and quasi-compact and `c` a descent cocycle on the
constant sheaf `S_V` (`AlgebraicGeometry.IsDescentCocycle`). This file collects three local
facts about the twisted sections of `c` (`AlgebraicGeometry.IsTwistedSection`):

* the locus where two twisted sections over `π : T ⟶ Y` agree is the preimage of an open subset
  of `T` (`AlgebraicGeometry.IsTwistedSection.exists_isOpen_eq_iff`), the locus being open and
  saturated for the pro-étale cover `V ×_Y T ⟶ T`;
* if the cover `V ×_Y T ⟶ T` has a section, there are twisted sections with any prescribed value
  at any given point (`AlgebraicGeometry.IsTwistedSection.exists_apply_eq_of_section`), obtained
  by transporting a value along the cocycle; this applies over the spectrum of a strictly
  henselian local ring
  (`AlgebraicGeometry.IsTwistedSection.exists_apply_eq_of_isStrictlyHenselian`);
* the twisted sections of the pulled back cocycle over `ψ : U ⟶ T` are the twisted sections of
  `c` over `ψ ≫ π`, through `(V ×_Y T) ×_T U ≅ V ×_Y U`
  (`AlgebraicGeometry.isTwistedSection_pullbackDescentCocycle_iff`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Y V : Scheme.{u}} {f : V ⟶ Y} {S : Type*} {c : ↥(pullback f f) → S → S}

/-- **Twisted sections agree on the preimage of an open subset.** For a weakly étale, surjective
and quasi-compact `f`, the locus where two twisted sections over `π : T ⟶ Y` agree is the
preimage of an open subset of `T` under `V ×_Y T ⟶ T`: it is open and saturated. -/
lemma IsTwistedSection.exists_isOpen_eq_iff [WeaklyEtale f] [Surjective f] [QuasiCompact f]
    {T : Scheme.{u}} {π : T ⟶ Y} {σ₁ σ₂ : ↥(pullback f π) → S}
    (h₁ : IsTwistedSection f c π σ₁) (h₂ : IsTwistedSection f c π σ₂) :
    ∃ O : Set T, IsOpen O ∧ ∀ x, σ₁ x = σ₂ x ↔ (pullback.snd f π).base x ∈ O := by
  set q := pullback.snd f π
  set A := {x | σ₁ x = σ₂ x}
  have hsat (x x' : ↥(pullback f π)) (h : q.base x = q.base x') (hx : x ∈ A) : x' ∈ A := by
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := q) x' x
      h.symm
    have e₁ := h₁.2 w
    have e₂ := h₂.2 w
    rw [hw₁, hw₂] at e₁ e₂
    simp only [A, Set.mem_ofPred_eq] at hx ⊢
    rw [e₁, e₂, hx]
  have hA : IsOpen A := by
    have hl : IsLocallyConstant fun x ↦ (σ₁ x, σ₂ x) := h₁.1.prodMk h₂.1
    exact hl {p | p.1 = p.2}
  have hcov : Presieve.ofArrows (fun _ : Unit ↦ pullback f π) (fun _ ↦ q) ∈
      Scheme.proetalePrecoverage T := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  have hpre : q.base ⁻¹' (q.base '' A) = A := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro x ⟨x', hx', e⟩
    exact hsat x' x e hx'
  refine ⟨q.base '' A, Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage _ hcov _
    fun _ ↦ by rwa [hpre], fun x ↦ ?_⟩
  rw [← Set.mem_preimage, hpre]
  rfl

/-- **Twisted sections through a given value, for a cover with a section.** If the cover
`V ×_Y T ⟶ T` has a section `s`, then for every point `x` of `V ×_Y T` and every `m : S` there is
a twisted section over `π : T ⟶ Y` taking the value `m` at `x`: transport a suitable value along
`c` from the section, `σ y = c (y, s(y)) m₀`. -/
lemma IsTwistedSection.exists_apply_eq_of_section (hc : IsDescentCocycle f c) {T : Scheme.{u}}
    {π : T ⟶ Y} (s : T ⟶ pullback f π) (hs : s ≫ pullback.snd f π = 𝟙 T)
    (x : ↥(pullback f π)) (m : S) :
    ∃ σ : ↥(pullback f π) → S, IsTwistedSection f c π σ ∧ σ x = m := by
  let δ : pullback f π ⟶ pullback (pullback.snd f π) (pullback.snd f π) :=
    pullback.lift (𝟙 _) (pullback.snd f π ≫ s) (by simp [hs])
  have hδ₁ : δ ≫ pullback.fst (pullback.snd f π) (pullback.snd f π) = 𝟙 _ :=
    pullback.lift_fst _ _ _
  have hδ₂ : δ ≫ pullback.snd (pullback.snd f π) (pullback.snd f π) = pullback.snd f π ≫ s :=
    pullback.lift_snd _ _ _
  obtain ⟨m₀, hm₀⟩ := (hc.bijective ((δ ≫ twistedPairMap f π).base x)).2 m
  refine ⟨fun y ↦ c ((δ ≫ twistedPairMap f π).base y) m₀,
    ⟨(hc.isLocallyConstant m₀).comp_continuous (δ ≫ twistedPairMap f π).base.hom.continuous,
      fun w ↦ ?_⟩, hm₀⟩
  -- the triple `(fst w, snd w, s (q (snd w)))`
  let τ : pullback (pullback.snd f π) (pullback.snd f π) ⟶ tripleProduct f :=
    pullback.lift (twistedPairMap f π)
      (pullback.snd (pullback.snd f π) (pullback.snd f π) ≫ δ ≫ twistedPairMap f π) (by
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
        rw [reassoc_of% hδ₁])
  have e₁ : τ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) = twistedPairMap f π :=
    pullback.lift_fst _ _ _
  have e₂ : τ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) =
      pullback.snd (pullback.snd f π) (pullback.snd f π) ≫ δ ≫ twistedPairMap f π :=
    pullback.lift_snd _ _ _
  have e₃ : τ ≫ tripleProj₁₃ f =
      pullback.fst (pullback.snd f π) (pullback.snd f π) ≫ δ ≫ twistedPairMap f π := by
    apply pullback.hom_ext
    · simp only [τ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [reassoc_of% hδ₁]
    · simp only [τ, δ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact (pullback.condition_assoc (f := pullback.snd f π) (g := pullback.snd f π) _).symm
  have := congrFun (hc.cocycle (τ.base w)) m₀
  simp only [← Scheme.Hom.comp_apply, e₁, e₂, e₃, Function.comp_apply] at this
  simpa only [Scheme.Hom.comp_apply] using this

/-- **Twisted sections over a strictly henselian local scheme.** If `f` is weakly étale and
surjective and `R` is a strictly henselian local ring, then for every `π : Spec R ⟶ Y`, every
point `x` of `V ×_Y Spec R` and every `m : S` there is a twisted section over `π` taking the
value `m` at `x`: the pro-étale cover `V ×_Y Spec R ⟶ Spec R` has a section. -/
lemma IsTwistedSection.exists_apply_eq_of_isStrictlyHenselian [WeaklyEtale f] [Surjective f]
    (hc : IsDescentCocycle f c) {R : Type u} [CommRing R] [IsStrictlyHenselianLocalRing R]
    (π : Spec (.of R) ⟶ Y) (x : ↥(pullback f π)) (m : S) :
    ∃ σ : ↥(pullback f π) → S, IsTwistedSection f c π σ ∧ σ x = m := by
  obtain ⟨s, hs⟩ := exists_section_of_weaklyEtale_of_isStrictlyHenselianLocalRing
    (pullback.snd f π) ((pullback.snd f π).surjective _)
  exact exists_apply_eq_of_section hc s hs x m

section PullbackCover

variable {T U : Scheme.{u}} (π : T ⟶ Y) (ψ : U ⟶ T)

/-- The identification of the schemes of pairs `R_U` of the cover `(V ×_Y T) ×_T U ⟶ U` and of
the cover `V ×_Y U ⟶ U`, induced by `(V ×_Y T) ×_T U ≅ V ×_Y U`. -/
noncomputable abbrev pairPullbackLeftPullbackSnd :
    pullback (pullback.snd (pullback.snd f π) ψ) (pullback.snd (pullback.snd f π) ψ) ⟶
      pullback (pullback.snd f (ψ ≫ π)) (pullback.snd f (ψ ≫ π)) :=
  pullback.map _ _ _ _ (pullbackLeftPullbackSndIso f π ψ).hom
    (pullbackLeftPullbackSndIso f π ψ).hom (𝟙 U) (by simp) (by simp)

/-- The inverse of `AlgebraicGeometry.pairPullbackLeftPullbackSnd`. -/
noncomputable abbrev pairPullbackLeftPullbackSndInv :
    pullback (pullback.snd f (ψ ≫ π)) (pullback.snd f (ψ ≫ π)) ⟶
      pullback (pullback.snd (pullback.snd f π) ψ) (pullback.snd (pullback.snd f π) ψ) :=
  pullback.map _ _ _ _ (pullbackLeftPullbackSndIso f π ψ).inv
    (pullbackLeftPullbackSndIso f π ψ).inv (𝟙 U) (by simp) (by simp)

/-- `AlgebraicGeometry.pairPullbackLeftPullbackSndInv` is a right inverse. -/
lemma pairPullbackLeftPullbackSndInv_comp :
    pairPullbackLeftPullbackSndInv (f := f) π ψ ≫ pairPullbackLeftPullbackSnd π ψ = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- `AlgebraicGeometry.pairPullbackLeftPullbackSnd` is compatible with the maps to `V ×_Y V`. -/
lemma pairPullbackLeftPullbackSnd_twistedPairMap :
    pairPullbackLeftPullbackSnd (f := f) π ψ ≫ twistedPairMap f (ψ ≫ π) =
      twistedPairMap (pullback.snd f π) ψ ≫ twistedPairMap f π := by
  apply pullback.hom_ext <;> simp

/-- **Twisted sections of a pulled back cocycle.** Through `(V ×_Y T) ×_T U ≅ V ×_Y U`, the
twisted sections over `ψ : U ⟶ T` of the cocycle `c` pulled back to the cover `V ×_Y T ⟶ T` are
the twisted sections of `c` over `ψ ≫ π`. -/
lemma isTwistedSection_pullbackDescentCocycle_iff (σ : ↥(pullback f (ψ ≫ π)) → S) :
    IsTwistedSection (pullback.snd f π) (pullbackDescentCocycle f c π) ψ
        (σ ∘ (pullbackLeftPullbackSndIso f π ψ).hom.base) ↔
      IsTwistedSection f c (ψ ≫ π) σ := by
  set κ := pullbackLeftPullbackSndIso f π ψ
  set K := pairPullbackLeftPullbackSnd (f := f) π ψ
  have hK₁ : K ≫ pullback.fst (pullback.snd f (ψ ≫ π)) (pullback.snd f (ψ ≫ π)) =
      pullback.fst (pullback.snd (pullback.snd f π) ψ) (pullback.snd (pullback.snd f π) ψ) ≫
        κ.hom := pullback.lift_fst _ _ _
  have hK₂ : K ≫ pullback.snd (pullback.snd f (ψ ≫ π)) (pullback.snd f (ψ ≫ π)) =
      pullback.snd (pullback.snd (pullback.snd f π) ψ) (pullback.snd (pullback.snd f π) ψ) ≫
        κ.hom := pullback.lift_snd _ _ _
  have hlc : IsLocallyConstant (σ ∘ κ.hom.base) ↔ IsLocallyConstant σ := by
    refine ⟨fun h ↦ ?_, fun h ↦ h.comp_continuous κ.hom.base.hom.continuous⟩
    have := h.comp_continuous κ.inv.base.hom.continuous
    simpa [Function.comp_def, ← Scheme.Hom.comp_apply] using this
  have key (w : ↥(pullback (pullback.snd (pullback.snd f π) ψ)
      (pullback.snd (pullback.snd f π) ψ))) :
      (σ ∘ κ.hom.base) ((pullback.fst (pullback.snd (pullback.snd f π) ψ)
          (pullback.snd (pullback.snd f π) ψ)).base w) =
        pullbackDescentCocycle f c π ((twistedPairMap (pullback.snd f π) ψ).base w)
          ((σ ∘ κ.hom.base) ((pullback.snd (pullback.snd (pullback.snd f π) ψ)
            (pullback.snd (pullback.snd f π) ψ)).base w)) ↔
      σ ((pullback.fst (pullback.snd f (ψ ≫ π)) (pullback.snd f (ψ ≫ π))).base (K.base w)) =
        c ((twistedPairMap f (ψ ≫ π)).base (K.base w))
          (σ ((pullback.snd (pullback.snd f (ψ ≫ π)) (pullback.snd f (ψ ≫ π))).base
            (K.base w))) := by
    have h₁ := congrArg (fun g ↦ g.base w) hK₁
    have h₂ := congrArg (fun g ↦ g.base w) hK₂
    have h₃ := congrArg (fun g ↦ g.base w) (pairPullbackLeftPullbackSnd_twistedPairMap (f := f) π ψ)
    simp only [Scheme.Hom.comp_apply] at h₁ h₂ h₃
    simp only [Function.comp_apply, pullbackDescentCocycle, K, h₁, h₂, h₃]
  refine ⟨fun h ↦ ⟨hlc.1 h.1, fun w ↦ ?_⟩, fun h ↦ ⟨hlc.2 h.1, fun w ↦ (key w).2 (h.2 _)⟩⟩
  have hw : K.base ((pairPullbackLeftPullbackSndInv π ψ).base w) = w := by
    rw [← Scheme.Hom.comp_apply, pairPullbackLeftPullbackSndInv_comp]
    simp
  have := (key ((pairPullbackLeftPullbackSndInv π ψ).base w)).1 (h.2 _)
  rwa [hw] at this

end PullbackCover

end AlgebraicGeometry

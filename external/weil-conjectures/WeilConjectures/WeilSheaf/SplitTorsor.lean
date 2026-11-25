/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier

/-!
# Pushforwards of the constant sheaf along split torsors

Let `π : W ⟶ Z` be a weakly étale morphism and `τ_g`, `g ∈ G`, automorphisms of `W` over `Z`
splitting `π`: the map `∐_{g ∈ G} W ⟶ W ×_Z W`, `(𝟙, τ_g)` on the summand indexed by `g`, is an
isomorphism. This is the situation of a torsor under the finite group `G`, after base change to
itself. For `v : V ⟶ W` the sections `x ↦ (x, τ_g (v x))` then decompose `V ×_Z W` into copies
of `V` (`CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_lift_comp`).

The group acts on `π_* ℚ̄_ℓ` by pulling back sections along the `τ_g`
(`AlgebraicGeometry.ProEtale.torsorTranslation`), and the evaluations
`π^* π_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along the sections `x ↦ (x, τ_g x)`
(`AlgebraicGeometry.ProEtale.torsorEval`, the pullback of the translation followed by the
counit) are jointly injective (`AlgebraicGeometry.ProEtale.torsorEval_hom_ext`): the sections of
`π^* π_* ℚ̄_ℓ` over `v : V ⟶ W` are the locally finite functions on `V ×_Z W`, which is covered by
the sections. This generalises the computation for the Artin–Schreier covering in
`WeilConjectures.WeilSheaf.Fourier`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open scoped ProEtale

variable {l : ℕ} [Fact l.Prime] {Z W : Scheme.{u}} (π : W ⟶ Z) {G : Type u}
  (τ : G → (W ≅ W)) (hτ : ∀ g, (τ g).hom ≫ π = π)

/-- The automorphisms `τ_g` of `W` over `Z` *split* `π` if the map `∐_{g ∈ G} W ⟶ W ×_Z W`,
`(𝟙, τ_g)` on the summand indexed by `g`, is an isomorphism. -/
def IsTorsorSplit [Finite G] : Prop :=
  IsIso (Sigma.desc fun g : G ↦ pullback.lift (f := π) (g := π) (𝟙 W) (τ g).hom
    (by simp [hτ]) : ∐ (fun _ : G ↦ W) ⟶ pullback π π)

section BaseChange

variable {π τ hτ} [Finite G] {Z' W' : Scheme.{u}}

/-- **Splittings are stable under base change.** If the automorphisms `τ_g` split `π`, then
their base changes `τ'_g` along `q : Z' ⟶ Z` split the base change `π' : W' ⟶ Z'` of `π`. -/
lemma IsTorsorSplit.of_isPullback (hsplit : IsTorsorSplit π τ hτ) {π' : W' ⟶ Z'} {p : W' ⟶ W}
    {q : Z' ⟶ Z} (sq : IsPullback p π' π q) (τ' : G → (W' ≅ W'))
    (hτ' : ∀ g, (τ' g).hom ≫ π' = π') (hp : ∀ g, (τ' g).hom ≫ p = p ≫ (τ g).hom) :
    IsTorsorSplit π' τ' hτ' := by
  have : IsIso (Sigma.desc fun g : G ↦ pullback.lift (f := π) (g := π) (𝟙 W) (τ g).hom
    (by simp [hτ]) : ∐ (fun _ : G ↦ W) ⟶ pullback π π) := hsplit
  have h₁ := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp π (fun g ↦ (τ g).hom) hτ p
  have hP : IsPullback (pullback.fst π' π') (pullback.snd π' π' ≫ p) (p ≫ π) π := by
    have := (IsPullback.of_hasPullback π' π').flip.paste_horiz sq
    rw [← sq.w] at this
    exact this.flip
  suffices IsIso (Sigma.desc (fun g : G ↦ pullback.lift (f := π') (g := π') (𝟙 _) (τ' g).hom
      (by simp [hτ'])) ≫ hP.isoPullback.hom) from IsIso.of_isIso_comp_right _ hP.isoPullback.hom
  convert h₁ using 1
  refine Sigma.hom_ext _ _ fun g ↦ ?_
  simp only [colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app]
  apply pullback.hom_ext
  · simp
  · simp [hp]

end BaseChange

section Sections

variable {V : Scheme.{u}} (v : V ⟶ W)

/-- The section `x ↦ (x, τ_g (v x))` of the first projection `V ×_Z W ⟶ V`, the fibre product
taken along `v ≫ π` and `π`. -/
noncomputable def torsorSection (g : G) : V ⟶ pullback (v ≫ π) π :=
  pullback.lift (𝟙 V) (v ≫ (τ g).hom) (by simp [hτ])

@[reassoc (attr := simp)]
lemma torsorSection_fst (g : G) : torsorSection π τ hτ v g ≫ pullback.fst _ _ = 𝟙 V :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma torsorSection_snd (g : G) :
    torsorSection π τ hτ v g ≫ pullback.snd _ _ = v ≫ (τ g).hom :=
  pullback.lift_snd _ _ _

@[simp]
lemma torsorSection_fst_apply (g : G) (x : V) :
    pullback.fst (v ≫ π) π (torsorSection π τ hτ v g x) = x := by
  rw [← Scheme.Hom.comp_apply, torsorSection_fst]
  rfl

variable [Finite G]

/-- The sections `x ↦ (x, τ_g (v x))` decompose `V ×_Z W` into a disjoint union of copies of
`V`. -/
lemma isIso_sigmaDesc_torsorSection (hsplit : IsTorsorSplit π τ hτ) :
    IsIso (Sigma.desc (torsorSection π τ hτ v) : ∐ (fun _ : G ↦ V) ⟶ _) :=
  have : IsIso (Sigma.desc fun g : G ↦ pullback.lift (f := π) (g := π) (𝟙 W) (τ g).hom
      (by simp [hτ]) : ∐ (fun _ : G ↦ W) ⟶ pullback π π) := hsplit
  FinitaryPreExtensive.isIso_sigmaDesc_lift_comp π (fun g ↦ (τ g).hom) hτ v

/-- The homeomorphism `Σ_{g ∈ G} V ≃ V ×_Z W`, `(g, x) ↦ (x, τ_g (v x))`. -/
noncomputable def torsorHomeomorph (hsplit : IsTorsorSplit π τ hτ) :
    (Σ _ : G, V) ≃ₜ (pullback (v ≫ π) π : Scheme.{u}) :=
  haveI := isIso_sigmaDesc_torsorSection π τ hτ v hsplit
  (sigmaMk fun _ : G ↦ V).trans (Sigma.desc (torsorSection π τ hτ v)).homeomorph

lemma torsorHomeomorph_apply (hsplit : IsTorsorSplit π τ hτ) (g : G) (x : V) :
    torsorHomeomorph π τ hτ v hsplit ⟨g, x⟩ = torsorSection π τ hτ v g x := by
  simp only [torsorHomeomorph, Homeomorph.trans_apply, sigmaMk_mk,
    Scheme.Hom.homeomorph_apply, ← Scheme.Hom.comp_apply, colimit.ι_desc, Cofan.mk_ι_app]

/-- The index `g` of the summand `x ↦ (x, τ_g (v x))` of `V ×_Z W` containing a point. -/
noncomputable def torsorIndex (hsplit : IsTorsorSplit π τ hτ)
    (z : (pullback (v ≫ π) π : Scheme.{u})) : G :=
  ((torsorHomeomorph π τ hτ v hsplit).symm z).1

@[simp]
lemma torsorIndex_torsorSection (hsplit : IsTorsorSplit π τ hτ) (g : G) (x : V) :
    torsorIndex π τ hτ v hsplit (torsorSection π τ hτ v g x) = g := by
  rw [torsorIndex, ← torsorHomeomorph_apply π τ hτ v hsplit, Homeomorph.symm_apply_apply]

/-- Every point of `V ×_Z W` is `(x, τ_g (v x))` for `g` its index and `x` its first
projection. -/
lemma torsorSection_torsorIndex (hsplit : IsTorsorSplit π τ hτ)
    (z : (pullback (v ≫ π) π : Scheme.{u})) :
    torsorSection π τ hτ v (torsorIndex π τ hτ v hsplit z) (pullback.fst (v ≫ π) π z) = z := by
  obtain ⟨⟨g, x⟩, rfl⟩ := (torsorHomeomorph π τ hτ v hsplit).surjective z
  rw [torsorHomeomorph_apply, torsorIndex_torsorSection, torsorSection_fst_apply]

end Sections

section Sheaves

variable (l) in
/-- The action of `τ_g` on `π_* ℚ̄_ℓ`, pulling back sections along `τ_g` and using
`τ_g ≫ π = π`:
```
π_* ℚ̄_ℓ ⟶ π_* (τ_g)_* ℚ̄_ℓ ≅ (τ_g ≫ π)_* ℚ̄_ℓ = π_* ℚ̄_ℓ
```
-/
noncomputable def torsorTranslation (g : G) :
    (π)_*ᵃ[l].obj (AdicSheaf.unit l W) ⟶ (π)_*ᵃ[l].obj (AdicSheaf.unit l W) :=
  (π)_*ᵃ[l].map (adicLowerStarUnitIso l (τ g)).inv ≫
    (adicLowerStarComp l (τ g).hom π).hom.app (AdicSheaf.unit l W) ≫
    (adicLowerStarCongr l (hτ g)).hom.app (AdicSheaf.unit l W)

lemma torsorTranslation_hom (g : G) :
    (torsorTranslation l π τ hτ g).hom =
      (π)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l (τ g)).inv ≫
        (lowerStarComp (WeilCoefficients.{u} l) (τ g).hom π).hom.app (adicConstantSheaf l W) ≫
        (lowerStarCongr (WeilCoefficients.{u} l) (hτ g)).hom.app (adicConstantSheaf l W) :=
  rfl

/-- On sections over `U ⟶ Z`, the action of `τ_g` on `π_* ℚ̄_ℓ` pulls functions on `U ×_Z W`
back along `(u, w) ↦ (u, τ_g w)`. -/
lemma torsorTranslation_hom_app (g : G) (U : Z.ProEt) :
    (torsorTranslation l π τ hτ g).hom.hom.app (op U) =
      (adicFunctionsPresheaf l).map (pullback.map U.hom π U.hom π (𝟙 _) (τ g).hom (𝟙 _)
        (by simp) (by simp [hτ])).op := by
  rw [torsorTranslation_hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, lowerStar_map_hom_app', unop_op,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    adicConstantSheafLowerStarIso_inv_hom_app, adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]

variable (l) in
/-- The evaluation `π^* π_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along the section `x ↦ (x, τ_g x)`: the pullback of the
action of `τ_g` followed by the counit of `π^* ⊣ π_*`. -/
noncomputable def torsorEval (g : G) :
    (π)^*ᵃ[l].obj ((π)_*ᵃ[l].obj (AdicSheaf.unit l W)) ⟶ AdicSheaf.unit l W :=
  (π)^*ᵃ[l].map (torsorTranslation l π τ hτ g) ≫
    (adicUpperStarLowerStarAdjunction l π).counit.app _

variable [WeaklyEtale π]

/-- The counit of `π^* ⊣ π_*`, computed by restriction, evaluates a function on `V ×_Z W` along
the diagonal section `x ↦ (x, v x)`. -/
lemma localizationRestrictionLowerStarAdjunction_counit_app_hom_app (V : W.ProEt) :
    ((localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) π
        inferInstance).counit.app (adicConstantSheaf l W)).hom.app (op V) =
      (adicFunctionsPresheaf l).map
        (pullback.lift (𝟙 V.left) V.hom (by simp) : V.left ⟶ pullback (V.hom ≫ π) π).op :=
  rfl

/-- On sections over `v : V ⟶ W`, the evaluation along `x ↦ (x, τ_g (v x))` pulls functions on
`V ×_Z W` back along this section. -/
lemma torsorEval_hom_app (g : G) (V : W.ProEt) :
    ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) π
        inferInstance).inv.app _ ≫ (torsorEval l π τ hτ g).hom).hom.app (op V) =
      (adicFunctionsPresheaf l).map (torsorSection π τ hτ V.hom g).op := by
  have h₁ : (torsorEval l π τ hτ g).hom =
      (π)^*[WeilCoefficients.{u} l].map (torsorTranslation l π τ hτ g).hom ≫
        (upperStarLowerStarAdjunction (WeilCoefficients.{u} l) π).counit.app
          (adicConstantSheaf l _) := by
    rw [torsorEval, Mod.comp_hom', adicUpperStar_map_hom]
    erw [Adjunction.modAdjunction_counit_app_hom]
    rfl
  have h₂ := (upperStarLowerStarAdjunction (WeilCoefficients.{u} l)
    π).leftAdjointUniq_hom_app_counit
      (localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) π
        inferInstance) (adicConstantSheaf l _)
  rw [h₁, ← Category.assoc, ← (upperStarIsoLocalizationRestriction
    (WeilCoefficients.{u} l) π inferInstance).inv.naturality, Category.assoc]
  erw [← h₂, Iso.inv_hom_id_app_assoc]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    localizationRestriction_map_hom_app]
  erw [torsorTranslation_hom_app, localizationRestrictionLowerStarAdjunction_counit_app_hom_app]
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · rw [Category.assoc]
    erw [pullback.lift_fst, Category.comp_id, pullback.lift_fst, torsorSection_fst]
  · rw [Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd_assoc, torsorSection_snd]

variable [Finite G]

/-- **The evaluations are jointly injective.** Morphisms into `π^* π_* ℚ̄_ℓ` are determined by
their composites with the evaluations along the sections `x ↦ (x, τ_g x)`, which cover
`V ×_Z W`. -/
lemma torsorEval_hom_ext (hsplit : IsTorsorSplit π τ hτ)
    {T : Sheaf (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)}
    {f g : T ⟶ ((π)^*ᵃ[l].obj ((π)_*ᵃ[l].obj (AdicSheaf.unit l W))).X}
    (h : ∀ c, f ≫ (torsorEval l π τ hτ c).hom = g ≫ (torsorEval l π τ hτ c).hom) : f = g := by
  let ε := upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) π inferInstance
  suffices hε : f ≫ ε.hom.app _ = g ≫ ε.hom.app _ by
    have := congrArg (· ≫ ε.inv.app _) hε
    simp only [Category.assoc, Iso.hom_inv_id_app] at this
    erw [Category.comp_id, Category.comp_id] at this
    exact this
  ext ⟨V⟩ : 3
  ext x
  have key (c : G) (φ : T ⟶ (localizationRestriction (WeilCoefficients.{u} l) π
      inferInstance).obj ((π)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l W))) :
      (φ ≫ ε.inv.app _ ≫ (torsorEval l π τ hτ c).hom).hom.app (op V) x =
        (adicFunctionsPresheaf l).map (torsorSection π τ hτ V.hom c).op
          (φ.hom.app (op V) x) := by
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply]
    erw [torsorEval_hom_app]
    rfl
  have hc (c : G) := (key c _).symm.trans ((congrArg (fun φ ↦ φ.hom.app (op V) x)
    (show (f ≫ ε.hom.app _) ≫ (ε.inv.app _ ≫ (torsorEval l π τ hτ c).hom) =
      (g ≫ ε.hom.app _) ≫ (ε.inv.app _ ≫ (torsorEval l π τ hτ c).hom) by
        simpa using h c)).trans (key c _))
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun z ↦ ?_))
  have := congrArg (fun y ↦ y.down.1 (pullback.fst (V.hom ≫ π) π z))
    (hc (torsorIndex π τ hτ V.hom hsplit z))
  simp only [adicFunctionsPresheaf_map, ModuleCat.hom_ofHom] at this
  rw [← torsorSection_torsorIndex π τ hτ V.hom hsplit z]
  exact this

variable [AddCommGroup G]

omit [Finite G] [WeaklyEtale π] in
/-- The actions of the `τ_g` on `π_* ℚ̄_ℓ` compose: if `τ_{g + h} = τ_g ≫ τ_h` then
`σ_g ≫ σ_h = σ_{g + h}`. -/
lemma torsorTranslation_comp (hadd : ∀ g h, (τ (g + h)).hom = (τ g).hom ≫ (τ h).hom)
    (g h : G) :
    torsorTranslation l π τ hτ g ≫ torsorTranslation l π τ hτ h =
      torsorTranslation l π τ hτ (g + h) := by
  refine Mod.hom_ext _ _ ?_
  ext ⟨U⟩ : 3
  rw [Mod.comp_hom', ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    torsorTranslation_hom_app, torsorTranslation_hom_app, torsorTranslation_hom_app,
    ← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · simp
  · simp [add_comm g h, hadd]

omit [Finite G] [WeaklyEtale π] in
/-- The evaluations compose with the action: `π^* σ_g ≫ ev_h = ev_{g + h}`. -/
lemma upperStar_map_torsorTranslation_comp_torsorEval
    (hadd : ∀ g h, (τ (g + h)).hom = (τ g).hom ≫ (τ h).hom) (g h : G) :
    (π)^*ᵃ[l].map (torsorTranslation l π τ hτ g) ≫ torsorEval l π τ hτ h =
      torsorEval l π τ hτ (g + h) := by
  rw [torsorEval, ← Functor.map_comp_assoc, torsorTranslation_comp π τ hτ hadd, torsorEval]

end Sheaves

end AlgebraicGeometry.ProEtale

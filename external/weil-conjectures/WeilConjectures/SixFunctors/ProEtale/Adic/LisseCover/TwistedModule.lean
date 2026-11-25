/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedGerm
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedLimit

/-!
# The étale sheaf of modules of a linear descent cocycle

Let `f : V ⟶ Y` be weakly étale, `M` a `Λ`-module and `c` a descent cocycle on the constant sheaf
`M_V` acting by `Λ`-linear automorphisms. The twisted sections of `c`
(`AlgebraicGeometry.IsTwistedSection`) over an étale `Y`-scheme form a `Λ`-submodule of the
functions to `M` (`AlgebraicGeometry.twistedSubmodule`), and these submodules form a sheaf of
`Λ`-modules on the small étale site of `Y` (`AlgebraicGeometry.twistedModuleSheaf`), whose
underlying sheaf of sets is `AlgebraicGeometry.twistedSectionsPresheaf`.

For `π : T ⟶ Y` the twisted sections over the étale `T`-schemes form a sheaf
`AlgebraicGeometry.twistedModuleSheafOver` on the small étale site of `T`, isomorphic to the sheaf
of twisted sections of the pulled back cocycle (`AlgebraicGeometry.twistedModuleSheafOverIso`).
For `f` weakly étale, surjective, quasi-compact and quasi-separated, pulling back commutes with
taking twisted sections (`AlgebraicGeometry.isIso_homEquiv_symm_twistedModuleSheafOverRestrict`,
`AlgebraicGeometry.upperStarTwistedModuleSheafIso`): this is checked on stalks at geometric points,
using that the locus where two twisted sections agree descends to an open subset of the base, and
that over a strict localization the cover has a section, so that twisted sections there exist with
any value and descend to an étale neighbourhood
(`AlgebraicGeometry.IsTwistedSection.exists_of_isLimit`).
Consequently restriction of twisted sections is bijective whenever the pullback map on global
sections is (`AlgebraicGeometry.bijective_twistedRestrict_of_isIso_globalSectionsUpperStarMap`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {Y V : Scheme.{u}} (f : V ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] {M : Type (u + 1)}
  [AddCommGroup M] [Module Λ M] (c : ↥(pullback f f) → M ≃ₗ[Λ] M)

/-- The twisted sections of a linear cocycle over `π : T ⟶ Y` form a `Λ`-submodule of the
functions `V ×_Y T → M`. -/
def twistedSubmodule {T : Scheme.{u}} (π : T ⟶ Y) : Submodule Λ (↥(pullback f π) → M) where
  carrier := {σ | IsTwistedSection f (fun z ↦ c z) π σ}
  add_mem' {σ τ} hσ hτ := ⟨hσ.1.add hτ.1, fun w ↦ by
    simp only [Pi.add_apply, hσ.2 w, hτ.2 w, map_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun w ↦ by simp⟩
  smul_mem' a σ hσ := ⟨hσ.1.comp (a • ·), fun w ↦ by
    simp only [Pi.smul_apply, hσ.2 w, map_smul]⟩

lemma mem_twistedSubmodule {T : Scheme.{u}} {π : T ⟶ Y} {σ : ↥(pullback f π) → M} :
    σ ∈ twistedSubmodule f c π ↔ IsTwistedSection f (fun z ↦ c z) π σ :=
  Iff.rfl

/-- The presheaf of `Λ`-modules of twisted sections of a linear cocycle on the small étale site
of `Y`. -/
noncomputable def twistedModulePresheaf : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj U := ModuleCat.of Λ (twistedSubmodule f c U.unop.hom)
  map {U U'} g := ModuleCat.ofHom
    { toFun σ := ⟨σ.1 ∘ (pullbackMapRight f g.unop.left (MorphismProperty.Over.w g.unop)).base,
        ((mem_twistedSubmodule f c).1 σ.2).comp g.unop.left (MorphismProperty.Over.w g.unop)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id U := by
    ext σ : 2
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (𝟙 U.unop.left) _).base = σ.1
    rw [pullbackMapRight_id]
    rfl
  map_comp {U U' U''} g g' := by
    ext σ : 2
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (g'.unop.left ≫ g.unop.left) _).base =
      (σ.1 ∘ (pullbackMapRight f g.unop.left _).base) ∘ (pullbackMapRight f g'.unop.left _).base
    rw [pullbackMapRight_comp g.unop.left (MorphismProperty.Over.w g.unop) g'.unop.left
      (MorphismProperty.Over.w g'.unop)]
    rfl

/-- The underlying presheaf of sets of `AlgebraicGeometry.twistedModulePresheaf` is the presheaf
of twisted sections `AlgebraicGeometry.twistedSectionsPresheaf`. -/
noncomputable def twistedModulePresheafCompForgetIso :
    twistedModulePresheaf f c ⋙ forget (ModuleCat.{u + 1} Λ) ≅
      twistedSectionsPresheaf f (fun z ↦ c z) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- **The sheaf of `Λ`-modules of twisted sections of a linear cocycle.** -/
noncomputable def twistedModuleSheaf : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj := twistedModulePresheaf f c
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{u + 1} Λ)),
      Presheaf.isSheaf_of_iso_iff (twistedModulePresheafCompForgetIso f c)]
    exact isSheaf_twistedSectionsPresheaf f _

section PullbackComparison

variable {f}

/-- The pullback of a linear cocycle along `π : T ⟶ Y`, a cocycle for the cover
`V ×_Y T ⟶ T`. -/
noncomputable def pullbackCocycle {T : Scheme.{u}} (π : T ⟶ Y) :
    ↥(pullback (pullback.snd f π) (pullback.snd f π)) → M ≃ₗ[Λ] M :=
  fun w ↦ c ((twistedPairMap f π).base w)

/-- A morphism of étale `T`-schemes commutes with the structure maps to `Y`. -/
lemma Etale.left_comp_hom_comp {T : Scheme.{u}} {U U' : T.Etale} (g : U' ⟶ U) (π : T ⟶ Y) :
    g.left ≫ U.hom ≫ π = U'.hom ≫ π := by
  rw [← Category.assoc, MorphismProperty.Over.w g]

/-- Composition of the maps `V ×_Y T'' ⟶ V ×_Y T' ⟶ V ×_Y T` along morphisms with a given
composite. -/
lemma pullbackMapRight_comp_eq {T T' T'' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    {π'' : T'' ⟶ Y} {t : T' ⟶ T} (ht : t ≫ π = π') {t' : T'' ⟶ T'} (ht' : t' ≫ π' = π'')
    {t'' : T'' ⟶ T} (ht'' : t'' ≫ π = π'') (e : t' ≫ t = t'') :
    pullbackMapRight f t' ht' ≫ pullbackMapRight f t ht = pullbackMapRight f t'' ht'' := by
  subst e
  exact pullback.hom_ext (by simp) (by simp)

/-- The restriction of twisted sections of a linear cocycle along a morphism `t : T' ⟶ T` over
`Y`, as a linear map. -/
noncomputable def twistedSubmoduleRestrict {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (t : T' ⟶ T) (ht : t ≫ π = π') : twistedSubmodule f c π →ₗ[Λ] twistedSubmodule f c π' where
  toFun σ := ⟨σ.1 ∘ (pullbackMapRight f t ht).base, ((mem_twistedSubmodule f c).1 σ.2).comp t ht⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The underlying function of a restriction of twisted sections. -/
lemma twistedSubmoduleRestrict_apply_coe {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    (t : T' ⟶ T) (ht : t ≫ π = π') (σ : twistedSubmodule f c π) :
    (twistedSubmoduleRestrict c t ht σ).1 = σ.1 ∘ (pullbackMapRight f t ht).base :=
  rfl

/-- Restrictions of twisted sections along equal morphisms agree. -/
lemma twistedSubmoduleRestrict_congr {T T' : Scheme.{u}} {π : T ⟶ Y} {π' : T' ⟶ Y}
    {a a' : T' ⟶ T} (ha : a ≫ π = π') (ha' : a' ≫ π = π') (e : a = a')
    (σ : twistedSubmodule f c π) :
    twistedSubmoduleRestrict c a ha σ = twistedSubmoduleRestrict c a' ha' σ := by
  subst e
  rfl

/-- Restricting twisted sections twice is restricting along the composite. -/
lemma twistedSubmoduleRestrict_comp_eq_comp {T₁ T₂ T₂' T₃ : Scheme.{u}} {π₁ : T₁ ⟶ Y}
    {π₂ : T₂ ⟶ Y} {π₂' : T₂' ⟶ Y} {π₃ : T₃ ⟶ Y} {a : T₂ ⟶ T₁} (ha : a ≫ π₁ = π₂)
    {b : T₃ ⟶ T₂} (hb : b ≫ π₂ = π₃) {a' : T₂' ⟶ T₁} (ha' : a' ≫ π₁ = π₂') {b' : T₃ ⟶ T₂'}
    (hb' : b' ≫ π₂' = π₃) (e : b ≫ a = b' ≫ a') (σ : twistedSubmodule f c π₁) :
    twistedSubmoduleRestrict c b hb (twistedSubmoduleRestrict c a ha σ) =
      twistedSubmoduleRestrict c b' hb' (twistedSubmoduleRestrict c a' ha' σ) := by
  have h : (b ≫ a) ≫ π₁ = π₃ := by rw [Category.assoc, ha, hb]
  refine Subtype.ext (funext fun x ↦ ?_)
  simp only [twistedSubmoduleRestrict_apply_coe, Function.comp_apply]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullbackMapRight_comp_eq ha hb h rfl,
    pullbackMapRight_comp_eq ha' hb' h e.symm]

/-- Restricting twisted sections twice is restricting along the composite. -/
lemma twistedSubmoduleRestrict_comp_eq {T₁ T₂ T₃ : Scheme.{u}} {π₁ : T₁ ⟶ Y} {π₂ : T₂ ⟶ Y}
    {π₃ : T₃ ⟶ Y} {a : T₂ ⟶ T₁} (ha : a ≫ π₁ = π₂) {b : T₃ ⟶ T₂} (hb : b ≫ π₂ = π₃)
    {d : T₃ ⟶ T₁} (hd : d ≫ π₁ = π₃) (e : b ≫ a = d) (σ : twistedSubmodule f c π₁) :
    twistedSubmoduleRestrict c b hb (twistedSubmoduleRestrict c a ha σ) =
      twistedSubmoduleRestrict c d hd σ := by
  refine Subtype.ext (funext fun x ↦ ?_)
  simp only [twistedSubmoduleRestrict_apply_coe, Function.comp_apply]
  rw [← Scheme.Hom.comp_apply, pullbackMapRight_comp_eq ha hb hd e]

/-- The presheaf of `Λ`-modules of twisted sections of a linear cocycle over the étale
`T`-schemes, for a morphism `π : T ⟶ Y`: its sections over `U ⟶ T` are the twisted sections of
`c` over `U ⟶ T ⟶ Y`. -/
noncomputable def twistedModulePresheafOver {T : Scheme.{u}} (π : T ⟶ Y) :
    T.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj U := ModuleCat.of Λ (twistedSubmodule f c (U.unop.hom ≫ π))
  map {U U'} g := ModuleCat.ofHom
    (twistedSubmoduleRestrict c g.unop.left (Etale.left_comp_hom_comp g.unop π))
  map_id U := by
    ext σ : 2
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (𝟙 U.unop.left) _).base = σ.1
    rw [pullbackMapRight_id]
    rfl
  map_comp {U U' U''} g g' := by
    ext σ : 2
    exact (twistedSubmoduleRestrict_comp_eq c (Etale.left_comp_hom_comp g.unop π)
      (Etale.left_comp_hom_comp g'.unop π) (Etale.left_comp_hom_comp (g ≫ g').unop π) rfl σ).symm

/-- The restriction maps of `AlgebraicGeometry.twistedModulePresheafOver`. -/
lemma twistedModulePresheafOver_map_apply {T : Scheme.{u}} (π : T ⟶ Y) {U U' : T.Etale}
    (g : U' ⟶ U) (σ : twistedSubmodule f c (U.hom ≫ π)) :
    (twistedModulePresheafOver c π).map g.op σ =
      twistedSubmoduleRestrict c g.left (Etale.left_comp_hom_comp g π) σ :=
  rfl

/-- `(V ×_Y T) ×_T U ≅ V ×_Y U` on points: the inverse after the map is the identity. -/
lemma pullbackLeftPullbackSndIso_hom_comp_inv_apply {T U : Scheme.{u}} (π : T ⟶ Y)
    (ψ : U ⟶ T) (x) :
    (pullbackLeftPullbackSndIso f π ψ).inv.base ((pullbackLeftPullbackSndIso f π ψ).hom.base x) =
      x := by
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  simp

/-- `(V ×_Y T) ×_T U ≅ V ×_Y U` on points: the map after the inverse is the identity. -/
lemma pullbackLeftPullbackSndIso_inv_comp_hom_apply {T U : Scheme.{u}} (π : T ⟶ Y)
    (ψ : U ⟶ T) (x) :
    (pullbackLeftPullbackSndIso f π ψ).hom.base ((pullbackLeftPullbackSndIso f π ψ).inv.base x) =
      x := by
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  simp

/-- Through `(V ×_Y T) ×_T U ≅ V ×_Y U`, the twisted sections over `ψ : U ⟶ T` of the pullback
of a linear cocycle are the twisted sections of the cocycle over `ψ ≫ π`. -/
noncomputable def twistedSubmodulePullbackEquiv {T U : Scheme.{u}} (π : T ⟶ Y) (ψ : U ⟶ T) :
    twistedSubmodule (pullback.snd f π) (pullbackCocycle c π) ψ ≃ₗ[Λ]
      twistedSubmodule f c (ψ ≫ π) where
  toFun τ := ⟨τ.1 ∘ (pullbackLeftPullbackSndIso f π ψ).inv.base, by
    rw [mem_twistedSubmodule, ← isTwistedSection_pullbackDescentCocycle_iff]
    have : (τ.1 ∘ (pullbackLeftPullbackSndIso f π ψ).inv.base) ∘
        (pullbackLeftPullbackSndIso f π ψ).hom.base = τ.1 :=
      funext fun x ↦ congrArg τ.1 (pullbackLeftPullbackSndIso_hom_comp_inv_apply π ψ x)
    rw [this]
    exact τ.2⟩
  invFun σ := ⟨σ.1 ∘ (pullbackLeftPullbackSndIso f π ψ).hom.base,
    (isTwistedSection_pullbackDescentCocycle_iff π ψ σ.1).2 ((mem_twistedSubmodule f c).1 σ.2)⟩
  left_inv τ := Subtype.ext (funext fun x ↦
    congrArg τ.1 (pullbackLeftPullbackSndIso_hom_comp_inv_apply π ψ x))
  right_inv σ := Subtype.ext (funext fun x ↦
    congrArg σ.1 (pullbackLeftPullbackSndIso_inv_comp_hom_apply π ψ x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The identifications `(V ×_Y T) ×_T U ≅ V ×_Y U` are natural in `U`. -/
lemma pullbackLeftPullbackSndIso_inv_pullbackMapRight {T U U' : Scheme.{u}} (π : T ⟶ Y)
    {ψ : U ⟶ T} {ψ' : U' ⟶ T} (g : U' ⟶ U) (hg : g ≫ ψ = ψ') (hg' : g ≫ ψ ≫ π = ψ' ≫ π) :
    (pullbackLeftPullbackSndIso f π ψ').inv ≫ pullbackMapRight (pullback.snd f π) g hg =
      pullbackMapRight f g hg' ≫ (pullbackLeftPullbackSndIso f π ψ).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  apply pullback.hom_ext <;> simp

/-- The presheaf of twisted sections of the pullback of a linear cocycle along `π : T ⟶ Y` is
the presheaf of twisted sections of the cocycle over the étale `T`-schemes. -/
noncomputable def twistedModulePresheafOverIso {T : Scheme.{u}} (π : T ⟶ Y) :
    twistedModulePresheaf (pullback.snd f π) (pullbackCocycle c π) ≅
      twistedModulePresheafOver c π :=
  NatIso.ofComponents (fun U ↦ (twistedSubmodulePullbackEquiv c π U.unop.hom).toModuleIso)
    (fun {U U'} g ↦ by
      ext τ : 2
      refine Subtype.ext (funext fun x ↦ congrArg τ.1 ?_)
      have := congrArg (fun m ↦ m.base x) (pullbackLeftPullbackSndIso_inv_pullbackMapRight
        (f := f) π g.unop.left (MorphismProperty.Over.w g.unop)
        (Etale.left_comp_hom_comp g.unop π))
      simpa only [Scheme.Hom.comp_apply] using this)

/-- **The sheaf of twisted sections of a linear cocycle over the étale `T`-schemes**, for
`π : T ⟶ Y`, with sections over `U ⟶ T` the twisted sections of `c` over `U ⟶ T ⟶ Y`. -/
noncomputable def twistedModuleSheafOver {T : Scheme.{u}} (π : T ⟶ Y) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj := twistedModulePresheafOver c π
  property := (Presheaf.isSheaf_of_iso_iff (twistedModulePresheafOverIso c π)).1
    (twistedModuleSheaf (pullback.snd f π) (pullbackCocycle c π)).property

/-- The sheaf of twisted sections of the pullback of a linear cocycle along `π : T ⟶ Y` is the
sheaf of twisted sections of the cocycle over the étale `T`-schemes. -/
noncomputable def twistedModuleSheafOverIso {T : Scheme.{u}} (π : T ⟶ Y) :
    twistedModuleSheaf (pullback.snd f π) (pullbackCocycle c π) ≅
      twistedModuleSheafOver c π :=
  ObjectProperty.isoMk _ (twistedModulePresheafOverIso c π)

/-- Restriction of twisted sections along the identity is the identity. -/
lemma twistedSubmoduleRestrict_id {T : Scheme.{u}} {π : T ⟶ Y} (h : 𝟙 T ≫ π = π)
    (σ : twistedSubmodule f c π) : twistedSubmoduleRestrict c (𝟙 T) h σ = σ := by
  refine Subtype.ext ?_
  rw [twistedSubmoduleRestrict_apply_coe, pullbackMapRight_id]
  rfl

/-- The structure morphism of an étale `Y`-scheme, composed with identities. -/
lemma Etale.id_comp_hom_comp_id {U : Y.Etale} : 𝟙 U.left ≫ U.hom = U.hom ≫ 𝟙 Y := by
  simp

/-- The structure morphism of an étale `Y`-scheme, composed with identities. -/
lemma Etale.id_comp_hom_comp_id' {U : Y.Etale} : 𝟙 U.left ≫ U.hom ≫ 𝟙 Y = U.hom := by
  simp

/-- The twisted sections over `U ⟶ Y` are the twisted sections over `U ⟶ Y ⟶ Y`. -/
noncomputable def twistedSubmoduleCompIdEquiv (U : Y.Etale) :
    twistedSubmodule f c U.hom ≃ₗ[Λ] twistedSubmodule f c (U.hom ≫ 𝟙 Y) :=
  LinearEquiv.ofLinearMap (twistedSubmoduleRestrict c (𝟙 U.left) Etale.id_comp_hom_comp_id)
    (twistedSubmoduleRestrict c (𝟙 U.left) Etale.id_comp_hom_comp_id')
    (LinearMap.ext fun σ ↦ (twistedSubmoduleRestrict_comp_eq c _ _ (Category.id_comp _)
      (Category.comp_id _) σ).trans (twistedSubmoduleRestrict_id c _ σ))
    (LinearMap.ext fun σ ↦ (twistedSubmoduleRestrict_comp_eq c _ _ (Category.id_comp _)
      (Category.comp_id _) σ).trans (twistedSubmoduleRestrict_id c _ σ))

/-- The sheaf of twisted sections of `c` is the sheaf of twisted sections of `c` over the étale
`Y`-schemes for `π = 𝟙 Y`. -/
noncomputable def twistedModuleSheafIsoOverId :
    twistedModuleSheaf f c ≅ twistedModuleSheafOver c (𝟙 Y) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U ↦ (twistedSubmoduleCompIdEquiv c U.unop).toModuleIso)
    (fun {U U'} g ↦ by
      ext σ : 2
      exact twistedSubmoduleRestrict_comp_eq_comp c (MorphismProperty.Over.w g.unop)
        Etale.id_comp_hom_comp_id Etale.id_comp_hom_comp_id
        (Etale.left_comp_hom_comp g.unop (𝟙 Y)) (by simp) σ))

/-- Twisted sections over the étale `T`-schemes for `π` and for `π'` agree if `π = π'`. -/
noncomputable def twistedModuleSheafOverCongr {T : Scheme.{u}} {π π' : T ⟶ Y} (h : π = π') :
    twistedModuleSheafOver c π ≅ twistedModuleSheafOver c π' := by
  subst h
  exact Iso.refl _

/-- The restriction of twisted sections along `t : T' ⟶ T`: a morphism from the sheaf of twisted
sections over the étale `T`-schemes to the pushforward of the sheaf of twisted sections over the
étale `T'`-schemes, `σ ↦ σ ∘ (V ×_Y (U ×_T T') ⟶ V ×_Y U)`. -/
noncomputable def twistedModuleSheafOverRestrict {T T' : Scheme.{u}} (π : T ⟶ Y)
    (t : T' ⟶ T) :
    twistedModuleSheafOver c π ⟶
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) t).obj (twistedModuleSheafOver c (t ≫ π)) :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom (twistedSubmoduleRestrict c (pullback.fst U.unop.hom t)
        (pullback.condition_assoc π))
      naturality {U U'} g := by
        ext σ : 2
        exact twistedSubmoduleRestrict_comp_eq_comp c (Etale.left_comp_hom_comp g.unop π)
          (pullback.condition_assoc π) (pullback.condition_assoc π)
          (Etale.left_comp_hom_comp
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ t).map g.unop) (t ≫ π))
          (by simp) σ }

/-- The components of `AlgebraicGeometry.twistedModuleSheafOverRestrict`. -/
lemma twistedModuleSheafOverRestrict_app_apply {T T' : Scheme.{u}} (π : T ⟶ Y) (t : T' ⟶ T)
    (U : T.Etale) (σ : twistedSubmodule f c (U.hom ≫ π)) :
    (twistedModuleSheafOverRestrict c π t).hom.app (Opposite.op U) σ =
      twistedSubmoduleRestrict c (pullback.fst U.hom t) (pullback.condition_assoc π) σ :=
  rfl

section Stalk

/-- A pointed étale neighbourhood `(U, u)` can be shrunk to an open subset `O` of `U` containing
the image of `u`. -/
lemma exists_fiber_map_eq_of_isOpen {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {y : Spec (.of Ω) ⟶ X} {U : X.Etale} (u : (Scheme.pointSmallEtale y).fiber.obj U)
    (O : Set U.left) (hO : IsOpen O) (hu : ∀ p, u.left.base p ∈ O) :
    ∃ (U' : X.Etale) (g : U' ⟶ U) (u' : (Scheme.pointSmallEtale y).fiber.obj U'),
      (Scheme.pointSmallEtale y).fiber.map g u' = u ∧ Set.range g.left.base ⊆ O := by
  let O' : U.left.Opens := ⟨O, hO⟩
  let U' : X.Etale := Scheme.Etale.mk (O'.ι ≫ U.hom)
  let g : U' ⟶ U := MorphismProperty.Over.homMk O'.ι rfl
  have hr : Set.range u.left.base ⊆ Set.range O'.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact hu p
  have hl : IsOpenImmersion.lift O'.ι u.left hr ≫ O'.ι = u.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U', g, CategoryTheory.Over.homMk (V := (Scheme.Etale.forget X).obj U')
    (IsOpenImmersion.lift O'.ι u.left hr) ?_, ?_, ?_⟩
  · change IsOpenImmersion.lift O'.ι u.left hr ≫ O'.ι ≫ U.hom = y
    rw [reassoc_of% hl]
    exact CategoryTheory.Over.w u
  · exact CategoryTheory.Over.OverMorphism.ext hl
  · rintro _ ⟨p, rfl⟩
    have h := Set.mem_range_self (f := O'.ι.base) p
    rw [Scheme.Opens.range_ι] at h
    exact h

/-- **Germs of the adjoint of a morphism to a pushforward.** Let `t : T' ⟶ T`, `φ : G ⟶ t_* H`
and `ψ : t^* G ⟶ H` its adjoint. Through `(t^* G)_y ≅ G_{y ≫ t}`, the germ at a point of `W` of
a section `σ` of `G` over `W` is sent by `ψ` to the germ at a point `v` of `V` of the restriction
of `φ σ` along a morphism `V ⟶ W` over `t`. -/
lemma Etale.toPresheafFiber_comp_upperStarCompSheafFiberIso_inv_comp_sheafFiber_map
    {T T' : Scheme.{u}} (t : T' ⟶ T) {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {H : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {φ : G ⟶ (Etale.lowerStar (ModuleCat.{u + 1} Λ) t).obj H}
    {ψ : (Etale.upperStar (ModuleCat.{u + 1} Λ) t).obj G ⟶ H}
    (hψ : (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).homEquiv G H ψ = φ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ T') {V : T'.Etale}
    {W : T.Etale} (φ₀ : V.left ⟶ W.left) (hφ₀ : φ₀ ≫ W.hom = V.hom ≫ t)
    (v : (Scheme.pointSmallEtale y).fiber.obj V) :
    (Scheme.pointSmallEtale (y ≫ t)).toPresheafFiber W
        (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (y ≫ t))
          (V := (Scheme.Etale.forget T).obj W) (v.left ≫ φ₀)
          (Etale.fiber_left_comp_comp_hom_eq t y hφ₀ v)) G.obj ≫
        ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t y).app G).inv ≫
          (Scheme.pointSmallEtale y).sheafFiber.map ψ =
      φ.hom.app (Opposite.op W) ≫ H.obj.map (Etale.homToPullback t φ₀ hφ₀).op ≫
        (Scheme.pointSmallEtale y).toPresheafFiber V v H.obj := by
  subst hψ
  rw [← Etale.unit_app_map_toPresheafFiber_upperStarCompSheafFiberIso_hom (ModuleCat.{u + 1} Λ)
    t G y φ₀ hφ₀ v]
  simp only [Category.assoc, Iso.app_inv, Iso.hom_inv_id_app_assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rw [Adjunction.homEquiv_unit]
  erw [reassoc_of% (ψ.hom.naturality (Etale.homToPullback t φ₀ hφ₀).op)]
  rfl

/-- The germ formula
`AlgebraicGeometry.Etale.toPresheafFiber_comp_upperStarCompSheafFiberIso_inv_comp_sheafFiber_map`
for the restriction of twisted sections. -/
lemma upperStarCompSheafFiberIso_inv_sheafFiber_map_toPresheafFiber_twisted {T T' : Scheme.{u}}
    (π : T ⟶ Y) (t : T' ⟶ T)
    {ψ : (Etale.upperStar (ModuleCat.{u + 1} Λ) t).obj (twistedModuleSheafOver c π) ⟶
      twistedModuleSheafOver c (t ≫ π)}
    (hψ : (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).homEquiv _ _ ψ =
      twistedModuleSheafOverRestrict c π t)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ T') {V : T'.Etale}
    {W : T.Etale} (φ₀ : V.left ⟶ W.left) (hφ₀ : φ₀ ≫ W.hom = V.hom ≫ t)
    (v : (Scheme.pointSmallEtale y).fiber.obj V) (hφ₀' : φ₀ ≫ W.hom ≫ π = V.hom ≫ t ≫ π)
    (σ : twistedSubmodule f c (W.hom ≫ π)) :
    (((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t y).app
        (twistedModuleSheafOver c π)).inv ≫ (Scheme.pointSmallEtale y).sheafFiber.map ψ)
      ((Scheme.pointSmallEtale (y ≫ t)).toPresheafFiber W
        (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (y ≫ t))
          (V := (Scheme.Etale.forget T).obj W) (v.left ≫ φ₀)
          (Etale.fiber_left_comp_comp_hom_eq t y hφ₀ v)) (twistedModuleSheafOver c π).obj σ) =
      (Scheme.pointSmallEtale y).toPresheafFiber V v (twistedModuleSheafOver c (t ≫ π)).obj
        (twistedSubmoduleRestrict c φ₀ hφ₀' σ) := by
  have := ConcreteCategory.congr_hom
    (Etale.toPresheafFiber_comp_upperStarCompSheafFiberIso_inv_comp_sheafFiber_map t hψ y φ₀ hφ₀
      v) σ
  simp only [ConcreteCategory.comp_apply] at this
  refine this.trans (congrArg _ ?_)
  exact twistedSubmoduleRestrict_comp_eq c _ _ _ (Etale.homToPullback_left_fst _ _ _) σ

/-- Restricting two twisted sections along a morphism into the open subset where they agree
gives equal sections. -/
lemma twistedSubmoduleRestrict_eq_of_range_subset {T T' : Scheme.{u}} {π : T ⟶ Y}
    {π' : T' ⟶ Y} {σ₁ σ₂ : twistedSubmodule f c π} {O : Set T}
    (hO : ∀ x, σ₁.1 x = σ₂.1 x ↔ (pullback.snd f π).base x ∈ O) (a : T' ⟶ T) (ha : a ≫ π = π')
    (h : Set.range a.base ⊆ O) :
    twistedSubmoduleRestrict c a ha σ₁ = twistedSubmoduleRestrict c a ha σ₂ := by
  refine Subtype.ext (funext fun x ↦ (hO _).2 ?_)
  rw [← Scheme.Hom.comp_apply, pullbackMapRight_snd, Scheme.Hom.comp_apply]
  exact h ⟨_, rfl⟩

variable [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f]

omit [QuasiSeparated f] in
/-- Injectivity on stalks of the adjoint of the restriction of twisted sections. -/
lemma injective_sheafFiber_map_twisted {T T' : Scheme.{u}} (π : T ⟶ Y) (t : T' ⟶ T)
    {ψ : (Etale.upperStar (ModuleCat.{u + 1} Λ) t).obj (twistedModuleSheafOver c π) ⟶
      twistedModuleSheafOver c (t ≫ π)}
    (hψ : (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).homEquiv _ _ ψ =
      twistedModuleSheafOverRestrict c π t)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ T') :
    Function.Injective (((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t y).app
        (twistedModuleSheafOver c π)).inv ≫ (Scheme.pointSmallEtale y).sheafFiber.map ψ) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro a b hab
  obtain ⟨W, w, σ₁, σ₂, rfl, rfl⟩ :=
    (Scheme.pointSmallEtale (y ≫ t)).toPresheafFiber_jointly_surjective₂
      (P := (twistedModuleSheafOver c π).obj) a b
  let V : T'.Etale := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ t).obj W
  let v : (Scheme.pointSmallEtale y).fiber.obj V :=
    (Scheme.pointSmallEtaleFiberEtaleIso t y).inv.app W w
  have hvw : v.left ≫ pullback.fst W.hom t = w.left :=
    Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst t y W w
  have hw : w = CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (y ≫ t))
      (V := (Scheme.Etale.forget T).obj W) (v.left ≫ pullback.fst W.hom t)
      (Etale.fiber_left_comp_comp_hom_eq t y pullback.condition v) :=
    CategoryTheory.Over.OverMorphism.ext hvw.symm
  have hab' := hab
  rw [hw, upperStarCompSheafFiberIso_inv_sheafFiber_map_toPresheafFiber_twisted c π t hψ y
      (pullback.fst W.hom t) pullback.condition v (pullback.condition_assoc π),
    upperStarCompSheafFiberIso_inv_sheafFiber_map_toPresheafFiber_twisted c π t hψ y
      (pullback.fst W.hom t) pullback.condition v (pullback.condition_assoc π)] at hab'
  obtain ⟨V', g, v', hv', hg⟩ := ((Scheme.pointSmallEtale y).toPresheafFiber_eq_iff'
    (P := (twistedModuleSheafOver c (t ≫ π)).obj) V v _ _).1 hab'
  obtain ⟨O, hO, hOiff⟩ := IsTwistedSection.exists_isOpen_eq_iff
    ((mem_twistedSubmodule f c).1 σ₁.2) ((mem_twistedSubmodule f c).1 σ₂.2)
  obtain ⟨x', hx'⟩ := (pullback.snd f (V'.hom ≫ t ≫ π)).surjective
    (v'.left.base (default : Spec (.of Ω)))
  have hx : σ₁.1 ((pullbackMapRight f (pullback.fst W.hom t) (pullback.condition_assoc π)).base
        ((pullbackMapRight f g.left (Etale.left_comp_hom_comp g (t ≫ π))).base x')) =
      σ₂.1 ((pullbackMapRight f (pullback.fst W.hom t) (pullback.condition_assoc π)).base
        ((pullbackMapRight f g.left (Etale.left_comp_hom_comp g (t ≫ π))).base x')) :=
    congrFun (congrArg Subtype.val hg) x'
  have hwO (p : Spec (.of Ω)) : w.left.base p ∈ O := by
    have h := (hOiff _).1 hx
    have e₁ := congrArg (fun m ↦ m.base x')
      (show pullbackMapRight f g.left (Etale.left_comp_hom_comp g (t ≫ π)) ≫
          pullbackMapRight f (pullback.fst W.hom t) (pullback.condition_assoc π) ≫
            pullback.snd f (W.hom ≫ π) =
        pullback.snd f (V'.hom ≫ t ≫ π) ≫ g.left ≫ pullback.fst W.hom t by simp)
    simp only [Scheme.Hom.comp_apply] at e₁
    erw [e₁, hx'] at h
    have hv'l : v'.left ≫ g.left = v.left := congrArg CategoryTheory.CommaMorphism.left hv'
    rw [Subsingleton.elim p (default : Spec (.of Ω)), ← hvw, ← hv'l, Category.assoc,
      Scheme.Hom.comp_apply]
    exact h
  obtain ⟨W₀, g₀, w₀, hw₀, hg₀⟩ := exists_fiber_map_eq_of_isOpen w O hO hwO
  rw [← hw₀, ← GrothendieckTopology.Point.toPresheafFiber_w_apply,
    ← GrothendieckTopology.Point.toPresheafFiber_w_apply]
  exact congrArg _ (twistedSubmoduleRestrict_eq_of_range_subset c hOiff _ _ hg₀)

/-- Surjectivity on stalks of the adjoint of the restriction of twisted sections: a germ of a
twisted section at a geometric point `y` of `T'` is, near `y`, the restriction of a twisted
section over an étale neighbourhood of `y ≫ t` in `T`. Such a section is obtained over the
strict localization of `T` at `y ≫ t`, where the cover has a section, and descends to an
affine étale neighbourhood. -/
lemma surjective_sheafFiber_map_twisted (hc : IsDescentCocycle f (fun z ↦ c z))
    {T T' : Scheme.{u}} (π : T ⟶ Y) (t : T' ⟶ T)
    {ψ : (Etale.upperStar (ModuleCat.{u + 1} Λ) t).obj (twistedModuleSheafOver c π) ⟶
      twistedModuleSheafOver c (t ≫ π)}
    (hψ : (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).homEquiv _ _ ψ =
      twistedModuleSheafOverRestrict c π t)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ T') :
    Function.Surjective (((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t y).app
        (twistedModuleSheafOver c π)).inv ≫ (Scheme.pointSmallEtale y).sheafFiber.map ψ) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro b
  obtain ⟨U, u, τ, rfl⟩ := (Scheme.pointSmallEtale y).toPresheafFiber_jointly_surjective
    (P := (twistedModuleSheafOver c (t ≫ π)).obj) b
  have hu : u.left ≫ U.hom = y := CategoryTheory.Over.w u
  have : Etale U.hom := U.prop
  -- a point of `V ×_Y Spec Ω`
  obtain ⟨p, -⟩ := (pullback.snd f (y ≫ t ≫ π)).surjective (default : Spec (.of Ω))
  have hux : u.left ≫ U.hom ≫ t ≫ π = y ≫ t ≫ π := by rw [reassoc_of% hu]
  -- the strict localization of `T` at `y ≫ t`
  have hs₀ : Spec.map (Scheme.strictHenselizationEval (y ≫ t)) ≫
      Scheme.strictLocalizationToBase (y ≫ t) = y ≫ t :=
    Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase (y ≫ t)
  have hs₀x : Spec.map (Scheme.strictHenselizationEval (y ≫ t)) ≫
      Scheme.strictLocalizationToBase (y ≫ t) ≫ π = y ≫ t ≫ π := by rw [reassoc_of% hs₀]
  obtain ⟨σZ, hσZ, hσZx⟩ := IsTwistedSection.exists_apply_eq_of_isStrictlyHenselian
    (R := ↑(Scheme.strictHenselization (y ≫ t))) hc
    (Scheme.strictLocalizationToBase (y ≫ t) ≫ π)
    ((pullbackMapRight f _ hs₀x).base p) (τ.1 ((pullbackMapRight f u.left hux).base p))
  -- descent to an affine pointed étale neighbourhood
  let ι := InitiallySmall.fromCofilteredInitialModel.{u}
    (Scheme.AffinePointedEtaleNeighborhood (y ≫ t))
  have hC := (Functor.Initial.isLimitWhiskerEquiv ι (Scheme.strictLocalizationCone (y ≫ t))).symm
    (Scheme.isLimitStrictLocalizationCone (y ≫ t))
  have hD : ∀ j, IsAffine ((ι ⋙ Scheme.affineNeighborhoodDiagram (y ≫ t)).obj j) :=
    fun j ↦ (ι.obj j).2
  obtain ⟨j, σj, hσj, hσjZ⟩ := IsTwistedSection.exists_of_isLimit hc hC
    (fun j ↦ (ι.obj j).obj.1.hom ≫ π) (fun g ↦ Etale.left_comp_hom_comp (ι.map g).hom.1 π)
    (Scheme.strictLocalizationToBase (y ≫ t) ≫ π)
    (fun j ↦ Scheme.strictLocalizationCone_π_app_hom_assoc (y ≫ t) (ι.obj j) π) hσZ
  let W : T.Etale := (ι.obj j).obj.1
  let w : (Scheme.pointSmallEtale (y ≫ t)).fiber.obj W := (ι.obj j).obj.2
  have : Etale W.hom := W.prop
  have hw : Spec.map (Scheme.strictHenselizationEval (y ≫ t)) ≫
      (Scheme.strictLocalizationCone (y ≫ t)).π.app (ι.obj j) = w.left :=
    Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationCone_π_app (y ≫ t) (ι.obj j)
  have hww : w.left ≫ W.hom = y ≫ t := CategoryTheory.Over.w w
  let σ : twistedSubmodule f c (W.hom ≫ π) := ⟨σj, hσj⟩
  -- the common refinement `U ×_T W`
  let V₁ : T'.Etale := Scheme.Etale.mk (pullback.fst (U.hom ≫ t) W.hom ≫ U.hom)
  have hcond : u.left ≫ U.hom ≫ t = w.left ≫ W.hom := by rw [reassoc_of% hu, hww]
  let v₁ : (Scheme.pointSmallEtale y).fiber.obj V₁ :=
    CategoryTheory.Over.homMk (V := (Scheme.Etale.forget T').obj V₁)
      (pullback.lift u.left w.left hcond) (by
        change pullback.lift u.left w.left hcond ≫ pullback.fst (U.hom ≫ t) W.hom ≫ U.hom = y
        rw [pullback.lift_fst_assoc, hu])
  have hv₁f : v₁.left ≫ pullback.fst (U.hom ≫ t) W.hom = u.left := pullback.lift_fst _ _ _
  have hv₁s : v₁.left ≫ pullback.snd (U.hom ≫ t) W.hom = w.left := pullback.lift_snd _ _ _
  have h₁ : pullback.fst (U.hom ≫ t) W.hom ≫ U.hom ≫ t ≫ π = V₁.hom ≫ t ≫ π := by
    simp [V₁]
  have h₂ : pullback.snd (U.hom ≫ t) W.hom ≫ W.hom ≫ π = V₁.hom ≫ t ≫ π := by
    simp [V₁, ← pullback.condition_assoc]
  let τ₁ := twistedSubmoduleRestrict c (pullback.fst (U.hom ≫ t) W.hom) h₁ τ
  let τ₂ := twistedSubmoduleRestrict c (pullback.snd (U.hom ≫ t) W.hom) h₂ σ
  obtain ⟨O, hO, hOiff⟩ := IsTwistedSection.exists_isOpen_eq_iff
    ((mem_twistedSubmodule f c).1 τ₁.2) ((mem_twistedSubmodule f c).1 τ₂.2)
  have hv₁x : v₁.left ≫ V₁.hom ≫ t ≫ π = y ≫ t ≫ π := by
    rw [← h₁, reassoc_of% hv₁f, hux]
  have hxO (q : Spec (.of Ω)) : v₁.left.base q ∈ O := by
    have h : τ₁.1 ((pullbackMapRight f v₁.left hv₁x).base p) =
        τ₂.1 ((pullbackMapRight f v₁.left hv₁x).base p) := by
      simp only [τ₁, τ₂, twistedSubmoduleRestrict_apply_coe, Function.comp_apply]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        pullbackMapRight_comp_eq h₁ hv₁x hux hv₁f,
        pullbackMapRight_comp_eq h₂ hv₁x (by rw [← hw, Category.assoc,
          Scheme.strictLocalizationCone_π_app_hom_assoc, hs₀x]) hv₁s, ← hσZx, ← hσjZ]
      simp only [σ, Function.comp_apply]
      rw [← Scheme.Hom.comp_apply]
      congr 2
      rw [pullbackMapRight_comp_eq
        (t := ((Scheme.strictLocalizationCone (y ≫ t)).whisker ι).π.app j) _ _ _ hw]
    have := (hOiff _).1 h
    rw [← Scheme.Hom.comp_apply, pullbackMapRight_snd, Scheme.Hom.comp_apply] at this
    rwa [Subsingleton.elim q ((pullback.snd f (y ≫ t ≫ π)).base p)]
  obtain ⟨V, g₁, v, hv, hg₁⟩ := exists_fiber_map_eq_of_isOpen v₁ O hO hxO
  have hv' : v.left ≫ g₁.left = v₁.left := congrArg CategoryTheory.CommaMorphism.left hv
  have hφ₀ : (g₁.left ≫ pullback.snd (U.hom ≫ t) W.hom) ≫ W.hom = V.hom ≫ t := by
    rw [Category.assoc, ← pullback.condition, ← MorphismProperty.Over.w g₁]
    simp [V₁]
  have hφ₀' : (g₁.left ≫ pullback.snd (U.hom ≫ t) W.hom) ≫ W.hom ≫ π = V.hom ≫ t ≫ π := by
    rw [Category.assoc, reassoc_of% hφ₀]
  let k : V₁ ⟶ U := MorphismProperty.Over.homMk (pullback.fst (U.hom ≫ t) W.hom) rfl
  have hk : (Scheme.pointSmallEtale y).fiber.map (g₁ ≫ k) v = u := by
    rw [Functor.map_comp_apply, hv]
    exact CategoryTheory.Over.OverMorphism.ext hv₁f
  refine ⟨(Scheme.pointSmallEtale (y ≫ t)).toPresheafFiber W
    (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (y ≫ t))
      (V := (Scheme.Etale.forget T).obj W) (v.left ≫ g₁.left ≫ pullback.snd (U.hom ≫ t) W.hom)
      (Etale.fiber_left_comp_comp_hom_eq t y hφ₀ v)) (twistedModuleSheafOver c π).obj σ, ?_⟩
  rw [upperStarCompSheafFiberIso_inv_sheafFiber_map_toPresheafFiber_twisted c π t hψ y _ hφ₀ v
    hφ₀', ← hk, ← GrothendieckTopology.Point.toPresheafFiber_w_apply]
  congr 1
  rw [← twistedSubmoduleRestrict_comp_eq c h₂ (Etale.left_comp_hom_comp g₁ (t ≫ π)) hφ₀' rfl,
    twistedSubmoduleRestrict_eq_of_range_subset c
      (σ₁ := twistedSubmoduleRestrict c (pullback.snd (U.hom ≫ t) W.hom) h₂ σ)
      (σ₂ := twistedSubmoduleRestrict c (pullback.fst (U.hom ≫ t) W.hom) h₁ τ)
      (fun x ↦ eq_comm.trans (hOiff x)) g₁.left _ hg₁]
  exact twistedSubmoduleRestrict_comp_eq c h₁ _ _ rfl τ


/-- **Pullback of twisted sheaves over étale schemes.** For `π : T ⟶ Y` and `t : T' ⟶ T`, the
adjoint `t^* F_π ⟶ F_{t ≫ π}` of the restriction of twisted sections is an isomorphism, where
`F_π` is the sheaf of twisted sections over the étale `T`-schemes. It is checked on the stalks
at the geometric points of `T'`, see `AlgebraicGeometry.injective_sheafFiber_map_twisted` and
`AlgebraicGeometry.surjective_sheafFiber_map_twisted`. -/
theorem isIso_homEquiv_symm_twistedModuleSheafOverRestrict
    (hc : IsDescentCocycle f (fun z ↦ c z)) {T T' : Scheme.{u}} (π : T ⟶ Y) (t : T' ⟶ T) :
    IsIso (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).homEquiv _ _).symm
      (twistedModuleSheafOverRestrict c π t)) := by
  have hψ := ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).homEquiv _ _
    ).apply_symm_apply (twistedModuleSheafOverRestrict c π t)
  generalize ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).homEquiv _ _).symm
    (twistedModuleSheafOverRestrict c π t) = ψ at hψ ⊢
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun z ↦ ?_
  rw [Scheme.uliftPointSmallEtale, NatIso.isIso_map_iff
    ((Scheme.pointSmallEtale _).uliftSheafFiberIso (ModuleCat.{u + 1} Λ))]
  have : IsIso (((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t
      (T'.algClosurePoint z)).app (twistedModuleSheafOver c π)).inv ≫
        (Scheme.pointSmallEtale (T'.algClosurePoint z)).sheafFiber.map ψ) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨injective_sheafFiber_map_twisted c π t hψ _, surjective_sheafFiber_map_twisted c hc π t hψ _⟩
  exact IsIso.of_isIso_comp_left (((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) t
    (T'.algClosurePoint z)).app (twistedModuleSheafOver c π)).inv)
    ((Scheme.pointSmallEtale (T'.algClosurePoint z)).sheafFiber.map ψ)

/-- **Pullback of twisted sheaves over étale schemes**, as an isomorphism
`t^* F_π ≅ F_{t ≫ π}`, see
`AlgebraicGeometry.isIso_homEquiv_symm_twistedModuleSheafOverRestrict`. -/
noncomputable def upperStarTwistedModuleSheafOverIso (hc : IsDescentCocycle f (fun z ↦ c z))
    {T T' : Scheme.{u}} (π : T ⟶ Y) (t : T' ⟶ T) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) t).obj (twistedModuleSheafOver c π) ≅
      twistedModuleSheafOver c (t ≫ π) :=
  have := isIso_homEquiv_symm_twistedModuleSheafOverRestrict c hc π t
  asIso (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).homEquiv _ _).symm
    (twistedModuleSheafOverRestrict c π t))

/-- The pullback of the sheaf of twisted sections of `c` along `π : T ⟶ Y` is the sheaf of
twisted sections of `c` over the étale `T`-schemes. -/
noncomputable def upperStarTwistedModuleSheafIsoOver (hc : IsDescentCocycle f (fun z ↦ c z))
    {T : Scheme.{u}} (π : T ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) π).obj (twistedModuleSheaf f c) ≅
      twistedModuleSheafOver c π :=
  (Etale.upperStar (ModuleCat.{u + 1} Λ) π).mapIso (twistedModuleSheafIsoOverId c) ≪≫
    upperStarTwistedModuleSheafOverIso c hc (𝟙 Y) π ≪≫
    twistedModuleSheafOverCongr c (Category.comp_id π)

end Stalk

/-- **Pullback of twisted sheaves.** For any `π : T ⟶ Y`, the pullback of the sheaf of twisted
sections of `c` is the sheaf of twisted sections of the pulled back cocycle. -/
noncomputable def upperStarTwistedModuleSheafIso [WeaklyEtale f] [Surjective f] [QuasiCompact f]
    [QuasiSeparated f] (hc : IsDescentCocycle f (fun z ↦ c z)) {T : Scheme.{u}} (π : T ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) π).obj (twistedModuleSheaf f c) ≅
      twistedModuleSheaf (pullback.snd f π) (pullbackCocycle c π) :=
  upperStarTwistedModuleSheafIsoOver c hc π ≪≫ (twistedModuleSheafOverIso c π).symm

/-- Restriction of twisted sections along an isomorphism of the base is bijective. -/
lemma bijective_twistedSubmoduleRestrict_of_isIso {T T' : Scheme.{u}} {π : T ⟶ Y}
    {π' : T' ⟶ Y} (e : T' ⟶ T) [IsIso e] (he : e ≫ π = π') :
    Function.Bijective (twistedSubmoduleRestrict c e he) := by
  have he' : inv e ≫ π' = π := by rw [← he, IsIso.inv_hom_id_assoc]
  refine Function.bijective_iff_has_inverse.2 ⟨twistedSubmoduleRestrict c (inv e) he',
    fun σ ↦ ?_, fun σ ↦ ?_⟩
  · exact (twistedSubmoduleRestrict_comp_eq c he he' (Category.id_comp π) (by simp) σ).trans
      (twistedSubmoduleRestrict_id c _ σ)
  · exact (twistedSubmoduleRestrict_comp_eq c he' he (Category.id_comp π') (by simp) σ).trans
      (twistedSubmoduleRestrict_id c _ σ)

/-- The pullback map on global sections along `q : Q ⟶ P` is an isomorphism if and only if the
composite of the unit of `q^* ⊣ q_*` at the terminal object with the identification of the base
change of the terminal object is. -/
lemma isIso_globalSectionsUpperStarMap_iff {P Q : Scheme.{u}} (q : Q ⟶ P)
    (G : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q G) ↔
      IsIso (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app G).hom.app
          (Opposite.op (⊤_ P.Etale)) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj G).obj.map
          (PreservesTerminal.iso q.Etale).inv.op) := by
  rw [Etale.globalSectionsUpperStarMap, isIso_comp_left_iff, ← Category.assoc,
    isIso_comp_right_iff]
  rfl

/-- The criterion `AlgebraicGeometry.isIso_globalSectionsUpperStarMap_iff` is invariant under
isomorphisms of sheaves. -/
lemma isIso_unit_app_comp_map_of_iso {P Q : Scheme.{u}} (q : Q ⟶ P)
    {G G' : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : G ≅ G')
    (h : IsIso (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app G).hom.app
          (Opposite.op (⊤_ P.Etale)) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj G).obj.map
          (PreservesTerminal.iso q.Etale).inv.op)) :
    IsIso (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app G').hom.app
          (Opposite.op (⊤_ P.Etale)) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj G').obj.map
          (PreservesTerminal.iso q.Etale).inv.op) := by
  have hu := congrArg (fun φ ↦ φ.hom.app (Opposite.op (⊤_ P.Etale)))
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.naturality α.hom)
  have hn := ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).map α.hom).hom.naturality
    (PreservesTerminal.iso q.Etale).inv.op
  have e : α.hom.hom.app (Opposite.op (⊤_ P.Etale)) ≫
      (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app G').hom.app
          (Opposite.op (⊤_ P.Etale)) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj G').obj.map
          (PreservesTerminal.iso q.Etale).inv.op) =
      (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app G).hom.app
          (Opposite.op (⊤_ P.Etale)) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj G).obj.map
          (PreservesTerminal.iso q.Etale).inv.op) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).map α.hom).hom.app
          (Opposite.op (⊤_ Q.Etale)) := by
    simp only [Functor.id_map, Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app] at hu
    rw [← Category.assoc, hu, Category.assoc, Category.assoc]
    erw [hn]
    rfl
  have : IsIso (α.hom.hom.app (Opposite.op (⊤_ P.Etale))) :=
    (NatIso.isIso_app_of_isIso _ _)
  rw [(IsIso.eq_inv_comp _).2 e]
  infer_instance

/-- **Global sections of pulled back twisted sheaves.** If the pullback of global sections
along `q : Q ⟶ P` is bijective for the pullback of the sheaf of twisted sections of `c` to
`p : P ⟶ Y`, then restriction of twisted sections from `P` to `Q` is bijective. -/
theorem bijective_twistedRestrict_of_isIso_globalSectionsUpperStarMap [WeaklyEtale f]
    [Surjective f] [QuasiCompact f] [QuasiSeparated f] (hc : IsDescentCocycle f (fun z ↦ c z))
    {P Q : Scheme.{u}} (p : P ⟶ Y) (q : Q ⟶ P)
    (h : IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj (twistedModuleSheaf f c)))) :
    Function.Bijective (fun σ : twistedSubmodule f c p ↦
      (⟨σ.1 ∘ (pullbackMapRight f q rfl).base, ((mem_twistedSubmodule f c).1 σ.2).comp q rfl⟩ :
        twistedSubmodule f c (q ≫ p))) := by
  have h₁ := isIso_unit_app_comp_map_of_iso q (upperStarTwistedModuleSheafIsoOver c hc p)
    ((isIso_globalSectionsUpperStarMap_iff q _).1 h)
  have hψ := ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).homEquiv _ _
    ).apply_symm_apply (twistedModuleSheafOverRestrict c p q)
  have : IsIso (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).homEquiv _ _).symm
      (twistedModuleSheafOverRestrict c p q)) :=
    isIso_homEquiv_symm_twistedModuleSheafOverRestrict c hc p q
  generalize ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).homEquiv _ _).symm
    (twistedModuleSheafOverRestrict c p q) = ψ at hψ this
  -- the restriction `Γ(P, F_p) ⟶ Γ(Q, F_{q ≫ p})` is an isomorphism
  have h₂ : IsIso ((twistedModuleSheafOverRestrict c p q).hom.app (Opposite.op (⊤_ P.Etale)) ≫
      (twistedModuleSheafOver c (q ≫ p)).obj.map (PreservesTerminal.iso q.Etale).inv.op) := by
    have e : (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app
          (twistedModuleSheafOver c p)).hom.app (Opposite.op (⊤_ P.Etale)) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj (twistedModuleSheafOver c p)).obj.map
          (PreservesTerminal.iso q.Etale).inv.op) ≫ ψ.hom.app (Opposite.op (⊤_ Q.Etale)) =
        (twistedModuleSheafOverRestrict c p q).hom.app (Opposite.op (⊤_ P.Etale)) ≫
          (twistedModuleSheafOver c (q ≫ p)).obj.map (PreservesTerminal.iso q.Etale).inv.op := by
      rw [← hψ, Adjunction.homEquiv_unit, Category.assoc, ψ.hom.naturality]
      rfl
    rw [← e]
    infer_instance
  have hb := (ConcreteCategory.isIso_iff_bijective _).1 h₂
  have : IsIso (⊤_ P.Etale).hom := Etale.isIso_terminal_hom P
  have : IsIso (⊤_ Q.Etale).hom := Etale.isIso_terminal_hom Q
  have hα := bijective_twistedSubmoduleRestrict_of_isIso c (π := p) (⊤_ P.Etale).hom rfl
  have hβ := bijective_twistedSubmoduleRestrict_of_isIso c (π := q ≫ p) (⊤_ Q.Etale).hom rfl
  have hcomm : ⇑(twistedSubmoduleRestrict c (π := q ≫ p) (⊤_ Q.Etale).hom rfl) ∘
      ⇑(twistedSubmoduleRestrict c (π := p) q rfl) =
      ⇑((twistedModuleSheafOverRestrict c p q).hom.app (Opposite.op (⊤_ P.Etale)) ≫
        (twistedModuleSheafOver c (q ≫ p)).obj.map (PreservesTerminal.iso q.Etale).inv.op) ∘
      ⇑(twistedSubmoduleRestrict c (π := p) (⊤_ P.Etale).hom rfl) := by
    funext σ
    have hj : ((PreservesTerminal.iso q.Etale).inv).left ≫ pullback.snd (⊤_ P.Etale).hom q =
        (⊤_ Q.Etale).hom := MorphismProperty.Over.w (PreservesTerminal.iso q.Etale).inv
    have hd : (pullback.fst (⊤_ P.Etale).hom q ≫ (⊤_ P.Etale).hom) ≫ p =
        pullback.snd (⊤_ P.Etale).hom q ≫ q ≫ p := by
      rw [Category.assoc, pullback.condition_assoc]
    have hd' : (((PreservesTerminal.iso q.Etale).inv).left ≫ pullback.fst (⊤_ P.Etale).hom q ≫
        (⊤_ P.Etale).hom) ≫ p = (⊤_ Q.Etale).hom ≫ q ≫ p := by
      rw [Category.assoc, hd, reassoc_of% hj]
    have R : twistedSubmoduleRestrict c ((PreservesTerminal.iso q.Etale).inv).left
        (Etale.left_comp_hom_comp (PreservesTerminal.iso q.Etale).inv (q ≫ p))
        (twistedSubmoduleRestrict c (pullback.fst (⊤_ P.Etale).hom q) (pullback.condition_assoc p)
          (twistedSubmoduleRestrict c (⊤_ P.Etale).hom rfl σ)) =
        twistedSubmoduleRestrict c _ hd' σ := by
      rw [twistedSubmoduleRestrict_comp_eq c rfl (pullback.condition_assoc p) hd rfl]
      exact twistedSubmoduleRestrict_comp_eq c hd _ hd' rfl _
    refine (twistedSubmoduleRestrict_comp_eq c rfl rfl (Category.assoc _ _ _) rfl σ).trans
      (Eq.trans ?_ R.symm)
    refine twistedSubmoduleRestrict_congr c _ _ ?_ σ
    rw [← reassoc_of% hj, pullback.condition]
  have := (Function.Bijective.of_comp_iff' hβ _).1 (hcomm ▸ hb.comp hα)
  exact this

end PullbackComparison

end AlgebraicGeometry

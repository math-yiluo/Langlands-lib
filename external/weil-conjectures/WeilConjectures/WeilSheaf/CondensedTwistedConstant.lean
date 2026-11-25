/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedLisseRepresentation

/-!
# Galois descent at the finite levels and twisted constant sheaves

`WeilConjectures.WeilSheaf.CondensedLisseRepresentation` proves effective Galois descent of
module objects along a covering `q : Y ⟶ X` with an action `ρ` of a finite monoid `Γ`
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_obj_iso_of_galoisDescentDatum`),
conditionally on the *Galois comparison* `q^* q_* N ⟶ ∏_σ (ρ σ)^* N` being an isomorphism. This
file proves that this holds for free Galois actions, hence at the finite levels
`q_K : X₀ ⊗_k K ⟶ X₀`, and uses it to realise characters of finite order of the Frobenius as
module objects on `X₀` (twisted constant sheaves).

## Free Galois coverings

* `AlgebraicGeometry.ProEtale.IsFreeAction`: an action `ρ` on `Y` is free if `t ≫ ρ σ = t ≫ ρ τ`
  on a nonempty scheme forces `σ = τ`.
* `AlgebraicGeometry.ProEtale.nonempty_isColimit_cofan_pullbackLift`: for a free Galois action,
  the graphs `(𝟙, w ≫ ρ σ) : W ⟶ W ×_X Y` exhibit `W ×_X Y` as `∐_σ W`.
* `AlgebraicGeometry.ProEtale.isLimitFanGaloisComponentRestriction`: hence, with the pullbacks
  along weakly étale morphisms computed by restriction, the Galois components
  `j_q^* q_* G ⟶ j_{ρ σ}^* G` are on sections the restrictions `G(W ×_X Y) ⟶ ∏_σ G(W)`
  along the graphs, and form a limit fan
  (`AlgebraicGeometry.ProEtale.isLimitSectionsFanOfIsColimitCofan`).
* `AlgebraicGeometry.ProEtale.isLimitFanUpperStarGaloisComponent`: the same for the pullbacks
  `q^*` of abelian sheaves, transported along `upperStarIsoLocalizationRestriction`
  (`CategoryTheory.Adjunction.isLimitFanGaloisComponentOfIso`).
* `AlgebraicGeometry.ProEtale.CondensedRing.isIso_galoisComparison`: **the Galois comparison of
  module objects is an isomorphism** for a free Galois action, transported along the forgetful
  functors (`CategoryTheory.Adjunction.isLimitFanGaloisComponentOfForget`).

## The finite levels

* `AlgebraicGeometry.Scheme.Hom.finiteLevelGaloisAction`: the action `σ ↦ 𝟙 × Spec (χ σ)` on
  `X₀ ⊗_k K` of a monoid `Γ` through `χ : Γ ≃* Gal(K / k)`; it is Galois
  (`AlgebraicGeometry.ProEtale.CondensedRing.isGaloisAction_finiteLevelGaloisAction`) and free
  (`AlgebraicGeometry.ProEtale.isFreeAction_finiteLevelGaloisMap`, from the injectivity of the
  ring homomorphisms `K ⟶ Γ(T, 𝒪_T)` for `T` nonempty).
* `AlgebraicGeometry.ProEtale.CondensedRing.isIso_galoisComparison_finiteLevelProj` and
  `CondensedRing.exists_upperStar_finiteLevelProj_obj_iso_of_galoisDescentDatum`:
  effective Galois descent of module objects along `X₀ ⊗_k K ⟶ X₀` holds unconditionally.

## Twisted constant module objects

* `CategoryTheory.Adjunction.exists_iso_twist`: twisting the canonical descent datum of `L M₀`
  by an anti-homomorphism `a : Γ →* (Aut M₀)ᵐᵒᵖ` gives a descent datum, which is effective.
* `AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_finiteLevelProj_obj_iso_twist`: for
  a module object `M₀` on `X₀` (e.g. the constant `Λ_{X₀}^r`) and `a : Γ →* (Aut M₀)ᵐᵒᵖ`, a
  module object `M` on `X₀` with `q_K^* M ≅ q_K^* M₀`, the Galois structure of `q_K^* M`
  corresponding to the one of `q_K^* M₀` twisted by `a`.
* `CondensedRing.exists_upperStar_finiteLevelProj_obj_iso_frobeniusTwist`:
  over a finite field, for an automorphism `A` of `M₀` with `A ^ [K : k] = 1`, the twist by the
  character `FiniteField.geometricFrobeniusCharacter` sending the geometric Frobenius to `A`:
  the finite-level Frobenius acts on `q_K^* M ≅ q_K^* M₀` through `A`. This realises characters
  of finite order of `W(k̄ / k)` (more generally finite-order automorphisms of `Λ^r`) as module
  objects on `X₀`; pulling back further along `ι : X̄ ⟶ X₀ ⊗_k K`, they become isomorphic to
  `p^* M₀` (`CondensedRing.upperStarGeometricFiberProjIsoOfFiniteLevel`).

## What remains

A bounded (not finite-order) Weil action, e.g. a unit of `ℤ_ℓ` or `ℚ̄_ℓ` of infinite order, is
not a Galois descent datum at any finite level: its reductions modulo `ℓ^k` have finite order
(`WeilConjectures.RepresentationTheory.WeilGroupBoundedExtension`) and give, by the results
here, compatible twisted module objects `M_k` at the finite levels `K_k` of degree the order
modulo `ℓ^k`; realising the action itself needs the limit over `k` (an `ℓ`-adic sheaf, i.e. a
compatible system of the `M_k` along the reductions `Λ/ℓ^{k+1} ⟶ Λ/ℓ^k`), which is not done here.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category.{v} C] [Category.{v} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {Γ : Type*} {S : Γ → D ⥤ D} {κ : ∀ σ, L ⋙ S σ ≅ L}

/-- The `galoisComparison` `L R N ⟶ ∏_σ S σ N` is an isomorphism as soon as the `galoisComponent`s
form a limit fan. -/
lemma isIso_galoisComparison_of_isLimit [HasLimitsOfShape (Discrete Γ) D] (N : D)
    (h : IsLimit (Fan.mk (L.obj (R.obj N)) fun σ ↦ adj.galoisComponent S κ σ N)) :
    IsIso (adj.galoisComparison S κ N) :=
  (Fan.nonempty_isLimit_iff_isIso_piLift _).1 ⟨h⟩

/-- **Transport of Galois components along an isomorphism of left adjoints.** Let `L, L' ⊣ R`
with `ι : L ≅ L'` compatible with the counits, and `S σ ≅ T σ`. If the composites
`θ σ : L' ⟶ L' ⋙ T σ` correspond to the inverses of `κ σ : L ⋙ S σ ≅ L` through these
isomorphisms and the morphisms `θ σ ≫ T σ (ε')` form a limit fan, then so do the Galois
components `L R N ⟶ S σ N`. -/
noncomputable def isLimitFanGaloisComponentOfIso {L' : C ⥤ D} (adj' : L' ⊣ R) (ι : L ≅ L')
    (hι : ∀ N, ι.hom.app (R.obj N) ≫ adj'.counit.app N = adj.counit.app N)
    {T : Γ → D ⥤ D} (ιS : ∀ σ, S σ ≅ T σ) (θ : ∀ σ, L' ⟶ L' ⋙ T σ)
    (hθ : ∀ σ M, (κ σ).inv.app M ≫ (S σ).map (ι.hom.app M) ≫ (ιS σ).hom.app (L'.obj M) =
      ι.hom.app M ≫ (θ σ).app M) (N : D)
    (h : IsLimit (Fan.mk (L'.obj (R.obj N)) fun σ ↦
      (θ σ).app (R.obj N) ≫ (T σ).map (adj'.counit.app N))) :
    IsLimit (Fan.mk (L.obj (R.obj N)) fun σ ↦ adj.galoisComponent S κ σ N) :=
  IsLimit.ofIsoLimit (Fan.isLimitMkCompOfIsIso h fun σ ↦ (ιS σ).inv.app N)
    (Cone.ext (ι.app (R.obj N)).symm fun ⟨σ⟩ ↦ by
      simp only [Fan.mk_pt, Fan.mk_π_app, Iso.symm_hom, Iso.app_inv, galoisComponent]
      rw [← cancel_epi (ι.hom.app (R.obj N)), Iso.hom_inv_id_app_assoc, Category.assoc,
        ← reassoc_of% (hθ σ (R.obj N)), ← (ιS σ).hom.naturality_assoc]
      simp only [Functor.id_obj, Iso.hom_inv_id_app, Category.comp_id]
      rw [← Functor.map_comp, hι])

/-- **Transport of Galois components along forgetful functors.** Let `F_X, F_Y` be functors
(e.g. forgetting module structures) with `F_X ⋙ L' ≅ L ⋙ F_Y`, `F_Y ⋙ R' ≅ R ⋙ F_X` compatible
with the counits of `L ⊣ R` and `L' ⊣ R'`, and `F_Y ⋙ S' σ ≅ S σ ⋙ F_Y` compatible with
`κ σ` and `κ' σ`. If `F_Y` reflects limits and the Galois components of `F_Y N` form a limit
fan, then so do the Galois components of `N`. -/
noncomputable def isLimitFanGaloisComponentOfForget {C' D' : Type*} [Category.{v} C']
    [Category.{v} D'] {FX : C ⥤ C'} {FY : D ⥤ D'} [ReflectsLimitsOfShape (Discrete Γ) FY]
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R') (ΦL : FX ⋙ L' ≅ L ⋙ FY)
    (ΨR : FY ⋙ R' ≅ R ⋙ FX)
    (hε : ∀ N, L'.map (ΨR.hom.app N) ≫ ΦL.hom.app (R.obj N) ≫ FY.map (adj.counit.app N) =
      adj'.counit.app (FY.obj N))
    {S' : Γ → D' ⥤ D'} {κ' : ∀ σ, L' ⋙ S' σ ≅ L'} (ΦS : ∀ σ, FY ⋙ S' σ ≅ S σ ⋙ FY)
    (hκ : ∀ σ M, ΦL.hom.app M ≫ FY.map ((κ σ).inv.app M) =
      (κ' σ).inv.app (FX.obj M) ≫ (S' σ).map (ΦL.hom.app M) ≫ (ΦS σ).hom.app (L.obj M))
    (N : D) (h : IsLimit (Fan.mk (L'.obj (R'.obj (FY.obj N))) fun σ ↦
      adj'.galoisComponent S' κ' σ (FY.obj N))) :
    IsLimit (Fan.mk (L.obj (R.obj N)) fun σ ↦ adj.galoisComponent S κ σ N) := by
  let e : L'.obj (R'.obj (FY.obj N)) ≅ FY.obj (L.obj (R.obj N)) :=
    L'.mapIso (ΨR.app N) ≪≫ ΦL.app (R.obj N)
  have he (σ : Γ) : e.hom ≫ FY.map (adj.galoisComponent S κ σ N) =
      adj'.galoisComponent S' κ' σ (FY.obj N) ≫ (ΦS σ).hom.app N := by
    have hκ' : L'.map (ΨR.hom.app N) ≫ (κ' σ).inv.app (FX.obj (R.obj N)) =
        (κ' σ).inv.app (R'.obj (FY.obj N)) ≫ (S' σ).map (L'.map (ΨR.hom.app N)) :=
      (κ' σ).inv.naturality (ΨR.hom.app N)
    have hS : (ΦS σ).hom.app (L.obj (R.obj N)) ≫ FY.map ((S σ).map (adj.counit.app N)) =
        (S' σ).map (FY.map (adj.counit.app N)) ≫ (ΦS σ).hom.app N :=
      ((ΦS σ).hom.naturality (adj.counit.app N)).symm
    simp only [e, galoisComponent, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hκ σ (R.obj N)), hS, reassoc_of% hκ', ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, Category.assoc, hε]
  refine Fan.isLimitOfIsLimitMapComp FY _ (fun σ ↦ e.inv ≫ adj'.galoisComponent S' κ' σ (FY.obj N))
    (IsLimit.ofIsoLimit h (Cone.ext e fun ⟨σ⟩ ↦ ?_)) (fun σ ↦ (ΦS σ).hom.app N) fun σ ↦ ?_
  · simp only [Fan.mk_pt, Fan.mk_π_app, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (q : Y ⟶ X) {Γ : Type u} (ρ : Γ → (Y ⟶ Y))

/-- An action `ρ` of `Γ` on a scheme `Y` is *free* if two distinct elements never agree on a
nonempty scheme: `t ≫ ρ σ = t ≫ ρ τ` for `t : T ⟶ Y` with `T` nonempty forces `σ = τ`
(the graphs of the `ρ σ` are pairwise disjoint). -/
def IsFreeAction : Prop :=
  ∀ σ τ (T : Scheme.{u}) (t : T ⟶ Y), t ≫ ρ σ = t ≫ ρ τ → Nonempty T → σ = τ

variable {q ρ} (hρ : ∀ σ, ρ σ ≫ q = q)

/-- **The base change of a free Galois covering is trivial.** For a free Galois action `ρ` on
`q : Y ⟶ X` and `w : W ⟶ Y`, the graphs `(𝟙, w ≫ ρ σ) : W ⟶ W ×_X Y` exhibit `W ×_X Y` as the
disjoint union of copies of `W`. -/
theorem nonempty_isColimit_cofan_pullbackLift (hgal : IsGaloisAction q ρ)
    (hfree : IsFreeAction ρ) {W : Scheme.{u}} (w : W ⟶ Y) :
    Nonempty (IsColimit (Cofan.mk (pullback (w ≫ q) q) fun σ ↦
      pullback.lift (𝟙 W) (w ≫ ρ σ) (by simp [hρ]))) := by
  set f : ∀ σ, W ⟶ pullback (w ≫ q) q := fun σ ↦ pullback.lift (𝟙 W) (w ≫ ρ σ) (by simp [hρ])
  obtain ⟨U, hU, hUρ⟩ := hgal _ (pullback.fst (w ≫ q) q ≫ w) (pullback.snd (w ≫ q) q)
    (by rw [Category.assoc, pullback.condition])
  have hfst (σ : Γ) : f σ ≫ pullback.fst _ _ = 𝟙 W := pullback.lift_fst _ _ _
  have hUf (σ : Γ) : (U σ).ι ≫ pullback.fst _ _ ≫ f σ = (U σ).ι := by
    refine pullback.hom_ext ?_ ?_
    · simp [f]
    · simp [f, hUρ σ]
  have hsub (σ : Γ) : ((U σ) : Set _) ⊆ Set.range (f σ) := fun x hx ↦ by
    refine ⟨pullback.fst (w ≫ q) q ((U σ).ι ⟨x, hx⟩), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hUf]
    rfl
  have hdisj (σ τ : Γ) (hστ : σ ≠ τ) : Disjoint (Set.range (f σ)) (Set.range (f τ)) := by
    rw [← Scheme.isEmpty_pullback_iff]
    refine ⟨fun z ↦ hστ (hfree σ τ _ (pullback.fst (f σ) (f τ) ≫ w) ?_ ⟨z⟩)⟩
    have h₁ := congrArg (· ≫ pullback.fst (w ≫ q) q) (pullback.condition (f := f σ) (g := f τ))
    have h₂ := congrArg (· ≫ pullback.snd (w ≫ q) q) (pullback.condition (f := f σ) (g := f τ))
    simp only [Category.assoc, hfst, Category.comp_id, f, pullback.lift_snd] at h₁ h₂
    rw [Category.assoc, Category.assoc, h₂, h₁]
  have hrange (σ : Γ) : Set.range (f σ) = U σ := by
    refine subset_antisymm (fun x hx ↦ ?_) (hsub σ)
    obtain ⟨τ, hτ⟩ := hU x
    obtain rfl : σ = τ := by
      by_contra hστ
      exact Set.disjoint_left.mp (hdisj σ τ hστ) hx (hsub τ hτ)
    exact hτ
  have hopen (σ : Γ) : IsOpenImmersion (f σ) := by
    let g := IsOpenImmersion.lift (U σ).ι (f σ) (by rw [Scheme.Opens.range_ι, hrange])
    have hg : g ≫ (U σ).ι = f σ := IsOpenImmersion.lift_fac _ _ _
    have : IsIso g := ⟨⟨(U σ).ι ≫ pullback.fst _ _, by rw [reassoc_of% hg, hfst], by
      rw [← cancel_mono (U σ).ι, Category.assoc, Category.assoc, hg, hUf, Category.id_comp]⟩⟩
    rw [← hg]
    infer_instance
  refine nonempty_isColimit_cofanMk_of f ?_ fun σ τ hστ ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨τ, hτ⟩ := hU x
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨τ, ?_⟩
    rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange, hrange]
    exact hτ
  · rw [Function.onFun, disjoint_iff, eq_bot_iff]
    intro x hx
    exact (Set.disjoint_left.mp (hdisj σ τ hστ) hx.1 hx.2).elim

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme Opposite

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}} (q : Y ⟶ X) [WeaklyEtale q] (s : Y ⟶ Y) [WeaklyEtale s]
  (hs : s ≫ q = q)

/-- The graph `(𝟙, w ≫ s) : W ⟶ W ×_X Y` of an endomorphism `s` of `Y` over `X`, as a morphism
`(W, w ≫ s) ⟶ (W ×_X Y, pr₂)` of the pro-étale site of `Y`, for `w : W ⟶ Y`. -/
noncomputable def graphHom (W : Y.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale s)).obj W ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ q).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale q)).obj W) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 W.left) (W.hom ≫ s) ((Category.id_comp _).trans
      ((congrArg (W.hom ≫ ·) hs.symm).trans (Category.assoc _ _ _).symm)))
    (by simp) trivial

/-- The Galois component `j_q^* q_* G ⟶ j_s^* G` in the model of the pullbacks along weakly
étale morphisms by restriction: the identification `j_q^* ≅ j_s^* j_q^*` (as `s ≫ q = q`)
followed by `j_s^*` of the counit. -/
noncomputable def galoisComponentRestriction (G : Sheaf (ProEt.topology Y) A) :
    (localizationRestriction A q inferInstance).obj ((q)_*[A].obj G) ⟶
      (localizationRestriction A s inferInstance).obj G :=
  (localizationRestrictionComp A s q inferInstance inferInstance q hs.symm inferInstance).hom.app
      ((q)_*[A].obj G) ≫
    (localizationRestriction A s inferInstance).map
      ((localizationRestrictionLowerStarAdjunction A q inferInstance).counit.app G)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- On sections over `W ⟶ Y`, the Galois component in the restriction model is the restriction
along the graph `(𝟙, w ≫ s) : W ⟶ W ×_X Y`. -/
lemma galoisComponentRestriction_hom_app (G : Sheaf (ProEt.topology Y) A) (W : Y.ProEt) :
    (galoisComponentRestriction A q s hs G).hom.app (op W) =
      G.obj.map (graphHom q s hs W).op := by
  simp only [localizationRestriction, lowerStar, galoisComponentRestriction, Functor.comp_obj,
    localizationRestrictionComp, Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso, Iso.symm_inv,
    Iso.symm_hom, Iso.refl_trans, Iso.symm_mk, localizationRestrictionLowerStarAdjunction,
    MorphismProperty.Over.mapPullbackAdj, Functor.id_obj, Functor.const_obj_obj,
    ObjectProperty.FullSubcategory.comp_hom, Functor.sheafPushforwardContinuousNatTrans_app_hom,
    ObjectProperty.ι_obj, NatTrans.comp_app, Functor.whiskerRight_app, Functor.op_obj,
    NatTrans.op_app, Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    Functor.sheafPushforwardContinuous_map_hom_app,
    Adjunction.sheafPushforwardContinuous_counit_app_hom_app, MorphismProperty.Over.map_obj_hom,
    ← Functor.map_comp, ← op_comp]
  congr 2
  refine MorphismProperty.Over.Hom.ext ?_
  apply pullback.hom_ext
  · simp only [graphHom, MorphismProperty.Comma.comp_hom, MorphismProperty.Over.homMk_hom,
      Comma.comp_left, Over.homMk_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.mapComp_inv_app_left, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left]
    exact Category.id_comp _
  · simp [graphHom]

variable {Γ : Type u} [Finite Γ] {ρ : Γ → (Y ⟶ Y)} [∀ σ, WeaklyEtale (ρ σ)]
  (hρ : ∀ σ, ρ σ ≫ q = q)

/-- **Sections of a pushforward along a free Galois covering**, restriction model: for a free
Galois action `ρ` of a finite `Γ` on `q : Y ⟶ X`, the Galois components
`j_q^* q_* G ⟶ j_{ρ σ}^* G` form a limit fan. On sections over `w : W ⟶ Y` they are the
restrictions along the graphs `W ⟶ W ×_X Y`, which exhibit `W ×_X Y` as a disjoint union of
copies of `W` (`AlgebraicGeometry.ProEtale.nonempty_isColimit_cofan_pullbackLift`). -/
noncomputable def isLimitFanGaloisComponentRestriction (hgal : IsGaloisAction q ρ)
    (hfree : IsFreeAction ρ) (G : Sheaf (ProEt.topology Y) A) :
    IsLimit (Fan.mk ((localizationRestriction A q inferInstance).obj ((q)_*[A].obj G))
      fun σ ↦ galoisComponentRestriction A q (ρ σ) (hρ σ) G) := by
  apply isLimitOfReflects (sheafToPresheaf _ A)
  refine (isLimitMapConeFanMkEquiv (sheafToPresheaf _ A) _ _).symm ?_
  apply evaluationJointlyReflectsLimits
  intro W
  refine (isLimitMapConeFanMkEquiv ((evaluation _ A).obj W) _ _).symm ?_
  refine IsLimit.ofIsoLimit (isLimitSectionsFanOfIsColimitCofan G
    (fun σ ↦ graphHom q (ρ σ) (hρ σ) W.unop)
    (nonempty_isColimit_cofan_pullbackLift hρ hgal hfree W.unop.hom).some)
    (Cone.ext (Iso.refl _) fun ⟨σ⟩ ↦ ?_)
  exact ((Category.id_comp _).trans
    (galoisComponentRestriction_hom_app A q (ρ σ) (hρ σ) G W.unop)).symm


omit [Finite Γ] [∀ σ, WeaklyEtale (ρ σ)] in
/-- The composition isomorphism `q^* = (s ≫ q)^* ≅ s^* q^*` is, through the identifications of
the pullbacks along weakly étale morphisms with restrictions, the composition isomorphism
`j_q^* ≅ j_s^* j_q^*` of restrictions. -/
lemma upperStarComp'_hom_app_map_upperStarIsoLocalizationRestriction
    (M : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    (upperStarComp' Ab.{u + 1} s q q hs.symm).symm.inv.app M ≫
        (s)^*[Ab.{u + 1}].map
          ((upperStarIsoLocalizationRestriction Ab.{u + 1} q inferInstance).hom.app M) ≫
        (upperStarIsoLocalizationRestriction Ab.{u + 1} s inferInstance).hom.app
          ((localizationRestriction Ab.{u + 1} q inferInstance).obj M) =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} q inferInstance).hom.app M ≫
        (localizationRestrictionComp Ab.{u + 1} s q inferInstance inferInstance q hs.symm
          inferInstance).hom.app M :=
  NatTrans.congr_app (upperStarComp'_hom_comp_upperStarIsoLocalizationRestriction
    Ab.{u + 1} s q inferInstance inferInstance q hs.symm inferInstance) M

/-- **Sections of a pushforward along a free Galois covering**: for a free Galois action `ρ` of a
finite `Γ` on `q : Y ⟶ X` by weakly étale endomorphisms over `X`, the Galois components
`q^* q_* G ⟶ (ρ σ)^* G` of abelian sheaves form a limit fan, i.e. `q^* q_* G ≅ ∏_σ (ρ σ)^* G`. -/
noncomputable def isLimitFanUpperStarGaloisComponent (hgal : IsGaloisAction q ρ)
    (hfree : IsFreeAction ρ) (G : Sheaf (ProEt.topology Y) Ab.{u + 1}) :
    IsLimit (Fan.mk ((q)^*[Ab.{u + 1}].obj ((q)_*[Ab.{u + 1}].obj G)) fun σ ↦
      (upperStarLowerStarAdjunction Ab.{u + 1} q).galoisComponent (fun σ ↦ (ρ σ)^*[Ab.{u + 1}])
        (fun σ ↦ (upperStarComp' Ab.{u + 1} (ρ σ) q q (hρ σ).symm).symm) σ G) :=
  (upperStarLowerStarAdjunction Ab.{u + 1} q).isLimitFanGaloisComponentOfIso
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} q inferInstance)
    (upperStarIsoLocalizationRestriction Ab.{u + 1} q inferInstance)
    (fun N ↦ Adjunction.leftAdjointUniq_hom_app_counit _ _ N)
    (fun σ ↦ upperStarIsoLocalizationRestriction Ab.{u + 1} (ρ σ) inferInstance)
    (fun σ ↦ (localizationRestrictionComp Ab.{u + 1} (ρ σ) q inferInstance inferInstance q
      (hρ σ).symm inferInstance).hom)
    (fun σ M ↦ upperStarComp'_hom_app_map_upperStarIsoLocalizationRestriction q (ρ σ) (hρ σ) M)
    G (isLimitFanGaloisComponentRestriction Ab.{u + 1} q hρ hgal hfree G)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}}

/-- The identifications `upperStarForgetIso` are compatible with the transport of pullbacks along
equal morphisms. -/
lemma upperStarForgetIso_hom_app_map_upperStarCongr_inv_app {f g : Y ⟶ X} (h : f = g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarForgetIso Λ g).hom.app M ≫ (Mod.forget _).map ((upperStarCongr Λ h).inv.app M) =
      (ProEtale.upperStarCongr Ab.{u + 1} h.symm).hom.app ((Mod.forget _).obj M) ≫
        (upperStarForgetIso Λ f).hom.app M := by
  subst h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable (q : Y ⟶ X) {s : Y ⟶ Y} (hs : s ≫ q = q)

/-- The identifications `upperStarForgetIso` are compatible with the canonical isomorphisms
`s^* q^* ≅ (s ≫ q)^* = q^*` for `s ≫ q = q`. -/
lemma upperStarForgetIso_hom_app_map_upperStarComp_symm_trans_inv_app
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarForgetIso Λ q).hom.app M ≫
        (Mod.forget _).map (((upperStarComp Λ s q).symm ≪≫ upperStarCongr Λ hs).inv.app M) =
      (ProEtale.upperStarComp' Ab.{u + 1} s q q hs.symm).symm.inv.app ((Mod.forget _).obj M) ≫
        (s)^*[Ab.{u + 1}].map ((upperStarForgetIso Λ q).hom.app M) ≫
        (upperStarForgetIso Λ s).hom.app ((q)^*⟦Λ⟧.obj M) := by
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    ProEtale.upperStarComp', Iso.trans_hom]
  rw [reassoc_of% (upperStarForgetIso_hom_app_map_upperStarCongr_inv_app Λ hs M),
    upperStarComp_hom_app_upperStarForgetIso]

variable {q} {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ σ, ρ σ ≫ q = q)

/-- **The Galois comparison of a free Galois covering is an isomorphism.** For a free Galois
action `ρ` of a finite `Γ` by weakly étale endomorphisms of `Y` over `X`, with `q : Y ⟶ X`
weakly étale, the comparison `q^* q_* N ⟶ ∏_σ (ρ σ)^* N` of module objects over `Λ` is an
isomorphism: on underlying sheaves and on sections over `w : W ⟶ Y`, it is the restriction
`N(W ×_X Y) ⟶ ∏_σ N(W)` along the graphs of the `w ≫ ρ σ`, which form a disjoint open covering
(`AlgebraicGeometry.ProEtale.nonempty_isColimit_cofan_pullbackLift`). -/
theorem isIso_galoisComparison [Finite Γ] [∀ σ, WeaklyEtale (ρ σ)] [WeaklyEtale q]
    (hgal : IsGaloisAction q ρ) (hfree : IsFreeAction ρ)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsIso (galoisComparison Λ q ρ hρ N) :=
  (upperStarLowerStarAdjunction Λ q).isIso_galoisComparison_of_isLimit N
    ((upperStarLowerStarAdjunction Λ q).isLimitFanGaloisComponentOfForget
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} q) (upperStarForgetIso Λ q)
      (lowerStarForgetIso Λ q) (forget_map_upperStarLowerStarAdjunction_counit_app Λ q)
      (fun σ ↦ upperStarForgetIso Λ (ρ σ))
      (fun σ M ↦ upperStarForgetIso_hom_app_map_upperStarComp_symm_trans_inv_app Λ q (hρ σ) M)
      N (ProEtale.isLimitFanUpperStarGaloisComponent q hρ hgal hfree ((Mod.forget _).obj N)))

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### The finite levels -/

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  {K : Type u} [Field K] [Algebra k K]

/-- The Galois action on `X₀ ⊗_k K` is unital. -/
lemma finiteLevelGaloisMap_one : f.finiteLevelGaloisMap (1 : Gal(K/k)) = 𝟙 _ := by
  have h : CommRingCat.ofHom ((1 : Gal(K/k)) : K →+* K) = 𝟙 _ := by
    ext
    rfl
  refine f.finiteLevel_hom_ext K ?_ ?_
  · simp
  · simp [h]

/-- The Galois action on `X₀ ⊗_k K` is by automorphisms. -/
instance isIso_finiteLevelGaloisMap (σ : Gal(K/k)) : IsIso (f.finiteLevelGaloisMap σ) :=
  ⟨f.finiteLevelGaloisMap σ⁻¹, by rw [finiteLevelGaloisMap_comp, mul_inv_cancel,
    finiteLevelGaloisMap_one], by rw [finiteLevelGaloisMap_comp, inv_mul_cancel,
    finiteLevelGaloisMap_one]⟩

/-- The action `σ ↦ 𝟙 × Spec (χ σ)` on `X₀ ⊗_k K` of a monoid `Γ` through `χ : Γ ≃* Gal(K / k)`. -/
noncomputable def finiteLevelGaloisAction {Γ : Type*} [Monoid Γ] (χ : Γ ≃* Gal(K/k)) (σ : Γ) :
    f.finiteLevel K ⟶ f.finiteLevel K :=
  f.finiteLevelGaloisMap (χ σ)

instance isIso_finiteLevelGaloisAction {Γ : Type*} [Monoid Γ] (χ : Γ ≃* Gal(K/k)) (σ : Γ) :
    IsIso (f.finiteLevelGaloisAction χ σ) :=
  isIso_finiteLevelGaloisMap f (χ σ)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  {K : Type u} [Field K] [Algebra k K]

/-- **The Galois action on a finite level is free**: if `t ≫ (𝟙 × Spec σ) = t ≫ (𝟙 × Spec τ)` for
`t : T ⟶ X₀ ⊗_k K` with `T` nonempty, then `σ = τ`, since the ring homomorphism
`K ⟶ Γ(T, 𝒪_T)` induced by `t` is injective. -/
theorem isFreeAction_finiteLevelGaloisMap :
    IsFreeAction (f.finiteLevelGaloisMap (K := K)) := by
  intro σ τ T t h ⟨x⟩
  have h' : (t ≫ f.finiteLevelToSpec K) ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K)) =
      (t ≫ f.finiteLevelToSpec K) ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K)) := by
    rw [Category.assoc, Category.assoc,
      ← Scheme.Hom.finiteLevelGaloisMap_comp_finiteLevelToSpec,
      ← Scheme.Hom.finiteLevelGaloisMap_comp_finiteLevelToSpec, reassoc_of% h]
  have h'' := congrArg
    (fun c ↦ ((Scheme.ΓSpecIso (.of K)).inv ≫ Scheme.Hom.appTop c).hom) h'
  simp only [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h''
  have : Nonempty (⊤ : T.Opens) := ⟨⟨x, trivial⟩⟩
  refine AlgEquiv.ext fun y ↦ RingHom.injective
    ((Scheme.ΓSpecIso (.of K)).inv ≫ Scheme.Hom.appTop (t ≫ f.finiteLevelToSpec K)).hom ?_
  exact RingHom.congr_fun h'' y

/-- **The finite levels are Galois coverings**: for a finite Galois extension `K / k`, the action
`σ ↦ 𝟙 × Spec σ` of `Gal(K / k)` on `q_K : X₀ ⊗_k K ⟶ X₀` is Galois. -/
theorem isGaloisAction_finiteLevelGaloisMap [FiniteDimensional k K] [IsGalois k K] :
    IsGaloisAction (f.finiteLevelProj K) (f.finiteLevelGaloisMap (K := K)) :=
  IsGaloisAction.pullback_of_comp_eq f
    (isGaloisAction_spec_map _ (fun σ : Gal(K/k) ↦ σ) (fun _ ↦ rfl) Function.surjective_id) _
    (fun σ ↦ f.finiteLevelGaloisMap_comp_finiteLevelProj σ)
    fun σ ↦ f.finiteLevelGaloisMap_comp_finiteLevelToSpec σ

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (K) [FiniteDimensional k K] [IsGalois k K]

/-- **The Galois comparison at a finite level is an isomorphism**: for a finite Galois extension
`K / k`, the comparison `q_K^* q_{K*} N ⟶ ∏_σ (𝟙 × Spec σ)^* N` of module objects on `X₀ ⊗_k K`
is an isomorphism. -/
theorem isIso_galoisComparison_finiteLevelProj
    (N : Mod (Sheaf (Scheme.ProEt.topology (f.finiteLevel K)) Ab.{u + 1})
      (condensedRingObj Λ (f.finiteLevel K))) :
    IsIso (galoisComparison Λ (f.finiteLevelProj K) (f.finiteLevelGaloisMap (K := K))
      f.finiteLevelGaloisMap_comp_finiteLevelProj N) :=
  isIso_galoisComparison Λ _ (isGaloisAction_finiteLevelGaloisMap f)
    (isFreeAction_finiteLevelGaloisMap f) N

variable {Γ : Type u} [Monoid Γ] [Finite Γ] (χ : Γ ≃* Gal(K/k))

omit [FiniteDimensional k K] [IsGalois k K] [Finite Γ] in
lemma finiteLevelGaloisAction_one : f.finiteLevelGaloisAction χ 1 = 𝟙 _ := by
  rw [Scheme.Hom.finiteLevelGaloisAction, map_one, Scheme.Hom.finiteLevelGaloisMap_one]

omit [FiniteDimensional k K] [IsGalois k K] [Finite Γ] in
lemma finiteLevelGaloisAction_mul (σ τ : Γ) :
    f.finiteLevelGaloisAction χ (σ * τ) =
      f.finiteLevelGaloisAction χ σ ≫ f.finiteLevelGaloisAction χ τ := by
  rw [Scheme.Hom.finiteLevelGaloisAction, Scheme.Hom.finiteLevelGaloisAction,
    Scheme.Hom.finiteLevelGaloisAction, map_mul, Scheme.Hom.finiteLevelGaloisMap_comp]

omit [FiniteDimensional k K] [IsGalois k K] [Finite Γ] in
lemma finiteLevelGaloisAction_comp_finiteLevelProj (σ : Γ) :
    f.finiteLevelGaloisAction χ σ ≫ f.finiteLevelProj K = f.finiteLevelProj K :=
  f.finiteLevelGaloisMap_comp_finiteLevelProj (χ σ)

omit [Finite Γ] in
/-- The action of `Γ ≃* Gal(K / k)` on the finite level `X₀ ⊗_k K` is Galois. -/
theorem isGaloisAction_finiteLevelGaloisAction :
    IsGaloisAction (f.finiteLevelProj K) (f.finiteLevelGaloisAction χ) :=
  IsGaloisAction.pullback_of_comp_eq f (isGaloisAction_spec_map _ (fun σ ↦ χ σ) (fun _ ↦ rfl)
    χ.surjective) _ (fun σ ↦ f.finiteLevelGaloisMap_comp_finiteLevelProj (χ σ))
    fun σ ↦ f.finiteLevelGaloisMap_comp_finiteLevelToSpec (χ σ)

omit [FiniteDimensional k K] [IsGalois k K] [Finite Γ] in
/-- The action of `Γ ≃* Gal(K / k)` on the finite level `X₀ ⊗_k K` is free. -/
theorem isFreeAction_finiteLevelGaloisAction : IsFreeAction (f.finiteLevelGaloisAction χ) :=
  fun σ τ T t h hT ↦ χ.injective (isFreeAction_finiteLevelGaloisMap f (χ σ) (χ τ) T t h hT)

/-- **Effective Galois descent of module objects at a finite level.** Let `K / k` be a finite
Galois extension and `χ : Γ ≃* Gal(K / k)`. A Galois descent datum
`ψ σ : N ⟶ (𝟙 × Spec (χ σ))^* N` (`σ ∈ Γ`) on a module object `N` on `X₀ ⊗_k K` is effective:
`N ≅ q_K^* M` for a module object `M` on `X₀`, compatibly with the canonical descent datum of
`q_K^* M`. This is
`AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_obj_iso_of_galoisDescentDatum`, whose
hypotheses on the Galois comparison hold by
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_galoisComparison`. -/
theorem exists_upperStar_finiteLevelProj_obj_iso_of_galoisDescentDatum
    (N : Mod (Sheaf (Scheme.ProEt.topology (f.finiteLevel K)) Ab.{u + 1})
      (condensedRingObj Λ (f.finiteLevel K)))
    (ψ : ∀ σ : Γ, N ⟶ (f.finiteLevelGaloisAction χ σ)^*⟦Λ⟧.obj N)
    (hψ₁ : ψ 1 ≫ (upperStarCongr Λ (finiteLevelGaloisAction_one f K χ)).hom.app N ≫
      (upperStarId Λ _).hom.app N = 𝟙 N)
    (hψ : ∀ σ τ, ψ σ ≫ (f.finiteLevelGaloisAction χ σ)^*⟦Λ⟧.map (ψ τ) =
      ψ (σ * τ) ≫ (upperStarCongr Λ (finiteLevelGaloisAction_mul f K χ σ τ)).hom.app N ≫
        (upperStarComp Λ (f.finiteLevelGaloisAction χ σ)
          (f.finiteLevelGaloisAction χ τ)).hom.app N) :
    ∃ (M : Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀))
      (e : (f.finiteLevelProj K)^*⟦Λ⟧.obj M ≅ N), ∀ σ, e.hom ≫ ψ σ =
        ((upperStarCongr Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K χ σ)).inv.app M ≫
          (upperStarComp Λ (f.finiteLevelGaloisAction χ σ) (f.finiteLevelProj K)).hom.app M) ≫
          (f.finiteLevelGaloisAction χ σ)^*⟦Λ⟧.map e.hom :=
  have := isIso_galoisComparison Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K χ)
    (isGaloisAction_finiteLevelGaloisAction f K χ) (isFreeAction_finiteLevelGaloisAction f K χ) N
  have := isIso_galoisComparison Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K χ)
    (isGaloisAction_finiteLevelGaloisAction f K χ) (isFreeAction_finiteLevelGaloisAction f K χ)
    ((f.finiteLevelProj K)^*⟦Λ⟧.obj ((f.finiteLevelProj K)_*⟦Λ⟧.obj N))
  exists_upperStar_obj_iso_of_galoisDescentDatum Λ (f.finiteLevelProj K)
    (f.finiteLevelGaloisAction χ) (finiteLevelGaloisAction_comp_finiteLevelProj f K χ)
    (finiteLevelGaloisAction_one f K χ) (finiteLevelGaloisAction_mul f K χ) N ψ hψ₁ hψ

end CondensedRing

end AlgebraicGeometry.ProEtale

/-! ### Twisted constant module objects -/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category.{v} C] [Category.{v} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {Γ : Type*} [Monoid Γ] {S : Γ → D ⥤ D} {κ : ∀ σ, L ⋙ S σ ≅ L} {ε₀ : S 1 ≅ 𝟭 D}
  {μ : ∀ σ τ, S (σ * τ) ≅ S τ ⋙ S σ}

omit adj in
/-- **Twisting the canonical descent datum.** If the isomorphisms `κ σ : L ⋙ S σ ≅ L` are
unital and multiplicative (for instance the canonical isomorphisms `σ^* q^* ≅ q^*`), then for an
anti-homomorphism `a : Γ →* (Aut M₀)ᵐᵒᵖ` the morphisms `L (a σ) ≫ (κ σ)⁻¹ : L M₀ ⟶ S σ (L M₀)`
form a Galois descent datum on `L M₀`: the canonical datum twisted by `a`. -/
lemma isGaloisDescentDatum_map_comp_inv_app
    (hκ₁ : ∀ M, (κ 1).hom.app M = ε₀.hom.app (L.obj M))
    (hκ : ∀ σ τ M, (κ (σ * τ)).hom.app M =
      (μ σ τ).hom.app (L.obj M) ≫ (S σ).map ((κ τ).hom.app M) ≫ (κ σ).hom.app M)
    {M₀ : C} (a : Γ →* (Aut M₀)ᵐᵒᵖ) :
    IsGaloisDescentDatum S ε₀ μ fun σ ↦ L.map (a σ).unop.asIso.hom ≫ (κ σ).inv.app M₀ where
  one := by
    rw [map_one, MulOpposite.unop_one, Category.assoc, ← hκ₁, Iso.inv_hom_id_app]
    exact (Category.comp_id _).trans (L.map_id M₀)
  mul σ τ := by
    have hn : (κ σ).inv.app M₀ ≫ (S σ).map (L.map (a τ).unop.asIso.hom) =
        L.map (a τ).unop.asIso.hom ≫ (κ σ).inv.app M₀ :=
      ((κ σ).inv.naturality (a τ).unop.asIso.hom).symm
    rw [Functor.map_comp, Category.assoc, reassoc_of% hn,
      inv_app_comp_map_inv_app hκ σ τ M₀, map_mul, MulOpposite.unop_mul, Aut.mul_asIso,
      Iso.trans_hom, Functor.map_comp, Category.assoc, Category.assoc]

/-- **Twisted objects.** Let `L ⊣ R` with `L` faithful and left exact out of an abelian category,
`κ σ : L ⋙ S σ ≅ L` unital and multiplicative, and assume the Galois comparisons of `L M₀` and
`L R L M₀` are isomorphisms. Then every anti-homomorphism `a : Γ →* (Aut M₀)ᵐᵒᵖ` defines an
object `M` with `L M ≅ L M₀`, the canonical descent datum of `L M` corresponding to the one of
`L M₀` twisted by `a`. -/
theorem exists_iso_twist [Abelian C] [L.Faithful] [PreservesFiniteLimits L]
    [HasLimitsOfShape (Discrete Γ) D] [∀ σ, PreservesLimitsOfShape (Discrete Γ) (S σ)]
    (hκ₁ : ∀ M, (κ 1).hom.app M = ε₀.hom.app (L.obj M))
    (hκ : ∀ σ τ M, (κ (σ * τ)).hom.app M =
      (μ σ τ).hom.app (L.obj M) ≫ (S σ).map ((κ τ).hom.app M) ≫ (κ σ).hom.app M)
    (M₀ : C) [IsIso (adj.galoisComparison S κ (L.obj M₀))]
    [IsIso (adj.galoisComparison S κ (L.obj (R.obj (L.obj M₀))))] (a : Γ →* (Aut M₀)ᵐᵒᵖ) :
    ∃ (M : C) (e : L.obj M ≅ L.obj M₀), ∀ σ,
      e.hom ≫ L.map (a σ).unop.asIso.hom ≫ (κ σ).inv.app M₀ = (κ σ).inv.app M ≫ (S σ).map e.hom :=
  adj.exists_iso_of_isGaloisDescentDatum hκ₁ hκ (L.obj M₀)
    (isGaloisDescentDatum_map_comp_inv_app hκ₁ hκ a)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Generic

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (q : Y ⟶ X) [WeaklyEtale q] {Γ : Type*} [Monoid Γ] (ρ : Γ → (Y ⟶ Y))
  (hρ : ∀ σ, ρ σ ≫ q = q)

/-- **Twisted module objects**, conditional form. Let `q : Y ⟶ X` be a quasi-compact surjective
weakly étale morphism with an action `ρ` of a finite monoid `Γ` over `X` whose Galois
comparisons at `q^* M₀` and `q^* q_* q^* M₀` are isomorphisms, and `a : Γ →* (Aut M₀)ᵐᵒᵖ`.
Then there is a module object `M` on `X` with `q^* M ≅ q^* M₀`, through which the canonical
descent datum `q^* M ⟶ (ρ σ)^* q^* M` corresponds to the canonical one of `q^* M₀` twisted by
`a σ`. -/
theorem exists_upperStar_obj_iso_twist [Surjective q] [QuasiCompact q] [Finite Γ]
    (hρ₁ : ρ 1 = 𝟙 Y) (hρmul : ∀ σ τ, ρ (σ * τ) = ρ σ ≫ ρ τ)
    (M₀ : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    [IsIso (galoisComparison Λ q ρ hρ ((q)^*⟦Λ⟧.obj M₀))]
    [IsIso (galoisComparison Λ q ρ hρ ((q)^*⟦Λ⟧.obj ((q)_*⟦Λ⟧.obj ((q)^*⟦Λ⟧.obj M₀))))]
    (a : Γ →* (Aut M₀)ᵐᵒᵖ) :
    ∃ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (e : (q)^*⟦Λ⟧.obj M ≅ (q)^*⟦Λ⟧.obj M₀), ∀ σ,
      e.hom ≫ (q)^*⟦Λ⟧.map (a σ).unop.asIso.hom ≫
          ((upperStarCongr Λ (hρ σ)).inv.app M₀ ≫ (upperStarComp Λ (ρ σ) q).hom.app M₀) =
        ((upperStarCongr Λ (hρ σ)).inv.app M ≫ (upperStarComp Λ (ρ σ) q).hom.app M) ≫
          (ρ σ)^*⟦Λ⟧.map e.hom := by
  have := Fintype.ofFinite Γ
  classical
  obtain ⟨M, e, he⟩ := (upperStarLowerStarAdjunction Λ q).exists_iso_twist
    (S := fun σ ↦ (ρ σ)^*⟦Λ⟧)
    (κ := fun σ ↦ (upperStarComp Λ (ρ σ) q).symm ≪≫ upperStarCongr Λ (hρ σ))
    (ε₀ := upperStarCongr Λ hρ₁ ≪≫ upperStarId Λ Y)
    (μ := fun σ τ ↦ upperStarCongr Λ (hρmul σ τ) ≪≫ upperStarComp Λ (ρ σ) (ρ τ))
    (fun M ↦ by
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
      exact upperStarComp_inv_app_upperStarCongr_hom_app_of_eq_id Λ q (hρ 1) hρ₁ M)
    (fun σ τ M ↦ by
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
      exact upperStarComp_inv_app_upperStarCongr_hom_app_of_eq_comp Λ q (hρ σ) (hρ τ)
        (hρ (σ * τ)) (hρmul σ τ) M)
    M₀ a
  exact ⟨M, e, fun σ ↦ by simpa only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app] using he σ⟩

end Generic

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k)) (K : Type u) [Field K]
  [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {Γ : Type u} [Monoid Γ] [Finite Γ] (χ : Γ ≃* Gal(K/k))

/-- **Twisted module objects at a finite level.** Let `K / k` be a finite Galois extension,
`χ : Γ ≃* Gal(K / k)`, `M₀` a module object on `X₀` and `a : Γ →* (Aut M₀)ᵐᵒᵖ` (e.g. the powers
of an automorphism of finite order dividing `[K : k]` for a cyclic `Γ`). There is a module object
`M` on `X₀` with `q_K^* M ≅ q_K^* M₀`, through which the canonical descent datum
`q_K^* M ⟶ (𝟙 × Spec (χ σ))^* q_K^* M` corresponds to the canonical one of `q_K^* M₀` twisted
by `a σ`. For `M₀` constant (e.g. `Λ_{X₀}^r`) this is the twist of `M₀` by `a`. -/
theorem exists_upperStar_finiteLevelProj_obj_iso_twist
    (M₀ : Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀))
    (a : Γ →* (Aut M₀)ᵐᵒᵖ) :
    ∃ (M : Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀))
      (e : (f.finiteLevelProj K)^*⟦Λ⟧.obj M ≅ (f.finiteLevelProj K)^*⟦Λ⟧.obj M₀), ∀ σ,
      e.hom ≫ (f.finiteLevelProj K)^*⟦Λ⟧.map (a σ).unop.asIso.hom ≫
          ((upperStarCongr Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K χ σ)).inv.app M₀ ≫
            (upperStarComp Λ (f.finiteLevelGaloisAction χ σ) (f.finiteLevelProj K)).hom.app M₀) =
        ((upperStarCongr Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K χ σ)).inv.app M ≫
          (upperStarComp Λ (f.finiteLevelGaloisAction χ σ) (f.finiteLevelProj K)).hom.app M) ≫
          (f.finiteLevelGaloisAction χ σ)^*⟦Λ⟧.map e.hom :=
  have := isIso_galoisComparison Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K χ)
    (isGaloisAction_finiteLevelGaloisAction f K χ) (isFreeAction_finiteLevelGaloisAction f K χ)
    ((f.finiteLevelProj K)^*⟦Λ⟧.obj M₀)
  have := isIso_galoisComparison Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K χ)
    (isGaloisAction_finiteLevelGaloisAction f K χ) (isFreeAction_finiteLevelGaloisAction f K χ)
    ((f.finiteLevelProj K)^*⟦Λ⟧.obj ((f.finiteLevelProj K)_*⟦Λ⟧.obj
      ((f.finiteLevelProj K)^*⟦Λ⟧.obj M₀)))
  exists_upperStar_obj_iso_twist Λ (f.finiteLevelProj K) (f.finiteLevelGaloisAction χ)
    (finiteLevelGaloisAction_comp_finiteLevelProj f K χ) (finiteLevelGaloisAction_one f K χ)
    (finiteLevelGaloisAction_mul f K χ) M₀ a

end AlgebraicGeometry.ProEtale.CondensedRing

/-! ### Characters of the Frobenius -/

namespace FiniteField

variable {k : Type u} [Field k] [Fintype k] (K : Type u) [Field K] [Algebra k K]
  [FiniteDimensional k K]

/-- The Galois group of a finite extension of a finite field is generated by the geometric
Frobenius. -/
lemma mem_zpowers_geometricFrobeniusAlgEquivOfAlgebraic (σ : Gal(K/k)) :
    σ ∈ Subgroup.zpowers (geometricFrobeniusAlgEquivOfAlgebraic k K) := by
  obtain ⟨m, hm⟩ := exists_geometricFrobeniusAlgEquivOfAlgebraic_pow_succ_eq K σ
  rw [← hm]
  exact Subgroup.npow_mem_zpowers _ _

/-- The geometric Frobenius of a finite extension `K / k` of a finite field has order `[K : k]`. -/
lemma orderOf_geometricFrobeniusAlgEquivOfAlgebraic [IsGalois k K] :
    orderOf (geometricFrobeniusAlgEquivOfAlgebraic k K) = Module.finrank k K := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (mem_zpowers_geometricFrobeniusAlgEquivOfAlgebraic K),
    IsGalois.card_aut_eq_finrank]

variable [IsGalois k K] {C : Type*} [Category C] {M : C}

/-- The character of `Gal(K / k)` with values in `(Aut M)ᵐᵒᵖ` sending the geometric Frobenius to
an automorphism `A` with `A ^ [K : k] = 1`. -/
noncomputable def geometricFrobeniusCharacter (A : Aut M) (hA : A ^ Module.finrank k K = 1) :
    Gal(K/k) →* (Aut M)ᵐᵒᵖ :=
  monoidHomOfForallMemZpowers (mem_zpowers_geometricFrobeniusAlgEquivOfAlgebraic K)
    (g' := MulOpposite.op A) (orderOf_dvd_of_pow_eq_one (by
      rw [orderOf_geometricFrobeniusAlgEquivOfAlgebraic, ← MulOpposite.op_pow, hA,
        MulOpposite.op_one]))

/-- The character `geometricFrobeniusCharacter` sends the geometric Frobenius to `A`. -/
lemma geometricFrobeniusCharacter_geometricFrobeniusAlgEquivOfAlgebraic (A : Aut M)
    (hA : A ^ Module.finrank k K = 1) :
    geometricFrobeniusCharacter K A hA (geometricFrobeniusAlgEquivOfAlgebraic k K) =
      MulOpposite.op A :=
  monoidHomOfForallMemZpowers_apply_gen _ _

end FiniteField

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] [Fintype k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))
  (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Realising a character of finite order of the Frobenius as a sheaf.** Let `K / k` be a
finite extension of degree `n` of the finite field `k`, `M₀` a module object on `X₀` (e.g. the
constant module `Λ_{X₀}^r`) and `A` an automorphism of `M₀` with `Aⁿ = 1` (e.g. a unit `c` of
the coefficients with `cⁿ = 1`, or an element of `GL_r` of finite order dividing `n`). There is
a module object `M` on `X₀` with `q_K^* M ≅ q_K^* M₀` on `X₀ ⊗_k K`, through which the canonical
descent datum of `q_K^* M` along `𝟙 × Spec σ` corresponds to the canonical one of `q_K^* M₀`
twisted by `a σ`, where `a = FiniteField.geometricFrobeniusCharacter K A hA` sends the geometric
Frobenius `γ` to `A`
(`FiniteField.geometricFrobeniusCharacter_geometricFrobeniusAlgEquivOfAlgebraic`): the
finite-level Frobenius `Fr_K = 𝟙 × Spec γ` acts on `q_K^* M ≅ q_K^* M₀` through `A`. -/
theorem exists_upperStar_finiteLevelProj_obj_iso_frobeniusTwist
    (M₀ : Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀))
    (A : Aut M₀) (hA : A ^ Module.finrank k K = 1) :
    ∃ (M : Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀))
      (e : (f.finiteLevelProj K)^*⟦Λ⟧.obj M ≅ (f.finiteLevelProj K)^*⟦Λ⟧.obj M₀), ∀ σ,
      e.hom ≫ (f.finiteLevelProj K)^*⟦Λ⟧.map
          (FiniteField.geometricFrobeniusCharacter K A hA σ).unop.asIso.hom ≫
          ((upperStarCongr Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K
              (MulEquiv.refl Gal(K/k)) σ)).inv.app M₀ ≫
            (upperStarComp Λ (f.finiteLevelGaloisAction (MulEquiv.refl Gal(K/k)) σ)
              (f.finiteLevelProj K)).hom.app M₀) =
        ((upperStarCongr Λ (finiteLevelGaloisAction_comp_finiteLevelProj f K
            (MulEquiv.refl Gal(K/k)) σ)).inv.app M ≫
          (upperStarComp Λ (f.finiteLevelGaloisAction (MulEquiv.refl Gal(K/k)) σ)
            (f.finiteLevelProj K)).hom.app M) ≫
          (f.finiteLevelGaloisAction (MulEquiv.refl Gal(K/k)) σ)^*⟦Λ⟧.map e.hom :=
  exists_upperStar_finiteLevelProj_obj_iso_twist f K Λ (MulEquiv.refl Gal(K/k)) M₀
    (FiniteField.geometricFrobeniusCharacter K A hA)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k)) {K : Type u} [Field K]
  [Algebra k K] (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] (θ : K →ₐ[k] AlgebraicClosure k)

/-- An isomorphism `q_K^* M ≅ q_K^* M₀` at a finite level induces an isomorphism
`p^* M ≅ p^* M₀` on the geometric fibre, by pulling back along
`ι = 𝟙 × Spec θ : X̄ ⟶ X₀ ⊗_k K` (`ι ≫ q_K = p`). In particular the twisted module objects of
`AlgebraicGeometry.ProEtale.CondensedRing.exists_upperStar_finiteLevelProj_obj_iso_twist` are
geometrically isomorphic to `M₀`. -/
noncomputable def upperStarGeometricFiberProjIsoOfFiniteLevel
    {M M₀ : Mod (Sheaf (Scheme.ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)}
    (e : (f.finiteLevelProj K)^*⟦Λ⟧.obj M ≅ (f.finiteLevelProj K)^*⟦Λ⟧.obj M₀) :
    (f.geometricFiberProj)^*⟦Λ⟧.obj M ≅ (f.geometricFiberProj)^*⟦Λ⟧.obj M₀ :=
  (upperStarCongr Λ (f.geometricFiberToFiniteLevel_comp_finiteLevelProj θ)).symm.app M ≪≫
    (upperStarComp Λ (f.geometricFiberToFiniteLevel θ) (f.finiteLevelProj K)).app M ≪≫
    (f.geometricFiberToFiniteLevel θ)^*⟦Λ⟧.mapIso e ≪≫
    (upperStarComp Λ (f.geometricFiberToFiniteLevel θ) (f.finiteLevelProj K)).symm.app M₀ ≪≫
    (upperStarCongr Λ (f.geometricFiberToFiniteLevel_comp_finiteLevelProj θ)).app M₀

end AlgebraicGeometry.ProEtale.CondensedRing
